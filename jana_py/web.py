"""Dependency-free playground, with a shared gateway for the PHP frontend.

Run ``python3 -m jana_py.web`` to serve http://127.0.0.1:8000.
Untrusted programs run in separate, resource-limited Unix processes.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import threading
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse

PKG_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WEBUI_DIR = os.path.join(PKG_ROOT, "webui")
SAVES_DIR = os.environ.get("PYJANUS_SAVES") or os.path.join(PKG_ROOT, "playground-saves")
RUN_TIMEOUT = 10
MAX_REQUEST = 256 * 1024
MAX_SOURCE = 64 * 1024
MAX_INPUT = 16 * 1024
MAX_SAVED = 128 * 1024
MAX_OUTPUT = 1024 * 1024  # per stdout/stderr file
MAX_MEMORY = 256 * 1024 * 1024
MAX_RUNS = 4
MAX_CONNECTIONS = 8
MAX_SAVES = 1000
MAX_SAVE_STORAGE = 64 * 1024 * 1024
STDS = ["janus2026", "jana2014", "jana2014basic", "jana2014_in_out", "janus1982", "janus1982ext"]
MODES = {
  "run": [], "store": ["-s"], "invert": ["-i"], "ast": ["-a"],
  "cpp": ["-c"], "debug": ["-d"], "circuit": ["--circuit"], "profile": ["--profile"],
}


def failure(message: str, code: int = 1) -> dict:
  return {"stdout": "", "stderr": message, "error": message, "code": code, "cmd": ""}


def checked_text(value, limit: int) -> str:
  if not isinstance(value, str):
    raise ValueError("fields must be strings")
  if len(value.encode("utf-8")) > limit:
    raise ValueError("input too large")
  return value


@contextmanager
def file_lock(name: str):
  # OS locks coordinate Python HTTP threads AND separate PHP gateway processes.
  # Do not delete lock files: replacing their inode would defeat active locks.
  import fcntl
  os.makedirs(SAVES_DIR, mode=0o700, exist_ok=True)
  fd = os.open(os.path.join(SAVES_DIR, name), os.O_CREAT | os.O_RDWR | os.O_NOFOLLOW, 0o600)
  try:
    fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    yield
  finally:
    os.close(fd)


@contextmanager
def run_slot():
  for index in range(MAX_RUNS):
    lock = file_lock(f".run-{index}.lock")
    try:
      lock.__enter__()
    except BlockingIOError:
      continue
    try:
      yield
    finally:
      lock.__exit__(None, None, None)
    return
  raise ValueError("server busy; try again later")


def run_pyjanus(source: str, std: str, direction: str, mode: str,
                args: str, mod_bits: str, mod_prime: str) -> dict:
  try:
    checked_text(source, MAX_SOURCE)
    checked_text(args, MAX_INPUT)
    for value in (std, direction, mode, mod_bits, mod_prime):
      checked_text(value, 64)
    if std not in STDS or mode not in MODES or direction not in ("forward", "backward"):
      raise ValueError("invalid dialect, mode or direction")
    flags = [*MODES[mode], "--direction", direction]
    for option, value, maximum in (("-m", mod_bits, 64), ("-p", mod_prime, 2147483647)):
      value = value.strip()
      if value:
        if not re.fullmatch(r"[0-9]{1,10}", value) or not 1 <= int(value) <= maximum:
          raise ValueError(f"invalid {option}: maximum is {maximum}")
        flags += [option, value]
    if mode in ("ast", "invert", "cpp"):
      flags += ["--no-main"]
    with run_slot(), tempfile.TemporaryDirectory(prefix="pyjanus-web-") as tmp:
      path = Path(tmp) / "program.ja"
      path.write_text(source, encoding="utf-8")
      cmd = [sys.executable, "-m", "jana_py.web", "--worker", "--std", std, *flags, str(path)]
      # Real stdin, never CLI arguments. Regular output files are capped by the
      # child's RLIMIT_FSIZE, so capture cannot exhaust the HTTP server's RAM.
      with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
        try:
          cp = subprocess.run(cmd, input="\n".join(args.split()), text=True,
                              stdout=stdout, stderr=stderr, cwd=PKG_ROOT, timeout=RUN_TIMEOUT)
        except subprocess.TimeoutExpired:
          return failure(f"timed out after {RUN_TIMEOUT}s", 124)
        stdout.seek(0)
        stderr.seek(0)
        out, err = stdout.read(MAX_OUTPUT), stderr.read(MAX_OUTPUT)
        if len(out) >= MAX_OUTPUT or len(err) >= MAX_OUTPUT:
          return failure("output limit exceeded")
        if cp.returncode < 0:
          return failure("execution stopped by a resource limit")
        return {"stdout": out.decode("utf-8", errors="replace"),
                "stderr": err.decode("utf-8", errors="replace"), "code": cp.returncode,
                "cmd": " ".join(["pyjanus", "--std", std, *flags])}
  except ValueError as exc:
    return failure(str(exc))
  except (OSError, ImportError):
    # Do not expose internal filesystem paths or platform exception details.
    return failure("execution unavailable")


def worker(argv: list[str]) -> int:
  # Set limits in the child before importing the interpreter; preexec_fn is
  # unsafe in the threaded HTTP parent. Fail closed on unsupported platforms.
  try:
    import resource
    for kind, cap in ((resource.RLIMIT_AS, MAX_MEMORY),
                      (resource.RLIMIT_CPU, RUN_TIMEOUT),
                      (resource.RLIMIT_FSIZE, MAX_OUTPUT), (resource.RLIMIT_CORE, 0)):
      _, hard = resource.getrlimit(kind)
      cap = cap if hard == resource.RLIM_INFINITY else min(cap, hard)
      resource.setrlimit(kind, (cap, cap))
  except (ImportError, AttributeError, OSError, ValueError):
    print("resource limits unavailable; web execution disabled", file=sys.stderr)
    return 1
  from .cli import main as cli_main
  from .preprocess import STDLIB_DIR
  return cli_main(argv, include_roots=[STDLIB_DIR])


def script_json(value) -> str:
  # JSON string quoting alone does not protect an HTML script element.
  return json.dumps(value, ensure_ascii=True).replace("<", "\\u003c")


def build_page(saved: str = "null") -> bytes:
  with open(os.path.join(WEBUI_DIR, "playground.html"), encoding="utf-8") as f:
    html = f.read()
  with open(os.path.join(WEBUI_DIR, "examples.json"), encoding="utf-8") as f:
    data = json.load(f)
  replacements = {"SAVED": script_json(json.loads(saved)),
                  "EXAMPLES": script_json(data["examples"]), "STDS": script_json(data["stds"])}
  # One pass: placeholder-like text in a submitted program remains literal.
  return re.sub(r"%%(SAVED|EXAMPLES|STDS)%%", lambda m: replacements[m[1]], html).encode()


def load_saved(query: str) -> str:
  pid = (parse_qs(query, max_num_fields=32).get("p") or [""])[0]
  if re.fullmatch(r"[a-f0-9]{6,16}", pid):
    try:
      with open(os.path.join(SAVES_DIR, pid + ".json"), "rb") as f:
        body = f.read(MAX_SAVED + 1)
      if len(body) <= MAX_SAVED:
        state = json.loads(body)
        if isinstance(state, dict):
          return json.dumps(state)
    except (OSError, ValueError, RecursionError):
      pass
  return "null"


def save_state(state: dict) -> dict:
  try:
    if not isinstance(state, dict):
      raise ValueError("bad state")
    clean = {k: checked_text(state.get(k, ""),
                            MAX_SOURCE if k == "source" else MAX_INPUT if k == "args" else 256)
             for k in ("source", "std", "mode", "dir", "args", "mbits", "mprime")}
    if clean["std"] not in STDS:
      clean["std"] = "janus2026"
    body = json.dumps(clean, ensure_ascii=False).encode("utf-8")
    if len(body) > MAX_SAVED:
      raise ValueError("state too large")
    pid = hashlib.sha256(body).hexdigest()[:10]
    with file_lock(".saves.lock"):
      path = Path(SAVES_DIR) / (pid + ".json")
      if path.is_file():
        return {"id": pid}
      count = total = 0
      with os.scandir(SAVES_DIR) as entries:
        for entry in entries:
          if entry.name.endswith(".json"):
            count += 1
            total += entry.stat().st_size
            if count >= MAX_SAVES or total + len(body) > MAX_SAVE_STORAGE:
              return {"error": "save storage full"}
      # Exclusive create prevents following an existing symlink. The lock also
      # bounds simultaneous saves across both backends.
      with path.open("xb") as f:
        f.write(body)
    return {"id": pid}
  except (ValueError, OSError, ImportError):
    return {"error": "invalid state or save storage unavailable"}


def dispatch(req) -> dict:
  if not isinstance(req, dict):
    return failure("request must be a JSON object")
  if req.get("action") == "save":
    return save_state(req.get("state", {}))
  return run_pyjanus(req.get("source", ""), req.get("std", "janus2026"),
                     req.get("direction", "forward"), req.get("mode", "run"),
                     req.get("args", ""), req.get("modBits", ""), req.get("modPrime", ""))


class Handler(BaseHTTPRequestHandler):
  def setup(self):
    self.request.settimeout(5)
    super().setup()

  def _send(self, code, ctype, body: bytes):
    self.send_response(code)
    self.send_header("Content-Type", ctype)
    self.send_header("Content-Length", str(len(body)))
    self.send_header("X-Content-Type-Options", "nosniff")
    self.end_headers()
    self.wfile.write(body)

  def do_GET(self):
    try:
      saved = load_saved(urlparse(self.path).query)
      self._send(200, "text/html; charset=utf-8", build_page(saved))
    except (OSError, ValueError, RecursionError):
      self._send(400, "text/plain", b"page unavailable")

  def do_POST(self):
    if self.headers.get_content_type() != "application/json":
      self._send(415, "application/json", b'{"error":"application/json required"}')
      return
    try:
      lengths = self.headers.get_all("Content-Length", [])
      if self.headers.get("Transfer-Encoding") or len(lengths) != 1:
        raise ValueError("invalid content length")
      n = int(lengths[0])
      if not 0 <= n <= MAX_REQUEST:
        self._send(413, "application/json", b'{"error":"request too large"}')
        return
      body = self.rfile.read(n)
      if len(body) != n:
        raise ValueError("incomplete request")
      result = dispatch(json.loads(body))
    except (ValueError, OSError, RecursionError):
      self._send(400, "application/json", b'{"error":"invalid request"}')
      return
    self._send(200, "application/json", json.dumps(result).encode())

  def log_message(self, *args):
    pass


class PlaygroundServer(ThreadingHTTPServer):
  def __init__(self, *args, **kwargs):
    self.connections = threading.BoundedSemaphore(MAX_CONNECTIONS)
    super().__init__(*args, **kwargs)

  def process_request(self, request, client_address):
    if not self.connections.acquire(blocking=False):
      try:
        request.settimeout(1)
        request.sendall(b"HTTP/1.0 503 Service Unavailable\r\nContent-Length: 0\r\n\r\n")
      finally:
        self.shutdown_request(request)
      return
    try:
      super().process_request(request, client_address)
    except Exception:
      self.connections.release()
      raise

  def process_request_thread(self, request, client_address):
    try:
      super().process_request_thread(request, client_address)
    finally:
      self.connections.release()


def gateway(method: str) -> int:
  """PHP delegates rendering and POSTs here to share the security boundary."""
  raw = sys.stdin.buffer.read(MAX_REQUEST + 1)
  try:
    if len(raw) > MAX_REQUEST:
      raise ValueError("request too large")
    if method == "GET":
      sys.stdout.buffer.write(build_page(load_saved(raw.decode("utf-8"))))
    elif method == "POST":
      print(json.dumps(dispatch(json.loads(raw))))
    else:
      raise ValueError("unsupported method")
    return 0
  except (ValueError, OSError, RecursionError):
    print(json.dumps(failure("invalid request")))
    return 1


def main(argv=None):
  argv = sys.argv[1:] if argv is None else argv
  if argv and argv[0] == "--worker":
    return worker(argv[1:])
  if len(argv) == 2 and argv[0] == "--gateway":
    return gateway(argv[1])
  ap = argparse.ArgumentParser(description="PyJanus web playground")
  ap.add_argument("--host", default="127.0.0.1")
  ap.add_argument("--port", type=int, default=8000)
  args = ap.parse_args(argv)
  with PlaygroundServer((args.host, args.port), Handler) as srv:
    print(f"PyJanus playground on http://{args.host}:{args.port} (Ctrl+C to stop)")
    try:
      srv.serve_forever()
    except KeyboardInterrupt:
      pass
  return 0


if __name__ == "__main__":
  raise SystemExit(main())
