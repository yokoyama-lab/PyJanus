"""A tiny, dependency-free web playground for PyJanus.

Run:  python3 -m jana_py.web            # serves http://127.0.0.1:8000
      python3 -m jana_py.web --port 9000 --host 0.0.0.0

Uses only the standard library (http.server), like the rest of PyJanus.  The page
lets you edit a Janus program, pick the dialect/direction/mode, supply read/scanf
input values, and run it; the backend shells out to `python -m jana_py.cli` with a
timeout and returns stdout/stderr.

The front-end (`webui/playground.html`) and the examples (`webui/examples.json`)
are shared with the Apache/PHP deployment in `webui/index.php`, so both serve the
same UI.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

PKG_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WEBUI_DIR = os.path.join(PKG_ROOT, "webui")
RUN_TIMEOUT = 10  # seconds, hard cap on each run

# mode id -> extra CLI flags (besides --std / --direction)
MODES = {
    "run": [],
    "store": ["-s"],
    "invert": ["-i"],
    "ast": ["-a"],
    "cpp": ["-c"],
    "debug": ["-d"],
    "circuit": ["--circuit"],
    "profile": ["--profile"],
}


def run_pyjanus(source: str, std: str, direction: str, mode: str,
                args: str, mod_bits: str, mod_prime: str) -> dict:
    flags = list(MODES.get(mode, []))
    if direction in ("forward", "backward"):
        flags += ["--direction", direction]
    if mod_bits.strip():
        flags += ["-m", mod_bits.strip()]
    if mod_prime.strip():
        flags += ["-p", mod_prime.strip()]
    if mode in ("ast", "invert", "cpp"):  # may be a library with no main
        flags += ["--no-main"]

    tmp = tempfile.NamedTemporaryFile("w", suffix=".ja", delete=False, encoding="utf-8")
    try:
        tmp.write(source)
        tmp.close()
        cmd = [sys.executable, "-m", "jana_py.cli", "--std", std, *flags, tmp.name]
        cmd += args.split()  # each value -> one scanf/read line on stdin
        try:
            cp = subprocess.run(cmd, capture_output=True, text=True,
                                cwd=PKG_ROOT, timeout=RUN_TIMEOUT)
            shown = " ".join(["pyjanus", "--std", std, *flags])
            if args.split():
                shown += " …args…"
            return {"stdout": cp.stdout, "stderr": cp.stderr, "code": cp.returncode,
                    "cmd": shown}
        except subprocess.TimeoutExpired:
            return {"stdout": "", "stderr": f"timed out after {RUN_TIMEOUT}s", "code": 124,
                    "cmd": ""}
    finally:
        os.unlink(tmp.name)


def build_page() -> bytes:
    """The shared front-end with the examples/stds injected."""
    with open(os.path.join(WEBUI_DIR, "playground.html"), encoding="utf-8") as f:
        html = f.read()
    with open(os.path.join(WEBUI_DIR, "examples.json"), encoding="utf-8") as f:
        data = json.load(f)
    html = html.replace("%%EXAMPLES%%", json.dumps(data["examples"]))
    html = html.replace("%%STDS%%", json.dumps(data["stds"]))
    return html.encode()


class Handler(BaseHTTPRequestHandler):
    def _send(self, code, ctype, body: bytes):
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        try:
            self._send(200, "text/html; charset=utf-8", build_page())
        except FileNotFoundError as exc:
            self._send(500, "text/plain", f"missing webui asset: {exc}".encode())

    def do_POST(self):
        try:
            n = int(self.headers.get("Content-Length", 0))
            req = json.loads(self.rfile.read(n) or b"{}")
            result = run_pyjanus(
                req.get("source", ""), req.get("std", "janus2026"),
                req.get("direction", "forward"), req.get("mode", "run"),
                req.get("args", ""), req.get("modBits", ""), req.get("modPrime", ""))
        except Exception as exc:  # never crash the server on a bad request
            result = {"stdout": "", "stderr": f"server error: {exc}", "code": 1, "cmd": ""}
        self._send(200, "application/json", json.dumps(result).encode())

    def log_message(self, *a):  # quiet
        pass


def main(argv=None):
    ap = argparse.ArgumentParser(description="PyJanus web playground")
    ap.add_argument("--host", default="127.0.0.1")
    ap.add_argument("--port", type=int, default=8000)
    args = ap.parse_args(argv)
    srv = ThreadingHTTPServer((args.host, args.port), Handler)
    url = f"http://{args.host}:{args.port}"
    print(f"PyJanus playground on {url}  (Ctrl+C to stop)")
    try:
        srv.serve_forever()
    except KeyboardInterrupt:
        print("\nbye")


if __name__ == "__main__":
    main()
