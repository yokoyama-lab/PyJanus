"""Exercise both public HTTP entry points, including the real PHP gateway."""
from __future__ import annotations

import http.client
import json
import os
from pathlib import Path
import shutil
import socket
import subprocess
import sys
import threading
import time

import pytest

from jana_py import web

ROOT = Path(__file__).resolve().parents[1]
EMPTY = "void main() {}"


@pytest.fixture(params=["python", "php"])
def endpoint(request, tmp_path, monkeypatch):
  saves = tmp_path / "saves"
  saves.mkdir()
  monkeypatch.setenv("PYJANUS_SAVES", str(saves))
  monkeypatch.setattr(web, "SAVES_DIR", str(saves))
  if request.param == "python":
    server = web.PlaygroundServer(("127.0.0.1", 0), web.Handler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()
    try:
      yield server.server_address[1], saves, server
    finally:
      server.shutdown()
      server.server_close()
      thread.join(timeout=5)
  else:
    php = shutil.which("php")
    if not php or not shutil.which("timeout"):
      pytest.skip("PHP and coreutils timeout are required")
    with socket.socket() as sock:
      sock.bind(("127.0.0.1", 0))
      port = sock.getsockname()[1]
    env = {**os.environ, "PYJANUS_ROOT": str(ROOT), "PYJANUS_PYTHON": sys.executable}
    proc = subprocess.Popen([php, "-S", f"127.0.0.1:{port}", "-t", str(ROOT / "webui")],
                            env=env, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    try:
      deadline = time.monotonic() + 10
      while True:
        try:
          with socket.create_connection(("127.0.0.1", port), timeout=0.2):
            break
        except OSError:
          if proc.poll() is not None or time.monotonic() >= deadline:
            pytest.fail("PHP server failed to start")
          time.sleep(0.05)
      yield port, saves, None
    finally:
      proc.terminate()
      try:
        proc.wait(timeout=5)
      except subprocess.TimeoutExpired:
        proc.kill()
        proc.wait()


def send(endpoint, payload=None, *, path="/", method="POST", headers=None):
  conn = http.client.HTTPConnection("127.0.0.1", endpoint[0], timeout=20)
  try:
    body = json.dumps(payload) if payload is not None else None
    conn.request(method, path, body, headers or {"Content-Type": "application/json"})
    response = conn.getresponse()
    return response.status, response.read().decode()
  finally:
    conn.close()


def test_run_and_stdin_over_http(endpoint):
  source = "procedure main()\n    int x\n    read x\n    write x\n"
  status, body = send(endpoint, {"source": source, "std": "jana2014_in_out", "args": "-7"})
  result = json.loads(body)
  assert status == 200
  assert result["code"] == 0, result
  assert result["stdout"].strip() == "-7"


def test_file_disclosure_paths_over_http(endpoint, tmp_path):
  secret = tmp_path / "secret.txt"
  secret.write_text("HTTP_PRIVATE_MARKER")
  for payload in ({"source": EMPTY, "args": f"--expect-file {secret}"},
                  {"source": f'#include "{secret}"\n{EMPTY}'}):
    status, body = send(endpoint, payload)
    assert status == 200
    assert "HTTP_PRIVATE_MARKER" not in body


def test_saved_xss_over_http_including_legacy_save(endpoint):
  state = {"source": '</script><script>window.injected=1</script>', "std": "janus2026"}
  status, body = send(endpoint, {"action": "save", "state": state})
  assert status == 200
  saved = json.loads(body)["id"]
  (endpoint[1] / "abcdef1234.json").write_text(json.dumps(state))
  for pid in (saved, "abcdef1234"):
    status, html = send(endpoint, method="GET", path="/?p=" + pid)
    assert status == 200
    assert html.count("<script>") == 1
    encoded = html.split("const SAVED = ", 1)[1].split(";\nfunction getState", 1)[0]
    assert json.loads(encoded)["source"] == state["source"]


def test_reject_oversized_body(endpoint):
  status, _ = send(endpoint, {"source": "x" * web.MAX_REQUEST})
  assert status == 413


def test_python_checks_length_before_reading(endpoint):
  if endpoint[2] is None:
    pytest.skip("PHP's web server buffers the body before invoking the script")
  status, _ = send(endpoint, headers={"Content-Type": "application/json",
                                    "Content-Length": str(web.MAX_REQUEST + 1)})
  assert status == 413


def test_reject_browser_simple_post(endpoint):
  status, _ = send(endpoint, {"source": EMPTY}, headers={"Content-Type": "text/plain"})
  assert status == 415


def test_reject_invalid_fields(endpoint):
  status, body = send(endpoint, {"source": EMPTY, "args": ["--expect-file", "secret"]})
  assert status == 200
  assert "error" in json.loads(body)


def test_python_connection_admission(endpoint):
  server = endpoint[2]
  if server is None:
    pytest.skip("PHP connection admission belongs to Apache")
  for _ in range(web.MAX_CONNECTIONS):
    assert server.connections.acquire(blocking=False)
  try:
    status, _ = send(endpoint, method="GET")
    assert status == 503
  finally:
    for _ in range(web.MAX_CONNECTIONS):
      server.connections.release()
