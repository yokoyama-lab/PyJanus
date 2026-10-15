"""Regression tests for the playground's untrusted-input boundary."""
from __future__ import annotations

from html.parser import HTMLParser
import json
import os
from pathlib import Path
import subprocess
import sys

import pytest

from jana_py import web
from jana_py.errors import JanaError
from jana_py.preprocess import STDLIB_DIR, preprocess_text

ROOT = Path(__file__).resolve().parents[1]
EMPTY = "void main() {}"
ECHO = "procedure main()\n    int x\n    read x\n    write x\n"


@pytest.fixture(autouse=True)
def isolated_saves(tmp_path, monkeypatch):
  monkeypatch.setattr(web, "SAVES_DIR", str(tmp_path / "saves"))
  monkeypatch.setenv("PYJANUS_SAVES", web.SAVES_DIR)


def run(source=EMPTY, args="", std="janus2026", mode="run", **kwargs):
  return web.run_pyjanus(source, std, "forward", mode, args,
                         kwargs.get("mod_bits", ""), kwargs.get("mod_prime", ""))


@pytest.mark.parametrize("args", ["--expect-file {path}", "--std jana2014", "-I {path}"])
def test_input_cannot_become_cli_options(tmp_path, args):
  marker = tmp_path / "secret.txt"
  marker.write_text("PRIVATE_REVIEW_MARKER")
  result = run(args=args.format(path=marker))
  assert result["code"] == 0, result
  assert result["stdout"] == ""
  assert "PRIVATE_REVIEW_MARKER" not in json.dumps(result)


@pytest.mark.parametrize("value", ["5", "0", "-7"])
def test_stdin_preserves_signed_numbers(value):
  result = run(ECHO, args=value, std="jana2014_in_out")
  assert result["code"] == 0, result
  assert result["stdout"].strip() == value


def test_cli_looking_input_is_read_as_data(tmp_path):
  marker = tmp_path / "secret.txt"
  marker.write_text("PRIVATE_REVIEW_MARKER")
  result = run(ECHO, args=f"--expect-file {marker}", std="jana2014_in_out")
  assert result["code"] != 0
  assert "PRIVATE_REVIEW_MARKER" not in json.dumps(result)
  assert "read expected an integer" in result["stdout"]


@pytest.mark.parametrize("relative", [False, True])
def test_web_include_cannot_read_external_file(tmp_path, relative):
  marker = tmp_path / "secret.txt"
  marker.write_text("PRIVATE_REVIEW_MARKER")
  target = os.path.relpath(marker, STDLIB_DIR) if relative else str(marker)
  result = run(f'#include "{target}"\n{EMPTY}')
  assert result["code"] != 0
  assert "PRIVATE_REVIEW_MARKER" not in json.dumps(result)


def test_nested_include_and_symlink_cannot_escape_allowed_root(tmp_path):
  allowed = tmp_path / "lib"
  allowed.mkdir()
  secret = tmp_path / "secret.ja"
  secret.write_text("PRIVATE_REVIEW_MARKER")
  (allowed / "link.ja").symlink_to(secret)
  for target in ("../secret.ja", "link.ja"):
    (allowed / "outer.ja").write_text(f'#include "{target}"\n')
    with pytest.raises(JanaError, match="not found"):
      preprocess_text(str(tmp_path / "program.ja"), '#include "outer.ja"\n',
                      include_dirs=[allowed], include_roots=[allowed])


@pytest.mark.parametrize("std,main", [("janus2026", EMPTY), ("jana2014", "procedure main()\n    skip")])
def test_web_keeps_bundled_libraries(std, main):
  result = run('#include "std/array.ja"\n' + main, std=std)
  assert result["code"] == 0, result


def test_normal_cli_keeps_local_includes(tmp_path):
  (tmp_path / "lib.ja").write_text("void inc(int x) { x += 1; }")
  program = tmp_path / "program.ja"
  program.write_text('#include "lib.ja"\nvoid main() { int x; call inc(x); }')
  cp = subprocess.run([sys.executable, "-m", "jana_py.cli", "-s", str(program)],
                      cwd=ROOT, capture_output=True, text=True, timeout=10)
  assert cp.returncode == 0, cp.stderr
  assert "x = 1" in cp.stdout


class Scripts(HTMLParser):
  def __init__(self):
    super().__init__()
    self.blocks = []
    self.active = False

  def handle_starttag(self, tag, attrs):
    if tag == "script":
      self.active = True
      self.blocks.append("")

  def handle_endtag(self, tag):
    if tag == "script":
      self.active = False

  def handle_data(self, data):
    if self.active:
      self.blocks[-1] += data


def test_existing_saved_xss_is_safe_and_source_roundtrips():
  source = '</script><script>window.injected=1</script>%%EXAMPLES%%\u2028'
  state = {"source": source, "std": "janus2026"}
  # Simulate a pre-fix saved file whose JSON contains literal HTML delimiters.
  os.makedirs(web.SAVES_DIR)
  (Path(web.SAVES_DIR) / "abcdef1234.json").write_text(json.dumps(state))
  page = web.build_page(web.load_saved("p=abcdef1234")).decode()
  parser = Scripts()
  parser.feed(page)
  assert len(parser.blocks) == 1
  encoded = page.split("const SAVED = ", 1)[1].split(";\nfunction getState", 1)[0]
  assert json.loads(encoded) == state
  assert "<script>window.injected" not in page


def test_save_roundtrip_and_quota(monkeypatch):
  monkeypatch.setattr(web, "MAX_SAVES", 1)
  state = {"source": EMPTY, "std": "janus2026"}
  first = web.save_state(state)
  assert "id" in first
  assert web.save_state(state) == first  # deduplication works at capacity
  assert json.loads(web.load_saved("p=" + first["id"]))["source"] == EMPTY
  assert "error" in web.save_state({**state, "source": EMPTY + "\n"})


def test_save_total_bytes_quota(monkeypatch):
  first = web.save_state({"source": EMPTY})
  assert "id" in first
  monkeypatch.setattr(web, "MAX_SAVE_STORAGE", 1)
  assert "error" in web.save_state({"source": EMPTY + "\n"})


@pytest.mark.parametrize("payload", [[], {"source": []}, {"std": []},
    {"source": "x" * (web.MAX_SOURCE + 1)}, {"args": "1" * (web.MAX_INPUT + 1)},
    {"modBits": "999999999"}, {"modBits": "-1"}, {"modPrime": "999999999999999"}])
def test_bad_run_input_rejected_before_start(payload, monkeypatch):
  def unexpected(*args, **kwargs):
    pytest.fail("invalid request spawned a child")
  monkeypatch.setattr(subprocess, "run", unexpected)
  assert "error" in web.dispatch(payload)


def test_all_saved_fields_are_bounded():
  for key in ("source", "args", "mode", "mbits"):
    assert "error" in web.save_state({key: "x" * (web.MAX_SAVED + 1)})


def test_run_slots_limit_separate_gateway_processes(monkeypatch):
  monkeypatch.setattr(web, "MAX_RUNS", 1)
  with web.run_slot():
    # Gateway processes use the same on-disk locks, independently of threads.
    with web.file_lock(".run-1.lock"), web.file_lock(".run-2.lock"), web.file_lock(".run-3.lock"):
      cp = subprocess.run([sys.executable, "-m", "jana_py.web", "--gateway", "POST"],
                          input=json.dumps({"source": EMPTY}), cwd=ROOT,
                          text=True, capture_output=True, timeout=10)
      assert "error" in json.loads(cp.stdout)
  assert run()["code"] == 0  # lock released


def test_wall_clock_timeout_releases_slot(monkeypatch):
  monkeypatch.setattr(web, "RUN_TIMEOUT", 0.001)
  assert run()["code"] == 124
  monkeypatch.setattr(web, "RUN_TIMEOUT", 10)
  assert run()["code"] == 0


def test_output_limit():
  result = run("void main() { int a[600000]; }", mode="store")
  assert result["code"] != 0, result
  assert "output limit" in result["stderr"]


def test_large_allocation_is_stopped_in_child():
  result = run("void main() { int x; x += 1 << 3000000000; }")
  assert result["code"] != 0
  assert result["code"] != 124  # memory cap, not just the wall-clock timer
  assert "insufficient memory" in result["stdout"]
  assert run()["code"] == 0


def test_unavailable_resource_limits_fail_closed(monkeypatch, capsys):
  import resource
  from jana_py import cli

  def unavailable(*args):
    raise OSError("not supported")

  def unexpected(*args, **kwargs):
    pytest.fail("interpreter started without resource limits")

  monkeypatch.setattr(resource, "setrlimit", unavailable)
  monkeypatch.setattr(cli, "main", unexpected)
  assert web.worker([]) == 1
  assert "web execution disabled" in capsys.readouterr().err
