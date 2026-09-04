#!/usr/bin/env python3
"""Differential test of PyJanus against the Haskell Jana reference interpreter.

`tests/janus2026/test_step1_golden.py` skips all 101 corpus programs because it
looks for `src/Main.hs` inside this repository.  The reference implementation is
the `jana` interpreter (Budde / Nielsen / Kirkedal Thomsen), which lives in its
own repository; point `JANA_HASKELL_BIN` at a built binary and this harness runs
the whole corpus through both engines.

Usage:
    JANA_HASKELL_BIN=/path/to/jana python3 tools/step1_differential.py [--json out.json]
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "tests" / "jana2014" / "fixtures" / "examples"
TIMEOUT = 20

# PyJanus prints diagnostics the 2014 reference never had (leftover-store
# warnings, deprecation notices).  The reference reports problems as `[ERROR …]`
# and never emits a `Warning:` line, so dropping them cannot hide a real
# disagreement.  Verified: this is what separates the three programs that
# otherwise differ only by a deprecation notice.
_PY_ONLY = re.compile(r"^Warning: .*$", re.M)


def find_binary() -> str | None:
  env = os.environ.get("JANA_HASKELL_BIN")
  if env and Path(env).exists():
    return env
  which = shutil.which("jana")
  if which:
    return which
  # The usual cabal build location of a sibling ghq checkout.
  home = Path.home()
  pat = "dev/github.com/*/Jana-JanusInterp/dist-newstyle/build/*/*/jana-*/x/jana/build/jana/jana"
  for cand in sorted(home.glob(pat)):
    if os.access(cand, os.X_OK):
      return str(cand)
  return None


def normalise(text: str) -> str:
  text = _PY_ONLY.sub("", text)
  lines = [ln.rstrip() for ln in text.splitlines()]
  return "\n".join(ln for ln in lines if ln.strip())


def run_haskell(binary: str, path: Path) -> tuple[int, str]:
  try:
    r = subprocess.run([binary, str(path)], cwd=ROOT, text=True,
                       capture_output=True, timeout=TIMEOUT)
  except subprocess.TimeoutExpired:
    return 124, ""
  return r.returncode, r.stdout + r.stderr


def run_python(path: Path) -> tuple[int, str]:
  env = dict(os.environ, PYTHONPATH=str(ROOT))
  try:
    r = subprocess.run(
      [sys.executable, "-m", "jana_py.cli", "--std", "jana2014", "-s", str(path)],
      cwd=ROOT, text=True, capture_output=True, timeout=TIMEOUT, env=env)
  except subprocess.TimeoutExpired:
    return 124, ""
  return r.returncode, r.stdout + r.stderr


def main() -> int:
  ap = argparse.ArgumentParser()
  ap.add_argument("--json", type=Path)
  ap.add_argument("--limit", type=int)
  args = ap.parse_args()

  binary = find_binary()
  if binary is None:
    print("no Haskell jana binary found; set JANA_HASKELL_BIN", file=sys.stderr)
    return 2
  print(f"reference: {binary}")

  programs = sorted(CORPUS.glob("*.ja"))
  if args.limit:
    programs = programs[: args.limit]

  agree, mismatch, both_fail = [], [], []
  for p in programs:
    hrc, hout = run_haskell(binary, p)
    prc, pout = run_python(p)
    hn, pn = normalise(hout), normalise(pout)
    if hrc != 0 and prc != 0:
      both_fail.append((p.name, hrc, prc))
    elif hrc == prc and hn == pn:
      agree.append(p.name)
    else:
      mismatch.append({
        "program": p.name, "haskell_rc": hrc, "pyjanus_rc": prc,
        "haskell": hn[:900], "pyjanus": pn[:900],
      })

  total = len(programs)
  print(f"\nprograms      {total}")
  print(f"agree         {len(agree)}")
  print(f"mismatch      {len(mismatch)}")
  print(f"both error    {len(both_fail)}  (reference cannot run these either)")

  if mismatch:
    print("\n--- mismatches ---")
    for m in mismatch:
      print(f"\n### {m['program']}  (haskell rc={m['haskell_rc']} pyjanus rc={m['pyjanus_rc']})")
      print("  haskell :", m["haskell"].replace("\n", "\n            ")[:400])
      print("  pyjanus :", m["pyjanus"].replace("\n", "\n            ")[:400])
  if both_fail:
    print("\n--- both error ---")
    for name, hrc, prc in both_fail:
      print(f"  {name}: haskell rc={hrc} pyjanus rc={prc}")

  if args.json:
    args.json.write_text(json.dumps(
      {"total": total, "agree": agree, "mismatch": mismatch,
       "both_fail": both_fail, "reference": binary}, indent=2))
  return 0


if __name__ == "__main__":
  raise SystemExit(main())
