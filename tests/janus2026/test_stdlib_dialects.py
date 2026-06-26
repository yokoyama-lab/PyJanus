"""Per-dialect copies of the standard library (currently: jana2014).

The library is authored in janus2026 and the jana2014 copies are generated
mechanically by `jana_py._gen_stdlib` (parse -> re-emit with the jana2014
formatter).  These tests guard the three things that can go wrong:

  1. drift — the committed jana2014 copies must equal a fresh regeneration;
  2. correctness of the AST -> jana2014-source translation — every procedure must
     compute the same final store under jana2014 (generated lib) as under
     janus2026 (original lib);
  3. include resolution — `#include "std/array.ja"` must pick up the dialect's
     copy under `--std jana2014` (and the janus2026 source otherwise).
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

import pytest

from jana_py._gen_stdlib import DIALECTS, STDLIB_DIR, generate
from jana_py.format import formatter_for_std
from jana_py.parser_janus2026 import parse_program
from jana_py.preprocess import preprocess_text

ROOT = Path(__file__).resolve().parents[2]


# Self-contained janus2026 programs (each #includes a module and calls into it),
# covering every procedure across all six modules.  Reused for the cross-dialect
# equivalence check.
SCENARIOS = {
  "reverse":   '#include "std/array.ja"\nvoid main(){int a[5]={5,4,3,2,1};call reverse(a,5);}\n',
  "rotate":    '#include "std/array.ja"\nvoid main(){int a[4]={1,2,3,4};call rotate_left(a,4);}\n',
  "addxor":    '#include "std/array.ja"\nvoid main(){int d[3]={5,6,7};int s[3]={1,2,3};call add_into(d,s,3);call xor_into(d,s,3);}\n',
  "cswap":     '#include "std/array.ja"\nvoid main(){int x=5;int y=2;int f;call cswap(x,y,f);}\n',
  "bits":      '#include "std/bits.ja"\nvoid main(){int x=1;int y=13;int z=11;call bit_reverse(x,8);call swap_bits(y,0,1);call rotate_bits_left(z,4);}\n',
  "flip":      '#include "std/bits.ja"\nvoid main(){int x=5;call flip_bit(x,1);}\n',
  "mulacc_dm": '#include "std/math.ja"\nvoid main(){int a=6;int b=7;int acc;int n=23;int d=5;int q;int r;call mul_acc(a,b,acc);call divmod(n,d,q,r);}\n',
  "gcd":       '#include "std/math.ja"\nvoid main(){int a=12;int b=8;stack h;call gcd(a,b,h);}\n',
  "reduce":    '#include "std/reduce.ja"\nvoid main(){int a[4]={2,4,6,8};int b[4]={1,0,2,1};int s;int dp;int c;call sum_into(a,4,s);call dot_into(a,b,4,dp);call count_into(a,4,4,c);}\n',
  "minmax":    '#include "std/reduce.ja"\nvoid main(){int a[5]={3,1,4,1,5};int m;int fl[4];stack h;int M;int fl2[4];stack h2;call min_into(a,5,m,fl,h);call max_into(a,5,M,fl2,h2);}\n',
  "sort":      '#include "std/sort.ja"\nvoid main(){int a[5]={3,1,4,1,5};int fl[10];call sort(a,5,fl);}\n',
  "stack":     '#include "std/stack.ja"\nvoid main(){stack s;stack t;int a=1;int b=2;int c=3;int x;push(a,s);push(b,s);push(c,s);call copy_top(s,x);call move_all(s,t);}\n',
  # Roundtrip (call;uncall) scenarios — these exercise reversibility (uncall)
  # under jana2014 too, matching the uncall coverage of the janus2026 suites.
  "rt_reverse":  '#include "std/array.ja"\nvoid main(){int a[5]={5,4,3,2,1};call reverse(a,5);uncall reverse(a,5);}\n',
  "rt_rotate":   '#include "std/array.ja"\nvoid main(){int a[4]={1,2,3,4};call rotate_left(a,4);uncall rotate_left(a,4);}\n',
  "rt_cswap":    '#include "std/array.ja"\nvoid main(){int x=5;int y=2;int f;call cswap(x,y,f);uncall cswap(x,y,f);}\n',
  "rt_bitrev":   '#include "std/bits.ja"\nvoid main(){int x=13;call bit_reverse(x,4);uncall bit_reverse(x,4);}\n',
  "rt_divmod":   '#include "std/math.ja"\nvoid main(){int n=23;int d=5;int q;int r;call divmod(n,d,q,r);uncall divmod(n,d,q,r);}\n',
  "rt_gcd":      '#include "std/math.ja"\nvoid main(){int a=12;int b=8;stack h;call gcd(a,b,h);uncall gcd(a,b,h);}\n',
  "rt_min":      '#include "std/reduce.ja"\nvoid main(){int a[5]={3,1,4,1,5};int m;int fl[4];stack h;call min_into(a,5,m,fl,h);uncall min_into(a,5,m,fl,h);}\n',
  "rt_sort":     '#include "std/sort.ja"\nvoid main(){int a[5]={3,1,4,1,5};int fl[10];call sort(a,5,fl);uncall sort(a,5,fl);}\n',
  "rt_moveall":  '#include "std/stack.ja"\nvoid main(){stack s;stack t;int a=1;int b=2;int c=3;push(a,s);push(b,s);push(c,s);call move_all(s,t);uncall move_all(s,t);}\n',
}


def _run(std: str, src: str, tmp_path: Path) -> list[str]:
  prog = tmp_path / "p.ja"
  prog.write_text(src)
  proc = subprocess.run(
    [sys.executable, "-m", "jana_py.cli", "--std", std, "-s", str(prog)],
    cwd=ROOT, text=True, capture_output=True,
  )
  assert proc.returncode == 0, proc.stderr
  return sorted(l for l in proc.stdout.splitlines() if " = " in l)


# --- 1. no drift ------------------------------------------------------------

@pytest.mark.parametrize("dialect", DIALECTS)
def test_committed_copies_are_up_to_date(dialect):
  for name, text in generate(dialect).items():
    on_disk = (STDLIB_DIR / dialect / "std" / name).read_text()
    assert on_disk == text, (
      f"{dialect}/std/{name} is stale; run `python -m jana_py._gen_stdlib`")


# --- 2. AST -> jana2014 source computes the same thing ----------------------

@pytest.mark.parametrize("name", list(SCENARIOS))
def test_jana2014_matches_janus2026(name, tmp_path):
  src = SCENARIOS[name]
  store_2026 = _run("janus2026", src, tmp_path)
  # Re-emit the whole program (lib inlined + main) as jana2014 and run that.
  pp = preprocess_text("s.ja", src)
  program = parse_program("s.ja", pp.text, pp.line_origins)
  jana2014_src = formatter_for_std("jana2014").format_program(program)
  store_2014 = _run("jana2014", jana2014_src, tmp_path)
  assert store_2014 == store_2026


# --- 3. dialect-aware include resolution ------------------------------------

def test_include_resolves_to_jana2014_copy(tmp_path):
  # No -I: under --std jana2014 the include must find the generated copy.
  out = _run("jana2014",
             '#include "std/array.ja"\n\nprocedure main()\n'
             '    int a[3]\n    a[0] += 1\n    a[1] += 2\n    a[2] += 3\n'
             '    call reverse(a, 3)\n', tmp_path)
  assert any("a[3] = {3, 2, 1}" in line for line in out)


def test_jana2014_reversibility_is_direct(tmp_path):
  # Beyond the equivalence check: run a call;uncall directly under jana2014 and
  # assert the store is fully restored (array back, flag cleared, stack empty).
  out = _run("jana2014",
             '#include "std/sort.ja"\n\nprocedure main()\n'
             '    int a[5]\n    int fl[10]\n'
             '    a[0] += 3\n    a[1] += 1\n    a[2] += 4\n    a[3] += 1\n    a[4] += 5\n'
             '    call sort(a, 5, fl)\n    uncall sort(a, 5, fl)\n', tmp_path)
  assert any("a[5] = {3, 1, 4, 1, 5}" in line for line in out)
  assert any("fl[10] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0}" in line for line in out)


def test_janus2026_still_uses_canonical_source(tmp_path):
  out = _run("janus2026",
             '#include "std/array.ja"\nvoid main() {\n'
             '    int a[3] = {1, 2, 3};\n    call reverse(a, 3);\n}\n', tmp_path)
  assert any("a[3] = {3, 2, 1}" in line for line in out)


if __name__ == "__main__":
  raise SystemExit(pytest.main([__file__, "-q"]))
