"""Output statements do not touch the store — but they can still fail.

Dropping them wholesale (`return  # printing does not touch the store`) let the
checker **prove safe** five error fixtures that PyJanus rejects: `printf` calls
whose arguments do not match the format string, and a `show` of a name that was
never declared.  That is a false *negative*, the mirror image of the aliasing
bug in §3.3 — and the same shape of mistake: a statement the model cannot see is
a statement the model must not silently accept.

All of these failures are store-independent, so reaching the statement *is* the
error and the edge to ERR is unconditional, exactly as for a `delocal` whose two
names disagree.  Input statements (`read`, `scanf`) are the other half: they
make the next store depend on stdin, which the model has no way to represent, so
they are refused rather than answered.
"""

from __future__ import annotations

from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py import nuxmv
from jana_py import parser_jana2014
from jana_py import parser_janus2026
from jana_py import preprocess
from jana_py.smv import SmvUnsupported
from jana_py.smv import compile_to_smv

BINARY = nuxmv.find_nuxmv()

HEAD = "procedure main()\n    int x\n    int y\n    int d[3]\n    x += 42\n    y += 7\n"


def model_of(src: str, std: str = "jana2014", **kw) -> str:
  parse = (parser_jana2014 if std == "jana2014" else parser_janus2026).parse_program
  pt = preprocess.preprocess_text("<test>", src, None, std)
  return compile_to_smv(parse("<test>", pt.text, pt.line_origins), **kw)


def reaches_err(model: str) -> bool:
  """True when some edge leads unconditionally to ERR (location 0)."""
  return ": 0;" in model.split("next(pc) := case")[1].split("esac;")[0]


def interpreter_fails(src: str, std: str = "jana2014") -> bool:
  proc = subprocess.run([sys.executable, "-m", "jana_py.cli", "--std", std, "-s", "-"],
                        input=src, capture_output=True, text=True, cwd=ROOT)
  return proc.returncode != 0


#: Each one is rejected by PyJanus for a reason that does not depend on the
#: store, so the model must route to ERR unconditionally.
BAD = {
    "too many arguments": HEAD + '    printf("only one: %d", x, y)\n',
    "too few arguments": HEAD + '    printf("two: %d %d", x)\n',
    "unrecognized specifier": HEAD + '    printf("%q", x)\n',
    "type mismatch (int for %s)": HEAD + '    printf("%s", x)\n',
    "type mismatch (array for %d)": HEAD + '    printf("%d", d)\n',
    "undeclared name": HEAD + "    show(x, a)\n",
}

GOOD = {
    "matching printf": HEAD + '    printf("%d and %d", x, y)\n',
    "escaped percent": HEAD + '    printf("100%% of %d", x)\n',
    "trailing percent": HEAD + '    printf("%d%", x)\n',
    "array with %a": HEAD + '    printf("%a", d)\n',
    "indexed element": HEAD + '    printf("%d", d[1])\n',
    "show of declared names": HEAD + "    show(x, y)\n",
    "plain print": HEAD + '    print("hello")\n',
}


class MalformedOutputTests(unittest.TestCase):
  def test_pyjanus_rejects_them(self):
    for name, src in BAD.items():
      with self.subTest(name):
        self.assertTrue(interpreter_fails(src), "fixture should fail in PyJanus")

  def test_the_model_routes_them_to_err(self):
    for name, src in BAD.items():
      with self.subTest(name):
        self.assertTrue(reaches_err(model_of(src, init="zero")))


class WellFormedOutputTests(unittest.TestCase):
  def test_pyjanus_accepts_them(self):
    for name, src in GOOD.items():
      with self.subTest(name):
        self.assertFalse(interpreter_fails(src), "fixture should run cleanly")

  def test_the_model_adds_no_error_edge(self):
    for name, src in GOOD.items():
      with self.subTest(name):
        self.assertFalse(reaches_err(model_of(src, init="zero")))


class OutOfBoundsArgumentTests(unittest.TestCase):
  """Reading a cell to print it is still a read, so it is bounds-checked."""

  SRC = HEAD + '    printf("%d", d[7])\n'

  def test_pyjanus_rejects_it(self):
    self.assertTrue(interpreter_fails(self.SRC))

  def test_the_model_routes_it_to_err(self):
    self.assertTrue(reaches_err(model_of(self.SRC, init="zero")))


class InputStatementTests(unittest.TestCase):
  """`read`/`scanf` make the store depend on stdin: refuse, do not answer."""

  def test_read_is_refused(self):
    src = "void main() {\n    int x;\n    read x;\n}\n"
    with self.assertRaises(SmvUnsupported):
      model_of(src, std="janus2026", init="zero")

  def test_scanf_is_refused(self):
    src = 'void main() {\n    int x;\n    scanf("%d", x);\n}\n'
    with self.assertRaises(SmvUnsupported):
      model_of(src, std="janus2026", init="zero")


@unittest.skipIf(BINARY is None, "nuXmv not installed")
class AgreementTests(unittest.TestCase):
  """The five fixtures the checker used to prove safe."""

  FIXTURES = ("prints-printf-args-mismatch.ja", "prints-printf-args-mismatch-2.ja",
              "prints-printf-type-mismatch.ja", "prints-printf-unrecognized-type.ja",
              "prints-show-undef-var.ja")

  def test_each_fixture_is_now_refuted(self):
    for name in self.FIXTURES:
      with self.subTest(name):
        path = ROOT / "tests/jana2014/fixtures_errors" / name
        src = path.read_text(encoding="utf-8")
        self.assertTrue(interpreter_fails(src))
        result = nuxmv.check(model_of(src, init="zero"), binary=BINARY)
        self.assertEqual(result.status, "refuted", result.output[-2000:])


if __name__ == "__main__":
  unittest.main()
