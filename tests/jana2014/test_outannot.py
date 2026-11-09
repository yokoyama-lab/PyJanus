"""Tests for jana_py.outannot (output / garbage annotations).

Covers:
1. Structured-comment parsing (// @out: / @in: / @garbage: / @scratch:)
2. Conflicting roles, bad names, dotted struct fields, trailing []
3. Sidecar loading, lookup by path / suffix / basename, 101-entry invariants
4. classify(): the four terminal classes and the mismatch notes
5. summarize(): the RC-03 shape (written / never-take / ends-empty)
6. recount.py end to end on a tiny CSV
"""
from __future__ import annotations

import csv
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from jana_py import outannot  # noqa: E402
from jana_py.outannot import (  # noqa: E402
  Annotation, AnnotationError, CLASS_CLEAN, CLASS_GARBAGE, CLASS_INPUT, CLASS_OUTPUT,
  ROLE_GARBAGE, ROLE_IN, ROLE_OUT, ROLE_SCRATCH,
  annotation_for_program, classify, classify_detailed, load_sidecar,
  parse_comment_annotations, sidecar_for, summarize,
)

SIDECAR = ROOT / "tests" / "resource_atlas" / "annotations" / "out_annotations.json"
CORPUS_DIRS = {
  "tests/jana2014/fixtures/examples": 85,
  "tests/jana2014_in_out/fixtures/examples": 10,
  "tests/janus2026/fixtures/examples": 4,
  "tests/jana2014basic/fixtures/examples": 2,
}


class TestCommentParsing(unittest.TestCase):

  def test_basic_tags(self):
    src = textwrap.dedent("""
      // Reversible knapsack
      // @out: K
      // @in: wt, val
      procedure main()
        int wt[4]
        // @garbage: gb
        stack gb
    """)
    ann = parse_comment_annotations(src)
    self.assertEqual(ann.roles, {"K": ROLE_OUT, "wt": ROLE_IN, "val": ROLE_IN, "gb": ROLE_GARBAGE})
    self.assertEqual(ann.outputs, ["K"])
    self.assertEqual(ann.inputs, ["val", "wt"])
    self.assertEqual(ann.source, "comment")

  def test_aliases_and_spacing(self):
    src = "//@output:a b\n//   @INPUT :  x ,y\n// @gb: g\n// @scratch: t\n"
    ann = parse_comment_annotations(src)
    self.assertEqual(ann.roles, {"a": ROLE_OUT, "b": ROLE_OUT, "x": ROLE_IN, "y": ROLE_IN,
                                 "g": ROLE_GARBAGE, "t": ROLE_SCRATCH})

  def test_block_comment_and_trailing_brackets(self):
    ann = parse_comment_annotations("/* @out: d[] */\n/* @in: n */")
    self.assertEqual(ann.roles, {"d": ROLE_OUT, "n": ROLE_IN})

  def test_dotted_struct_field(self):
    ann = parse_comment_annotations("// @in: a.v, a.grid\n// @out: r")
    self.assertEqual(ann.role_of("a.v"), ROLE_IN)
    self.assertEqual(ann.role_of("a.grid"), ROLE_IN)

  def test_non_tag_comments_ignored(self):
    src = "// outputs: dist[], pred[] and the logs\n// @foo: bar\n int x\n"
    self.assertEqual(parse_comment_annotations(src).roles, {})
    self.assertFalse(outannot.has_comment_annotations(src))
    self.assertTrue(outannot.has_comment_annotations("// @out: x"))

  def test_conflict_strict_raises(self):
    with self.assertRaises(AnnotationError):
      parse_comment_annotations("// @out: x\n// @in: x\n")

  def test_conflict_lenient_last_wins(self):
    ann = parse_comment_annotations("// @out: x\n// @in: x\n", strict=False)
    self.assertEqual(ann.roles, {"x": ROLE_IN})

  def test_same_role_twice_ok(self):
    ann = parse_comment_annotations("// @out: x\n// @out: x, y\n")
    self.assertEqual(ann.roles, {"x": ROLE_OUT, "y": ROLE_OUT})

  def test_bad_name_raises(self):
    with self.assertRaises(AnnotationError):
      parse_comment_annotations("// @out: 3x\n")
    with self.assertRaises(AnnotationError):
      parse_comment_annotations("// @out: a[0]\n")

  def test_comment_overrides_sidecar(self):
    side = Annotation(roles={"a": ROLE_IN, "b": ROLE_GARBAGE}, source="sidecar", file="x.ja", confidence="medium")
    ann = annotation_for_program("x.ja", "// @out: b\n", {"x.ja": side})
    self.assertEqual(ann.roles, {"a": ROLE_IN, "b": ROLE_OUT})
    self.assertEqual(ann.confidence, "medium")
    self.assertIn("comment", ann.source)

  def test_no_sidecar_no_comment(self):
    ann = annotation_for_program("nowhere.ja", "int x\n", {})
    self.assertEqual(ann.roles, {})


class TestSidecar(unittest.TestCase):

  @classmethod
  def setUpClass(cls):
    cls.side = load_sidecar(SIDECAR)
    with open(SIDECAR, encoding="utf-8") as f:
      cls.raw = json.load(f)

  def test_count_and_coverage(self):
    self.assertEqual(len(self.side), 101)
    for d, n in CORPUS_DIRS.items():
      files = sorted(p.relative_to(ROOT).as_posix() for p in (ROOT / d).glob("*.ja"))
      self.assertEqual(len(files), n, d)
      for f in files:
        self.assertIn(f, self.side, f)

  def test_entries_well_formed(self):
    valid_conf = {"high", "medium", "low"}
    for entry in self.raw["programs"]:
      self.assertTrue((ROOT / entry["file"]).exists(), entry["file"])
      self.assertIn(entry["confidence"], valid_conf, entry["file"])
      self.assertTrue(entry["rationale"].strip(), entry["file"])
      for role in entry["arrays"].values():
        self.assertIn(role, outannot.ROLES, entry["file"])
      for role in entry["stacks"].values():
        self.assertIn(role.split()[0], outannot.ROLES, entry["file"])
      self.assertIsInstance(entry["scalars_out"], list)

  def test_roles_normalised(self):
    gcd = self.side["tests/jana2014/fixtures/examples/gcd.ja"]
    self.assertEqual(gcd.role_of("log"), ROLE_GARBAGE)      # "garbage (reversibility log)"
    self.assertEqual(gcd.role_of("a"), ROLE_OUT)             # scalars_out
    ks = self.side["tests/jana2014/fixtures/examples/knapsack.ja"]
    self.assertEqual(ks.roles, {"wt": ROLE_IN, "val": ROLE_IN, "K": ROLE_OUT})
    self.assertEqual(ks.confidence, "medium")
    self.assertIn("K[n][W]", ks.rationale)

  def test_lookup_exact_suffix_basename(self):
    exact = sidecar_for("tests/jana2014/fixtures/examples/gcd.ja", self.side)
    self.assertIsNotNone(exact)
    self.assertIs(sidecar_for(str(ROOT / "tests/jana2014/fixtures/examples/gcd.ja"), self.side), exact)
    self.assertIs(sidecar_for("gcd.ja", self.side), exact)
    # ambiguous basename -> the jana2014 copy is preferred
    fib = sidecar_for("fib.ja", self.side)
    self.assertEqual(fib.file, "tests/jana2014/fixtures/examples/fib.ja")
    self.assertIsNone(sidecar_for("does_not_exist.ja", self.side))

  def test_low_confidence_listed_in_readme(self):
    readme = (SIDECAR.parent / "README.md").read_text(encoding="utf-8")
    lows = [e["file"] for e in self.raw["programs"] if e["confidence"] == "low"]
    self.assertTrue(lows)
    for f in lows:
      self.assertIn(f, readme)

  def test_duplicate_file_rejected(self):
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as tmp:
      json.dump({"programs": [{"file": "a.ja", "arrays": {}}, {"file": "a.ja", "arrays": {}}]}, tmp)
    try:
      with self.assertRaises(AnnotationError):
        load_sidecar(tmp.name)
    finally:
      Path(tmp.name).unlink()


def _st(puts, takes, ends_empty, written=None):
  d = {"puts": puts, "takes": takes, "ends_empty": ends_empty}
  if written is not None:
    d["written"] = written
  return d


class TestClassify(unittest.TestCase):

  def test_four_classes(self):
    state = {
      "K": _st(18, 0, False),          # annotated out, non-zero   -> output
      "wt": _st(3, 0, False),          # annotated in              -> input-preserved
      "ftab": _st(6, 0, False),        # annotated garbage         -> garbage
      "tmp": _st(4, 4, True),          # annotated scratch, empty  -> clean
      "x": _st(2, 0, False),           # unannotated               -> garbage
    }
    roles = {"K": "output", "wt": "input", "ftab": "garbage", "tmp": "scratch"}
    self.assertEqual(classify(state, roles), {
      "K": CLASS_OUTPUT, "wt": CLASS_INPUT, "ftab": CLASS_GARBAGE, "tmp": CLASS_CLEAN, "x": CLASS_GARBAGE,
    })

  def test_ends_empty_wins(self):
    state = {"ord": _st(0, 0, True), "b": _st(5, 5, True)}
    res = classify_detailed(state, {"ord": "output", "b": "input"})
    by = {c.name: c for c in res}
    self.assertEqual(by["ord"].cls, CLASS_CLEAN)
    self.assertIn("annotated output", by["ord"].note)
    self.assertEqual(by["b"].cls, CLASS_CLEAN)

  def test_scratch_not_empty_is_garbage_with_note(self):
    res = classify_detailed({"t": _st(3, 1, False)}, {"t": "scratch"})
    self.assertEqual(res[0].cls, CLASS_GARBAGE)
    self.assertIn("scratch", res[0].note)

  def test_unannotated_note_and_none_annotation(self):
    res = classify_detailed({"a": _st(1, 0, False)}, None)
    self.assertEqual(res[0].cls, CLASS_GARBAGE)
    self.assertEqual(res[0].note, "unannotated")

  def test_accepts_annotation_object_and_string_flags(self):
    ann = parse_comment_annotations("// @out: d\n// @in: n")
    state = {"d": {"puts": "4", "takes": "0", "ends_empty": "false", "written": "true"},
             "n": {"puts": "1", "takes": "0", "ends_empty": "0", "written": "1"}}
    self.assertEqual(classify(state, ann), {"d": CLASS_OUTPUT, "n": CLASS_INPUT})

  def test_stack_role_string_normalised(self):
    self.assertEqual(classify({"log": _st(4, 0, False)}, {"log": "garbage (reversibility log)"}),
                     {"log": CLASS_GARBAGE})

  def test_written_defaults_from_puts(self):
    res = classify_detailed({"a": _st(0, 0, True), "b": _st(2, 0, False)}, {})
    self.assertFalse(res[0].written)
    self.assertTrue(res[1].written)

  def test_summarize_shape(self):
    state = {
      "K": _st(18, 0, False), "wt": _st(3, 0, False), "ftab": _st(6, 0, False),
      "tmp": _st(4, 4, True), "x": _st(2, 0, False), "never": _st(0, 0, True),
      "partial": _st(5, 2, False),
    }
    roles = {"K": "output", "wt": "input", "ftab": "garbage", "tmp": "scratch", "partial": "output"}
    s = summarize(classify_detailed(state, roles))
    self.assertEqual(s["arrays"], 7)
    self.assertEqual(s["written"], 6)            # 'never' has no puts
    self.assertEqual(s["never_take"], 4)         # K wt ftab x
    self.assertEqual(s["never_take_by_class"], {CLASS_OUTPUT: 1, CLASS_INPUT: 1, CLASS_GARBAGE: 2, CLASS_CLEAN: 0})
    self.assertEqual(s["ends_empty"], 1)         # tmp
    self.assertEqual(s["by_class"][CLASS_OUTPUT], 2)
    self.assertEqual(s["unannotated"], 1)
    self.assertEqual(s["mismatches"], [])


class TestRecountScript(unittest.TestCase):

  def test_end_to_end_on_fake_csv(self):
    rows = [
      ("tests/jana2014/fixtures/examples/knapsack.ja", "wt", 3, 0, 0, 1),
      ("tests/jana2014/fixtures/examples/knapsack.ja", "val", 3, 0, 0, 1),
      ("tests/jana2014/fixtures/examples/knapsack.ja", "K", 18, 0, 0, 1),
      ("selection_sort.ja", "a", 6, 6, 0, 1),           # bare basename join
      ("selection_sort.ja", "ftab", 5, 0, 0, 1),
      ("selection_sort.ja", "p", 0, 0, 1, 0),
      ("tests/jana2014/fixtures/examples/gcd.ja", "mystery", 2, 0, 0, 1),   # unnamed in sidecar
      ("unknown_prog.ja", "z", 1, 0, 0, 1),               # unknown program
    ]
    with tempfile.TemporaryDirectory() as td:
      csv_path = Path(td) / "corpus_arrays.csv"
      with open(csv_path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["file", "array", "puts", "takes", "ends_empty", "written"])
        w.writerows(rows)
      out_path = Path(td) / "recount.md"
      proc = subprocess.run(
        [sys.executable, str(ROOT / "tests" / "resource_atlas" / "recount.py"),
         "--csv", str(csv_path), "--out", str(out_path), "--quiet"],
        cwd=ROOT, text=True, capture_output=True, check=False,
      )
      self.assertEqual(proc.returncode, 0, proc.stderr)
      report = out_path.read_text(encoding="utf-8")
    self.assertIn("| written arrays | 7 |", report)
    self.assertIn("| never take (takes = 0) | 6 |", report)
    self.assertIn("**output** | 1 |", report)             # K
    self.assertIn("**input-preserved** | 2 |", report)    # wt val
    self.assertIn("**garbage** | 3 |", report)            # ftab mystery z
    self.assertIn("unknown_prog.ja", report)
    self.assertIn("`mystery`", report)
    self.assertIn("ftab (5/0)", report)

  def test_missing_csv_exit_code(self):
    proc = subprocess.run(
      [sys.executable, str(ROOT / "tests" / "resource_atlas" / "recount.py"),
       "--csv", "/nonexistent/corpus_arrays.csv", "--out", "-"],
      cwd=ROOT, text=True, capture_output=True, check=False,
    )
    self.assertEqual(proc.returncode, 2)
    self.assertIn("not found", proc.stderr)


if __name__ == "__main__":
  unittest.main()
