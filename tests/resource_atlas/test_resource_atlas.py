"""Regression tests for the resource atlas.

Keeps the committed artefacts honest: the generated variants must match the
generator, a few spot measurements must match the committed CSV, and the
static bounds must hold on the spot-checked programs.  The full
re-measurement (`python3 -m tests.resource_atlas.measure`) is not run here.
"""
from __future__ import annotations

import csv
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from tests.resource_atlas import gen_inputs  # noqa: E402
from tests.resource_atlas.common import DATA_DIR, GENERATED_DIR, corpus_files, measure  # noqa: E402

SPOT = {
    # filename: (family, predicted stack_peak)
    "gcd_fib_k05.ja": ("gcd_fib", 5),
    "gcd_pair_100_7.ja": ("gcd_pair", 18),
    "bubble_sort_n05.ja": ("bubble_sort", 10),
    "bubble_sort_fwd_n04.ja": ("bubble_sort_fwd", 6),
    "bubble_sort_perm_n05.ja": ("bubble_sort_perm", 10),
    "knapsack_n03.ja": ("knapsack", 0),
    "lcs_n03.ja": ("lcs", 0),
    "edit_distance_n03.ja": ("edit_distance", 0),
}


class GeneratedVariantsTests(unittest.TestCase):
    def test_generated_files_are_current(self):
        vs = gen_inputs.variants()
        self.assertGreaterEqual(len(vs), 120)
        names = {v.filename for v in vs}
        on_disk = {p.name for p in GENERATED_DIR.glob("*.ja")}
        self.assertEqual(on_disk, names, "stale or missing files under generated/")
        for v in vs:
            with self.subTest(v.filename):
                self.assertEqual(v.path.read_text(), gen_inputs.render(v))

    def test_originals_are_untouched_in_variants(self):
        """The procedure part of every variant is byte-identical to its original."""
        for v in gen_inputs.variants():
            with self.subTest(v.filename):
                original = (gen_inputs.EXAMPLES / v.original).read_text()
                procs = original[: original.index("procedure main()")]
                self.assertIn(procs, v.path.read_text())

    def test_corpus_is_101_programs(self):
        self.assertEqual(len(corpus_files()), 101)


class SpotMeasurementTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        with (DATA_DIR / "scaling.csv").open() as fh:
            cls.scaling = {Path(r["file"]).name: r for r in csv.DictReader(fh)}

    def test_spot_variants_match_law_and_csv(self):
        for name, (family, predicted) in SPOT.items():
            with self.subTest(name):
                m = measure(GENERATED_DIR / name, gen_inputs.STD)
                self.assertIsNone(m.error)
                p = m.profile
                self.assertEqual(p.stack_peak, predicted)
                row = self.scaling[name]
                self.assertEqual(row["family"], family)
                self.assertEqual(int(row["steps"]), p.total_steps)
                self.assertEqual(int(row["stack_peak"]), p.stack_peak)
                self.assertEqual(int(row["final_live_bits"]), p.final_live_bits)
                self.assertEqual(row["match"], "True")
                # static bounds are sound (and, for these programs, tight)
                pred = m.prediction
                self.assertEqual(p.call_depth_max, pred.depth_bound)
                self.assertEqual(p.total_calls, pred.calls_bound)
                self.assertEqual(pred.stack_free, p.stack_peak == 0)

    def test_rc03_six_point_rows_reproduced(self):
        """gcd_fib and forward-only bubble sort reproduce rc03's scaling rows
        (assets/tables/scaling.tex) exactly at the six sizes rc03 measured."""
        expect = {
            "gcd_fib": {4: 20, 6: 28, 8: 36, 10: 44, 12: 52, 14: 60},
            "bubble_sort_fwd": {4: 68, 6: 148, 8: 260, 10: 404, 12: 580, 14: 788},
        }
        for family, table in expect.items():
            for size, steps in table.items():
                with self.subTest(family=family, size=size):
                    row = self.scaling[f"{family}_{'k' if family == 'gcd_fib' else 'n'}{size:02d}.ja"]
                    self.assertEqual(int(row["steps"]), steps)

    def test_no_violations_recorded(self):
        with (DATA_DIR / "prediction_vs_measurement.csv").open() as fh:
            rows = list(csv.DictReader(fh))
        self.assertEqual(len(rows), 101 + len(gen_inputs.variants()))
        for r in rows:
            with self.subTest(r["file"]):
                self.assertEqual(r["error"], "")
                self.assertNotEqual(r["depth_ok"], "False")
                self.assertNotEqual(r["stack_ok"], "False")
                self.assertNotEqual(r["calls_ok"], "False")


if __name__ == "__main__":
    unittest.main()
