from __future__ import annotations

import unittest


# This suite is skipped pending two follow-ups (tracked separately from the
# per-dialect test split):
#
# 1. examples/build-dict.ja currently parses under NONE of the dialect parsers
#    (janus2026/jana2014/jana2014basic/janus1982ext all reject it), so
#    test_build_dict_example_file_runs cannot pass until the example is
#    updated to a supported dialect.
# 2. The inline build-dict program exercises iterate-loops and from-loops whose
#    janus2026 (C-style) surface syntax is not yet pinned down here; porting it
#    is blocked on the same example being fixed.
@unittest.skip(
  "build-dict depends on examples/build-dict.ja, which parses under no "
  "current dialect; port blocked until the example is fixed"
)
class DictProgramTests(unittest.TestCase):
  def test_build_dict_style_program_runs(self) -> None:
    raise NotImplementedError

  def test_build_dict_example_file_runs(self) -> None:
    raise NotImplementedError


if __name__ == "__main__":
  unittest.main()
