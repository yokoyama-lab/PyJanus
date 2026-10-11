#!/usr/bin/env bash
# Re-measure the differential-testing numbers the Janus mechanization paper
# quotes, on an exact commit, in a throw-away export (no worktree is touched).
#
#   cd <PyJanus checkout> && coq/harness/measure/remeasure.sh <commit> <out-dir>
#
# Writes <out-dir>/{meta.tsv,junit.xml,pytest.log,codegen_diff.log,
# fuel_probe.log,counts.tsv}.
# Cost on mikawa (2026-10-11): Rocq extraction 38 s / 1.5 GB, pytest 6.5 min /
# 0.2 GB, codegen diff 1.5 min.  All under runcap.
set -euo pipefail
commit="$1"; out="$(realpath -m "$2")"; mkdir -p "$out"
here="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$here" && git rev-parse --show-toplevel)"
work="$(mktemp -d)"; trap 'rm -rf "$work"' EXIT
(cd "$repo" && git archive "$commit") | tar -x -C "$work"
printf 'commit\t%s\n' "$(cd "$repo" && git rev-parse "$commit")" > "$out/meta.tsv"
cd "$work/coq"
rocq makefile -f _CoqProject -o Makefile >/dev/null
runcap -m 8 -t 600 -N 10 -- make -j4 RevExtract.vo RevExtractP.vo RevExtractAr.vo RevExtractFrame.vo >/dev/null
for f in janus_verified.ml janus_param.ml janus_arr.ml janus_frame.ml; do
  [ -s "$f" ] || { echo "extraction did not produce $f" >&2; exit 1; }
done
cd "$work"
rc=0
runcap -m 8 -t 900 -N 10 -- python3 -m pytest -q -p no:cacheprovider -rs \
  --junitxml="$out/junit.xml" \
  tests/jana2014/test_verified_corpus.py tests/jana2014/test_vjanus_corpus.py \
  tests/jana2014/test_vjanus_inverse.py tests/jana2014/test_verified_cores_corpus.py \
  > "$out/pytest.log" 2>&1 || rc=$?
printf 'pytest_exit\t%s\n' "$rc" >> "$out/meta.tsv"
runcap -m 8 -t 600 -N 10 -- python3 coq/harness/codegen_diff.py \
  tests/jana2014/fixtures/examples/*.ja coq/harness/fixtures/*.ja \
  2>/dev/null | grep -v '^Warning' > "$out/codegen_diff.log"
printf 'corpus.examples\t%s\n' "$(ls tests/jana2014/fixtures/examples/*.ja | wc -l)" >> "$out/meta.tsv"
printf 'corpus.harness_fixtures\t%s\n' "$(ls coq/harness/fixtures/*.ja | wc -l)" >> "$out/meta.tsv"
# Why does the one "out of fuel?" skip return NONE?  See fuel_probe.sh.
bash "$here/fuel_probe.sh" "$work" > "$out/fuel_probe.log" 2>&1 || true
python3 "$here/tally_differential.py" "$out" > "$out/counts.tsv"
