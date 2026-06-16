#!/usr/bin/env bash
# Build the extracted interpreters + drivers, then differentially test the
# verified interpreters against PyJanus.
set -euo pipefail
cd "$(dirname "$0")/.."          # -> coq/
export PYTHONPATH="$(dirname "$(pwd)")"   # repo root, so `-m jana_py.cli` resolves

# 1. extract the verified interpreters to OCaml
[ -f janus_verified.ml ] || rocq compile RevExtract.v   >/dev/null
[ -f janus_param.ml    ] || rocq compile RevExtractP.v  >/dev/null
[ -f janus_arr.ml      ] || rocq compile RevExtractAr.v >/dev/null

# 2. build the drivers
ocamlc -w -a -o harness/driver   janus_verified.mli janus_verified.ml harness/driver.ml
ocamlc -w -a -o harness/driverp  janus_param.mli    janus_param.ml    harness/driverp.ml
ocamlc -w -a -o harness/driverar janus_arr.mli      janus_arr.ml      harness/driverar.ml

# 3. core interpreter on the in-subset fixtures (quick check)
echo "== core interpreter (RevExtract) =="
python3 harness/differential.py harness/driver harness/fixtures/{arith_swap,loop_count,mul_acc,xor_swap}.ja

# 4. array+procedure interpreter (RevExtractAr, most capable) on the repo's real
#    fixtures + local fixtures
echo; echo "== array + procedure interpreter (RevExtractAr) =="
python3 harness/differentialar.py harness/driverar \
    ../tests/jana2014/fixtures/examples/*.ja harness/fixtures/*.ja
