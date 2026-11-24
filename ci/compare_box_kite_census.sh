#!/bin/sh
# Usage: GOROROBA_QUANTUM=PATH PYTHON=PATH sh ci/compare_box_kite_census.sh
# Compares the sedenion sign table and the associator signs of the box-kite census in two
# implementations on the same inputs (ci/compare_box_kite_census.py): sed_sign i j of
# rocq/open/verified/C1467_XORSignCocycle.v against cd_sign(16, i, j) of
# gororoba_quantum/cd_core.py on the 256 index pairs, and (lsign, rsign) of
# rocq/open/verified/C1630_BasisAssociatorTensor.v, whose product is its omega, against
# triple_sign(16, i, j, k) of cd_core.py, whose product is omega of scripts/box_kite_census.py, on
# the 4096 ordered triples. Rocq evaluates with vm_compute after compiling the two sources from a
# copy of this checkout. Before the verdict counts, the comparison must reject a mutated Rocq
# reference whose rsign takes its first two arguments exchanged. Runs on demand, outside
# ci/check.sh, because it needs the gororoba-quantum checkout that GOROROBA_QUANTUM names and the
# Rocq switch of ci/install_rocq.sh.
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool, the switch or the
# checkout is missing, or a source does not compile. The script writes only under a temporary
# directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
export PYTHON
for tool in git opam "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_box_kite_census: $tool is not on PATH" >&2
    exit 2
  }
done
[ -n "${GOROROBA_QUANTUM:-}" ] && [ -f "$GOROROBA_QUANTUM/gororoba_quantum/cd_core.py" ] || {
  echo "compare_box_kite_census: set GOROROBA_QUANTUM to a gororoba-quantum checkout" >&2
  exit 2
}
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_box_kite_census: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
quantum=$(CDPATH='' cd -- "$GOROROBA_QUANTUM" && pwd)
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

mkdir "$work/verified"
for source in C1467_XORSignCocycle.v C1630_BasisAssociatorTensor.v; do
  git -C "$root" show "HEAD:rocq/open/verified/$source" >"$work/verified/$source"
done
"$PYTHON" -I -B "$here/compare_box_kite_census.py" cases "$work/verified/CompareCensus.v" \
  "$work/verified/CompareCensusMutant.v" || exit 2
(
  cd "$work"
  for source in C1467_XORSignCocycle C1630_BasisAssociatorTensor; do
    opam exec --switch="$switch" -- rocq compile -q -R verified OpenGororobaVerified "verified/$source.v" \
      >>"$work/compile.log" 2>&1 || {
      echo "compare_box_kite_census: $source.v does not compile" >&2
      exit 2
    }
  done
  opam exec --switch="$switch" -- rocq compile -q -R verified OpenGororobaVerified verified/CompareCensus.v \
    >"$work/rocq.txt" 2>&1 || {
    echo "compare_box_kite_census: the Rocq evaluation fails:" >&2
    tail -n 20 "$work/rocq.txt" >&2
    exit 2
  }
  opam exec --switch="$switch" -- rocq compile -q -R verified OpenGororobaVerified verified/CompareCensusMutant.v \
    >"$work/mutant.txt" 2>&1 || {
    echo "compare_box_kite_census: the mutated Rocq evaluation fails:" >&2
    tail -n 20 "$work/mutant.txt" >&2
    exit 2
  }
)
status=0
"$PYTHON" -I -B "$here/compare_box_kite_census.py" compare "$quantum" "$work/mutant.txt" >/dev/null 2>&1 ||
  status=$?
[ "$status" -eq 1 ] || {
  echo "compare_box_kite_census: the comparison did not reject the mutated Rocq reference (status $status)" >&2
  exit 1
}
echo "compare_box_kite_census: the Rocq reference with exchanged rsign arguments is rejected"
"$PYTHON" -I -B "$here/compare_box_kite_census.py" compare "$quantum" "$work/rocq.txt" || exit $?
