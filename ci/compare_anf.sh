#!/bin/sh
# Usage: GOROROBA_QUANTUM=PATH sh ci/compare_anf.sh
# Compares the algebraic normal form of a Boolean truth table in three
# implementations on the same inputs (ci/compare_anf.py): Tower.anfCoeff,
# Tower.anfEval and Tower.anfDegree of
# lean/GororobaMath/CayleyDickson/BooleanAnf.lean, anf_coef and anf_eval of
# rocq/quantum/CdSignRowAnf.v with anf_degree of
# rocq/quantum/CdAssociatorCensus.v, and anf_coefficients, evaluate_anf and
# anf_degree of gororoba_quantum/boolean_anf.py in the gororoba-quantum
# checkout at $GOROROBA_QUANTUM. The inputs are every truth table on 0, 1, 2
# and 3 variables and the sign rows x -> [cd_sign(2^k, x, m) = -1] for every m
# at the levels 3, 4 and 5; for each table the comparison covers the
# coefficient table and the evaluation of that coefficient table at every
# input, which must return the truth table, and the degree row, the largest
# weight of a mask with coefficient 1. Lean runs as a program under
# lake env lean --run, Rocq evaluates with vm_compute after compiling the
# closure of the Rocq source from a copy of rocq/quantum of this checkout, and
# the Python side generates the tables with cd_core.cd_sign and hands them to
# the other two as integer literals. The open-tree spelling anf_evaluate
# (canonical_anf) of rocq/open/theories/BooleanANFDegree.v is compared by
# ci/compare_open_tree.sh. Before the verdict counts, the comparison must
# reject a Rocq reference whose submask test is reversed, a
# Rocq reference whose degree skips the monomial of every variable, a Python
# reference with one coefficient changed and a Python reference with one
# degree raised. Prints the gororoba-quantum
# commit and the sha256 of the Python files read. Runs on demand, outside
# ci/check.sh, because it reads another repository and needs the Rocq switch of
# ci/install_rocq.sh beside the Lean toolchain with a built lean/.lake (the
# script runs lake build --no-build, which builds nothing).
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool, the
# switch or the checkout is missing, a source does not compile or the Lean
# module is stale. On a stale Lean module, Lake writes a .nobuild trace beside
# the module's trace in lean/.lake before the script exits 2; otherwise the
# script writes only under a temporary directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
export PYTHON
for tool in git lake opam "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_anf: $tool is not on PATH" >&2
    exit 2
  }
done
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_anf: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}
[ -n "${GOROROBA_QUANTUM:-}" ] || {
  echo "compare_anf: set GOROROBA_QUANTUM to a gororoba-quantum checkout" >&2
  exit 2
}
[ -f "$GOROROBA_QUANTUM/gororoba_quantum/boolean_anf.py" ] || {
  echo "compare_anf: $GOROROBA_QUANTUM/gororoba_quantum/boolean_anf.py does not exist" >&2
  exit 2
}
quantum=$(CDPATH='' cd -- "$GOROROBA_QUANTUM" && pwd)

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

"$PYTHON" -I -B "$here/compare_anf.py" import "$quantum" || exit 2
mkdir "$work/quantum"
git -C "$root" ls-files -z -- 'rocq/quantum/*.v' | (cd "$root" && xargs -0 cp -t "$work/quantum")
"$PYTHON" -I -B "$here/compare_anf.py" cases "$quantum" "$work/CompareAnf.lean" "$work/quantum/CompareAnf.v" \
  "$work/quantum/CompareAnfMutant.v" "$work/quantum/CompareAnfDegreeMutant.v" || exit 2
(
  cd "$work/quantum"
  opam exec --switch="$switch" -- rocq dep -Q . "" ./*.v >"$work/dep.txt" 2>"$work/dep.log" || {
    echo "compare_anf: rocq dep failed" >&2
    exit 2
  }
  "$PYTHON" -I "$here/compare_anf.py" closure CdAssociatorCensus.v <"$work/dep.txt" >"$work/closure.txt" || exit 2
  echo "compare_anf: compiling $(grep -c . "$work/closure.txt") sources"
  while IFS= read -r source; do
    opam exec --switch="$switch" -- rocq compile -q -Q . "" "$source" >>"$work/compile.log" 2>&1 || {
      echo "compare_anf: $source does not compile" >&2
      exit 2
    }
  done <"$work/closure.txt"
  opam exec --switch="$switch" -- rocq compile -q -Q . "" CompareAnf.v >"$work/rocq.txt" 2>&1 || {
    echo "compare_anf: the Rocq evaluation fails:" >&2
    tail -n 20 "$work/rocq.txt" >&2
    exit 2
  }
  opam exec --switch="$switch" -- rocq compile -q -Q . "" CompareAnfMutant.v >"$work/mutant.txt" 2>&1 || {
    echo "compare_anf: the mutated Rocq evaluation fails:" >&2
    tail -n 20 "$work/mutant.txt" >&2
    exit 2
  }
  opam exec --switch="$switch" -- rocq compile -q -Q . "" CompareAnfDegreeMutant.v >"$work/degree_mutant.txt" 2>&1 || {
    echo "compare_anf: the Rocq evaluation with the mutated degree fails:" >&2
    tail -n 20 "$work/degree_mutant.txt" >&2
    exit 2
  }
)
cd "$root/lean"
lake build --no-build -q GororobaMath.CayleyDickson.BooleanAnf >&2 || {
  echo "compare_anf: build the Lean library first (lake build in lean/)" >&2
  exit 2
}
lake env lean --run "$work/CompareAnf.lean" >"$work/lean.txt" || {
  echo "compare_anf: the Lean program failed" >&2
  exit 2
}
status=0
"$PYTHON" -I -B "$here/compare_anf.py" compare "$quantum" "$work/lean.txt" "$work/mutant.txt" >/dev/null 2>&1 ||
  status=$?
[ "$status" -eq 1 ] || {
  echo "compare_anf: the comparison did not reject the Rocq reference with a reversed submask test (status $status)" >&2
  exit 1
}
status=0
"$PYTHON" -I -B "$here/compare_anf.py" compare "$quantum" "$work/lean.txt" "$work/rocq.txt" --mutate-python \
  >/dev/null 2>&1 || status=$?
[ "$status" -eq 1 ] || {
  echo "compare_anf: the comparison did not reject the Python reference with one coefficient changed (status $status)" >&2
  exit 1
}
status=0
"$PYTHON" -I -B "$here/compare_anf.py" compare "$quantum" "$work/lean.txt" "$work/degree_mutant.txt" >/dev/null 2>&1 ||
  status=$?
[ "$status" -eq 1 ] || {
  echo "compare_anf: the comparison did not reject the Rocq degree that skips the monomial of every variable (status $status)" >&2
  exit 1
}
status=0
"$PYTHON" -I -B "$here/compare_anf.py" compare "$quantum" "$work/lean.txt" "$work/rocq.txt" --mutate-python-degree \
  >/dev/null 2>&1 || status=$?
[ "$status" -eq 1 ] || {
  echo "compare_anf: the comparison did not reject the Python degree raised by one (status $status)" >&2
  exit 1
}
echo "compare_anf: the reversed Rocq submask test, the Rocq degree without the top monomial, the changed Python coefficient and the raised Python degree are rejected"
"$PYTHON" -I -B "$here/compare_anf.py" compare "$quantum" "$work/lean.txt" "$work/rocq.txt" || exit $?
echo "compare_anf: gororoba-quantum $(git -C "$quantum" rev-parse HEAD)"
