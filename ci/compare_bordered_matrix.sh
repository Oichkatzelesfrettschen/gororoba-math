#!/bin/sh
# Usage: PYTHON=PATH sh ci/compare_bordered_matrix.sh
# Compares the bordered matrix of lean/GororobaMath/LinearAlgebra/PfaffianSixteen.lean in Lean and Rocq on
# the same integer inputs (ci/compare_bordered_matrix.py): PfaffianSixteen.borderedA z t a b for a, b below
# 16 and PfaffianSixteen.rhsv z t, against Amat a b and rhs of rocq/quantum/StiefelA5Certificate.v evaluated
# at the same z and t through ev of rocq/quantum/StiefelA5Pfaffian.v instantiated at the integers (the
# evaluation of its theorem pf_A_eval). The cases are 24 seeded pairs of integer vectors z, t with entries of
# both signs, a z with zeros at every fourth seed. At three seeds Matrix.pfaffian of PfaffianSixteenSchur.A16
# is also evaluated and compared with P.pf of PfaffianTheory over the evaluated matrix and with the Rocq
# rhs. Lean runs as a program under lake env lean --run, and Rocq evaluates with vm_compute after compiling
# the closure of StiefelA5Pfaffian.v from a copy of rocq/quantum of this checkout. Before the verdict counts,
# the comparison must reject two mutated Rocq references: Amat 3 5 negated, and z and t exchanged. The
# Rocq sources are in this repository, so the script reads no other checkout. Runs on demand, outside
# ci/check.sh, because it needs the Rocq switch of ci/install_rocq.sh beside the Lean toolchain with a built
# lean/.lake (the script runs lake build --no-build, which builds nothing).
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool or the switch is missing, a
# source does not compile, an output is empty or incomplete, or the Lean module is stale. On a stale Lean
# module, Lake writes a .nobuild trace beside the module's trace in lean/.lake before the script exits 2;
# otherwise the script writes only under a temporary directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
export PYTHON
for tool in git lake opam "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_bordered_matrix: $tool is not on PATH" >&2
    exit 2
  }
done
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_bordered_matrix: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

mkdir "$work/quantum"
git -C "$root" ls-files -z -- 'rocq/quantum/*.v' | (cd "$root" && xargs -0 cp -t "$work/quantum")
"$PYTHON" -I -B "$here/compare_bordered_matrix.py" cases "$work/CompareBordered.lean" "$work/quantum" || exit 2
(
  cd "$work/quantum"
  opam exec --switch="$switch" -- rocq dep -Q . "" ./*.v >"$work/dep.txt" 2>"$work/dep.log" || {
    echo "compare_bordered_matrix: rocq dep failed" >&2
    exit 2
  }
  "$PYTHON" -I -B "$here/compare_bordered_matrix.py" closure StiefelA5Pfaffian.v <"$work/dep.txt" \
    >"$work/closure.txt" || exit 2
  echo "compare_bordered_matrix: compiling $(grep -c . "$work/closure.txt") sources"
  while IFS= read -r source; do
    opam exec --switch="$switch" -- rocq compile -q -Q . "" "$source" >>"$work/compile.log" 2>&1 || {
      echo "compare_bordered_matrix: $source does not compile" >&2
      tail -n 20 "$work/compile.log" >&2
      exit 2
    }
  done <"$work/closure.txt"
  for name in CompareBordered CompareBorderedSign CompareBorderedSwap; do
    opam exec --switch="$switch" -- rocq compile -q -Q . "" "$name.v" >"$work/$name.txt" 2>&1 || {
      echo "compare_bordered_matrix: the Rocq evaluation $name fails:" >&2
      tail -n 20 "$work/$name.txt" >&2
      exit 2
    }
  done
)
cd "$root/lean"
lake build --no-build -q GororobaMath.LinearAlgebra.PfaffianSixteenSchur >&2 || {
  echo "compare_bordered_matrix: build the Lean library first (lake build in lean/)" >&2
  exit 2
}
lake env lean --run "$work/CompareBordered.lean" >"$work/lean.txt" || {
  echo "compare_bordered_matrix: the Lean program failed" >&2
  exit 2
}
for pair in "Sign:Amat 3 5 negated" "Swap:z and t exchanged"; do
  name=${pair%%:*}
  status=0
  "$PYTHON" -I -B "$here/compare_bordered_matrix.py" rows "$work/lean.txt" "$work/CompareBordered$name.txt" \
    >/dev/null 2>&1 || status=$?
  [ "$status" -eq 1 ] || {
    echo "compare_bordered_matrix: the comparison did not reject the mutated Rocq reference (${pair#*:}), status $status" >&2
    exit 1
  }
  echo "compare_bordered_matrix: the Rocq reference with ${pair#*:} is rejected"
done
"$PYTHON" -I -B "$here/compare_bordered_matrix.py" compare "$work/lean.txt" "$work/CompareBordered.txt" || exit $?
