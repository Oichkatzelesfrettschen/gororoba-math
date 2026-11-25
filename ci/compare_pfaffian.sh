#!/bin/sh
# Usage: PYTHON=PATH sh ci/compare_pfaffian.sh
# Compares the Pfaffian over the integers in two implementations on the same inputs
# (ci/compare_pfaffian.py): Matrix.pfaffianAux A l of lean/GororobaMath/LinearAlgebra/Pfaffian.lean
# and pf M l of PfaffianTheory in rocq/quantum/Pfaffian.v instantiated at Z. A matrix is a function
# of two natural-number indices and the index list holds natural numbers on both sides; both expand
# along the first index of the list with the sign (-1)^k on the k-th remaining index, so the
# arguments correspond one to one. The cases are three integer matrices (two skew, one general) on
# the full ranges of length 0 to 8, permuted and reversed lists, lists with a repeated index and
# lists of odd length. Lean runs as a program under lake env lean --run, and Rocq evaluates with
# vm_compute after compiling the closure of Pfaffian.v from a copy of rocq/quantum of this
# checkout. Before the verdict counts, the comparison must reject a copy of the Rocq definitions
# whose expansion sign is replaced by one. The Rocq sources are in this repository, so the script
# reads no other checkout. Runs on demand, outside ci/check.sh, because it needs the Rocq switch of
# ci/install_rocq.sh beside the Lean toolchain with a built lean/.lake (the script runs
# lake build --no-build, which builds nothing).
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool or the switch is
# missing, a source does not compile or the Lean module is stale. On a stale Lean module, Lake
# writes a .nobuild trace beside the module's trace in lean/.lake before the script exits 2;
# otherwise the script writes only under a temporary directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
export PYTHON
for tool in git lake opam "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_pfaffian: $tool is not on PATH" >&2
    exit 2
  }
done
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_pfaffian: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
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
"$PYTHON" -I -B "$here/compare_pfaffian.py" cases "$work/ComparePfaffian.lean" "$work/quantum" || exit 2
(
  cd "$work/quantum"
  opam exec --switch="$switch" -- rocq dep -Q . "" ./*.v >"$work/dep.txt" 2>"$work/dep.log" || {
    echo "compare_pfaffian: rocq dep failed" >&2
    exit 2
  }
  "$PYTHON" -I -B "$here/compare_pfaffian.py" closure Pfaffian.v <"$work/dep.txt" >"$work/closure.txt" || exit 2
  echo "compare_pfaffian: compiling $(grep -c . "$work/closure.txt") sources"
  while IFS= read -r source; do
    opam exec --switch="$switch" -- rocq compile -q -Q . "" "$source" >>"$work/compile.log" 2>&1 || {
      echo "compare_pfaffian: $source does not compile" >&2
      tail -n 20 "$work/compile.log" >&2
      exit 2
    }
  done <"$work/closure.txt"
  opam exec --switch="$switch" -- rocq compile -q -Q . "" PfaffianMutant.v >>"$work/compile.log" 2>&1 || {
    echo "compare_pfaffian: the mutated definitions do not compile" >&2
    tail -n 20 "$work/compile.log" >&2
    exit 2
  }
  opam exec --switch="$switch" -- rocq compile -q -Q . "" ComparePfaffian.v >"$work/rocq.txt" 2>&1 || {
    echo "compare_pfaffian: the Rocq evaluation fails:" >&2
    tail -n 20 "$work/rocq.txt" >&2
    exit 2
  }
  opam exec --switch="$switch" -- rocq compile -q -Q . "" ComparePfaffianMutant.v >"$work/mutant.txt" 2>&1 || {
    echo "compare_pfaffian: the mutated Rocq evaluation fails:" >&2
    tail -n 20 "$work/mutant.txt" >&2
    exit 2
  }
)
cd "$root/lean"
lake build --no-build -q GororobaMath.LinearAlgebra.Pfaffian >&2 || {
  echo "compare_pfaffian: build the Lean library first (lake build in lean/)" >&2
  exit 2
}
lake env lean --run "$work/ComparePfaffian.lean" >"$work/lean.txt" || {
  echo "compare_pfaffian: the Lean program failed" >&2
  exit 2
}
status=0
"$PYTHON" -I -B "$here/compare_pfaffian.py" compare "$work/lean.txt" "$work/mutant.txt" >/dev/null 2>&1 ||
  status=$?
[ "$status" -eq 1 ] || {
  echo "compare_pfaffian: the comparison did not reject the mutated Rocq reference (status $status)" >&2
  exit 1
}
echo "compare_pfaffian: the Rocq reference with the expansion sign replaced by one is rejected"
"$PYTHON" -I -B "$here/compare_pfaffian.py" compare "$work/lean.txt" "$work/rocq.txt" || exit $?
