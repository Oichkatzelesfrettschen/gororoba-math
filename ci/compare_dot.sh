#!/bin/sh
# Usage: sh ci/compare_dot.sh
# Compares Tower.dot and Tower.re of
# lean/GororobaMath/CayleyDickson/AnnihilatorSymmetry.lean with dot and re of
# rocq/quantum/CdImaginarySumConference.v (the integer instance of the
# functor CdTower of rocq/quantum/CdTowerDomain.v) on 36 pairs of integer
# vectors at levels 0 to 5 drawn from a fixed seed (ci/compare_dot.py): Lean
# evaluates them in a compiled program, Rocq with vm_compute after compiling
# the integer file of this checkout. The comparison must also reject a Rocq
# reference whose dot keeps only the first half of each pair and whose re
# reads the second half. Runs on demand, outside ci/check.sh, because it
# needs the Rocq switch of ci/install_rocq.sh beside the Lean toolchain.
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool or
# the switch is missing. The script runs lake build, which builds a stale
# AnnihilatorSymmetry module and its imports in lean/.lake; otherwise it
# writes only under a temporary directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
for tool in git lake opam "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_dot: $tool is not on PATH" >&2
    exit 2
  }
done
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_dot: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT INT TERM

"$PYTHON" -I "$here/compare_dot.py" cases "$work/Dot.lean" "$work/Dot.v" "$work/DotMutant.v"
cp "$root/rocq/quantum/CdImaginarySumConference.v" "$work/"
(
  cd "$work"
  opam exec --switch="$switch" -- rocq compile -q -Q . "" CdImaginarySumConference.v >"$work/compile.log" 2>&1
  opam exec --switch="$switch" -- rocq compile -q -Q . "" Dot.v >"$work/rocq.txt"
  opam exec --switch="$switch" -- rocq compile -q -Q . "" DotMutant.v >"$work/mutant.txt"
)
cd "$root/lean"
lake build -q GororobaMath.CayleyDickson.AnnihilatorSymmetry
lake env lean --run "$work/Dot.lean" >"$work/lean.txt"
"$PYTHON" -I "$here/compare_dot.py" compare "$work/lean.txt" "$work/rocq.txt"
status=0
"$PYTHON" -I "$here/compare_dot.py" compare "$work/lean.txt" "$work/mutant.txt" >/dev/null 2>&1 || status=$?
[ "$status" -eq 1 ] || {
  echo "compare_dot: the comparison did not reject the mutated reference (status $status)" >&2
  exit 1
}
echo "compare_dot: the mutated reference is rejected"
