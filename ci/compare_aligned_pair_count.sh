#!/bin/sh
# Usage: sh ci/compare_aligned_pair_count.sh
# Compares Tower.alignedPairCount of lean/GororobaMath/CayleyDickson/TwoTerm.lean
# with TwoTermRecursion.aligned_pair_count of
# rocq/quantum/CdTowerTwoTermRecursion.v on every pair of indices i, j below
# 2^k at the levels 0 to 7, 21845 pairs (ci/compare_aligned_pair_count.py):
# Lean evaluates them in a program run by lake env lean --run, Rocq with
# vm_compute after compiling the closure of the Rocq source from a copy of
# rocq/quantum of this checkout. The comparison must also reject a Rocq
# reference that counts only the indices with aligned_add. Runs on demand,
# outside ci/check.sh, because it needs the Rocq switch of
# ci/install_rocq.sh beside the Lean toolchain.
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool or
# the switch is missing or a source does not compile. Writes only under a
# temporary directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
for tool in git lake opam "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_aligned_pair_count: $tool is not on PATH" >&2
    exit 2
  }
done
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_aligned_pair_count: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
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
"$PYTHON" -I "$here/compare_aligned_pair_count.py" cases "$work/Count.lean" "$work/quantum/Count.v" \
  "$work/quantum/CountMutant.v"
(
  cd "$work/quantum"
  opam exec --switch="$switch" -- rocq dep -Q . "" ./*.v >"$work/dep.txt" 2>"$work/dep.log" || {
    echo "compare_aligned_pair_count: rocq dep failed" >&2
    exit 2
  }
  "$PYTHON" -I "$here/compare_aligned_pair_count.py" closure CdTowerTwoTermRecursion.v <"$work/dep.txt" \
    >"$work/closure.txt" || exit 2
  while IFS= read -r source; do
    opam exec --switch="$switch" -- rocq compile -q -Q . "" "$source" >>"$work/compile.log" 2>&1 || {
      echo "compare_aligned_pair_count: $source does not compile" >&2
      exit 2
    }
  done <"$work/closure.txt"
  opam exec --switch="$switch" -- rocq compile -q -Q . "" Count.v >"$work/rocq.txt" 2>&1 || exit 2
  opam exec --switch="$switch" -- rocq compile -q -Q . "" CountMutant.v >"$work/mutant.txt" 2>&1 || exit 2
)
cd "$root/lean"
lake build -q GororobaMath.CayleyDickson.TwoTerm
lake env lean --run "$work/Count.lean" >"$work/lean.txt"
"$PYTHON" -I "$here/compare_aligned_pair_count.py" compare "$work/lean.txt" "$work/rocq.txt"
status=0
"$PYTHON" -I "$here/compare_aligned_pair_count.py" compare "$work/lean.txt" "$work/mutant.txt" >/dev/null 2>&1 ||
  status=$?
[ "$status" -eq 1 ] || {
  echo "compare_aligned_pair_count: the comparison did not reject the mutated reference (status $status)" >&2
  exit 1
}
echo "compare_aligned_pair_count: the mutated reference is rejected"
