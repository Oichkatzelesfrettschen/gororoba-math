#!/bin/sh
# Usage: GOROROBA_QUANTUM=PATH sh ci/compare_kernel_map_bins.sh [LEVEL [SCOPE]]
# Compares the bin contract of
# KernelMap.nullity_eq_alignedPairCount_of_binContract with the ideal kernel
# map of pathion_kernel_map in the gororoba-quantum checkout at
# $GOROROBA_QUANTUM, at level LEVEL (5, 6 or 7; default 5), dimension
# D = 2^LEVEL: for every two-term operand e_i + t e_j (i != j, t = +1 or -1;
# 1,984 operands at level 5, 8,064 at 6, 32,512 at 7), Python computes the
# ideal output contrast of kernel_map_circuit at dim D, and at levels 6 and 7
# also the contrast of each operand of pathion_wide_coset.WIDE_OPERANDS at
# that dimension as its coset-block circuits produce it. SCOPE all (the
# default) takes every operand; SCOPE wide, at levels 6 and 7, takes only the
# wide operands and the mutants, the circuits the 64- and 128-dimensional
# runs executed. COMPARE_JOBS > 1 sweeps the operands in that many worker
# processes. Measured on the build host under a 4 GiB memory cap: level 5
# all 56 s, level 6 all 237 s, level 7 wide 5 s. Level 7 all needs more than
# 4 GiB, since pathion_kernel_map._k_matrix caches a 128 KiB matrix for each
# of the 32,512 operands; issue 36 records its run on a hosted runner.
# Exit status: 0 agreement and every mutant rejected, 1 a difference or an
# accepted mutant, 2 a tool or the checkout is missing, the checkout's
# gororoba_quantum directory is modified or changes during the run, or the
# LEVEL and SCOPE pair is not one of those above. Writes
# only under a temporary directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
level=${1:-5}
scope=${2:-all}
case $level:$scope in
  5:all | 6:all | 6:wide | 7:all | 7:wide) ;;
  *)
    echo "compare_kernel_map_bins: LEVEL SCOPE must be 5 all, 6 all, 6 wide, 7 all or 7 wide, not $level $scope" >&2
    exit 2
    ;;
esac
for tool in git lake sha256sum "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_kernel_map_bins: $tool is not on PATH" >&2
    exit 2
  }
done
quantum=${GOROROBA_QUANTUM:?compare_kernel_map_bins: set GOROROBA_QUANTUM to a gororoba-quantum checkout}
[ -f "$quantum/gororoba_quantum/pathion_kernel_map.py" ] || {
  echo "compare_kernel_map_bins: $quantum/gororoba_quantum/pathion_kernel_map.py does not exist" >&2
  exit 2
}
quantum=$(CDPATH='' cd -- "$quantum" && pwd)
[ -z "$(git -C "$quantum" status --porcelain -- gororoba_quantum)" ] || {
  echo "compare_kernel_map_bins: $quantum/gororoba_quantum has uncommitted changes" >&2
  exit 2
}
commit=$(git -C "$quantum" rev-parse HEAD)
tree=$(git -C "$quantum" rev-parse HEAD:gororoba_quantum)

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

"$PYTHON" -B "$here/compare_kernel_map_bins.py" cases "$level" "$scope" "$quantum" "$work/KernelMapBins.lean" "$work/cases.txt" "$work/python.json"
cd "$root/lean"
lake env lean --run "$work/KernelMapBins.lean" "$work/cases.txt" >"$work/lean.txt"
"$PYTHON" -B "$here/compare_kernel_map_bins.py" compare "$work/python.json" "$work/lean.txt"
[ -z "$(git -C "$quantum" status --porcelain -- gororoba_quantum)" ] &&
  [ "$(git -C "$quantum" rev-parse HEAD:gororoba_quantum)" = "$tree" ] || {
  echo "compare_kernel_map_bins: $quantum/gororoba_quantum changed during the run" >&2
  exit 1
}
echo "compare_kernel_map_bins: level $level, scope $scope, gororoba-quantum $commit, gororoba_quantum tree $tree"
for module in pathion_kernel_map pathion_coset_block pathion_wide_coset; do
  echo "compare_kernel_map_bins: $module.py sha256 $(sha256sum "$quantum/gororoba_quantum/$module.py" | cut -d' ' -f1)"
done
"$PYTHON" -c 'import numpy, qiskit; print(f"compare_kernel_map_bins: numpy {numpy.__version__}, qiskit {qiskit.__version__}")'

