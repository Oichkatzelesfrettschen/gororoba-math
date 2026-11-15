#!/bin/sh
# Usage: GOROROBA_QUANTUM=PATH sh ci/compare_kernel_map_bins.sh
# Compares the bin contract of
# KernelMap.nullity_eq_alignedPairCount_of_binContract with the ideal kernel
# map of pathion_kernel_map in the gororoba-quantum checkout at
# $GOROROBA_QUANTUM: for every two-term operand e_i + t e_j of A_5 (i != j,
# t = +1 or -1; 1,984 operands, the six operands and two twins of the module
# among them), Python computes the ideal output contrast of
# kernel_map_circuit, and Lean evaluates KernelMap.binContract on the +1 bins
# with bin y read as index y, together with Tower.alignedPairCount and
# KernelMap.nullity; every operand must meet the contract with both equal to
# half the contrast sum. The contract must reject two mutated references:
# the kmap_flip3_e1pe18 member and the contrast of e_1 + e_18 with one bin
# negated. The gororoba_quantum directory of the checkout must be clean, and
# the script prints the commit, the sha256 of each module of that directory
# the cases import, and the numpy and qiskit versions. Runs on demand,
# outside ci/check.sh, because it reads another repository and needs its
# Python packages (numpy, qiskit, python-flint) under $PYTHON, and lake env
# lean reads the built library (lake build in lean/ first).
# Exit status: 0 agreement and both mutants rejected, 1 a difference or an
# accepted mutant, 2 a tool or the checkout is missing or the checkout's
# gororoba_quantum directory is modified. Writes only under a temporary
# directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
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

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT INT TERM

"$PYTHON" -B "$here/compare_kernel_map_bins.py" cases "$quantum" "$work/KernelMapBins.lean" "$work/python.json"
cd "$root/lean"
lake env lean --run "$work/KernelMapBins.lean" >"$work/lean.txt"
"$PYTHON" -B "$here/compare_kernel_map_bins.py" compare "$work/python.json" "$work/lean.txt"
echo "compare_kernel_map_bins: gororoba-quantum $(git -C "$quantum" rev-parse HEAD)"
for module in pathion_kernel_map cd_core select_lcu boolean_anf experiments; do
  echo "compare_kernel_map_bins: $module.py sha256 $(sha256sum "$quantum/gororoba_quantum/$module.py" | cut -d' ' -f1)"
done
"$PYTHON" -c 'import numpy, qiskit; print(f"compare_kernel_map_bins: numpy {numpy.__version__}, qiskit {qiskit.__version__}")'

