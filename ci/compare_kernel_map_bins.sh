#!/bin/sh
# Usage: GOROROBA_QUANTUM=PATH sh ci/compare_kernel_map_bins.sh
# Compares the bin contract of KernelMap.nullity_eq_alignedPairCount with
# the ideal kernel map of pathion_kernel_map in the gororoba-quantum
# checkout at $GOROROBA_QUANTUM: for the six operands and two twins of that
# module, Python computes the ideal output contrast of kernel_map_circuit,
# and Lean checks, with the +1 bins as pos and bin y read as index y, that
# every index of an aligned pair of Tower.misaligned is a +1 bin and every
# misaligned pair holds one bin of each sign, and that
# Tower.alignedPairCount, KernelMap.nullity and half the contrast sum agree.
# The comparator must reject two mutated references: the kmap_flip3_e1pe18
# member and the contrast of e_1 + e_18 with one bin negated. Prints one
# summary line, then the gororoba-quantum commit and the sha256 of
# pathion_kernel_map.py. Runs on demand, outside ci/check.sh, because it
# reads another repository and needs its Python packages (numpy, qiskit,
# python-flint) under $PYTHON, and lake env lean needs the built library.
# Exit status: 0 agreement and both mutants rejected, 1 a difference or an
# accepted mutant, 2 a tool or the checkout is missing. Writes only under a
# temporary directory it removes.
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

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT INT TERM

"$PYTHON" -B "$here/compare_kernel_map_bins.py" cases "$quantum" "$work/KernelMapBins.lean" "$work/python.json"
cd "$root/lean"
lake env lean --run "$work/KernelMapBins.lean" >"$work/lean.txt"
"$PYTHON" -B "$here/compare_kernel_map_bins.py" compare "$work/python.json" "$work/lean.txt"
echo "compare_kernel_map_bins: gororoba-quantum $(git -C "$quantum" rev-parse HEAD), pathion_kernel_map.py sha256 $(sha256sum "$quantum/gororoba_quantum/pathion_kernel_map.py" | cut -d' ' -f1)"
