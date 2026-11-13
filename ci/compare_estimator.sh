#!/bin/sh
# Usage: GOROROBA_QUANTUM=PATH sh ci/compare_estimator.sh
# Compares the Lean nullity estimator (KernelMap.vHat, KernelMap.nHat,
# KernelMap.nullity) with pathion_kernel_map._pair_summary of the
# gororoba-quantum checkout at $GOROROBA_QUANTUM on the twelve fixed blocks
# of ci/compare_estimator.py, each with every bin decided. Lean evaluates
# over the rationals on the exact values of the Python contrasts; the
# readings agree within 1e-12. The comparator must also reject a mutated
# reference. Prints one summary line, then the gororoba-quantum commit and
# the sha256 of pathion_kernel_map.py. Runs on demand, outside ci/check.sh,
# because it reads another repository and needs its Python packages (numpy,
# qiskit, python-flint) under $PYTHON.
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool
# or the checkout is missing. Writes only under a temporary directory it
# removes.
set -eu

PYTHON=${PYTHON:-python3}
for tool in git lake sha256sum "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_estimator: $tool is not on PATH" >&2
    exit 2
  }
done
quantum=${GOROROBA_QUANTUM:?compare_estimator: set GOROROBA_QUANTUM to a gororoba-quantum checkout}
[ -f "$quantum/gororoba_quantum/pathion_kernel_map.py" ] || {
  echo "compare_estimator: $quantum/gororoba_quantum/pathion_kernel_map.py does not exist" >&2
  exit 2
}
quantum=$(CDPATH='' cd -- "$quantum" && pwd)

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work"' EXIT INT TERM

"$PYTHON" -B "$here/compare_estimator.py" cases "$quantum" "$work/EstimatorBlocks.lean" "$work/python.json"
cd "$root/lean"
lake env lean --run "$work/EstimatorBlocks.lean" >"$work/lean.txt"
"$PYTHON" -B "$here/compare_estimator.py" compare "$work/python.json" "$work/lean.txt"
echo "compare_estimator: gororoba-quantum $(git -C "$quantum" rev-parse HEAD), pathion_kernel_map.py sha256 $(sha256sum "$quantum/gororoba_quantum/pathion_kernel_map.py" | cut -d' ' -f1)"
