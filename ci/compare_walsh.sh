#!/bin/sh
# Usage: GOROROBA_QUANTUM=PATH sh ci/compare_walsh.sh
# Compares KernelMap.walshChar and KernelMap.coeff of
# lean/GororobaMath/KernelMap/EstimatorWalsh.lean with walsh_matrix and
# coefficients of docs/evidence/pathion-kernel-map/nhat-bias/nhat_spectral.py
# in the gororoba-quantum checkout at $GOROROBA_QUANTUM: the 64 character
# values on 8 bins and the coefficients of four fixed contrasts, as exact
# fractions, with bit i of a bin index read as the coordinate i of
# Fin 3 -> Bool. The comparator must also reject a reference with one
# negated entry. Prints one summary line, then the gororoba-quantum commit
# and the sha256 of nhat_spectral.py. Runs on demand, outside ci/check.sh,
# because it reads another repository and needs numpy under $PYTHON.
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool
# or the checkout is missing. Writes only under a temporary directory it
# removes.
set -eu

PYTHON=${PYTHON:-python3}
for tool in git lake sha256sum "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_walsh: $tool is not on PATH" >&2
    exit 2
  }
done
quantum=${GOROROBA_QUANTUM:?compare_walsh: set GOROROBA_QUANTUM to a gororoba-quantum checkout}
source=docs/evidence/pathion-kernel-map/nhat-bias/nhat_spectral.py
[ -f "$quantum/$source" ] || {
  echo "compare_walsh: $quantum/$source does not exist" >&2
  exit 2
}
quantum=$(CDPATH='' cd -- "$quantum" && pwd)

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

"$PYTHON" -B "$here/compare_walsh.py" cases "$quantum" "$work/WalshCases.lean" "$work/python.json"
cd "$root/lean"
lake env lean --run "$work/WalshCases.lean" >"$work/lean.txt"
"$PYTHON" -B "$here/compare_walsh.py" compare "$work/python.json" "$work/lean.txt"
"$PYTHON" -B "$here/compare_walsh.py" mutate "$work/python.json" "$work/mutant.json"
if "$PYTHON" -B "$here/compare_walsh.py" compare "$work/mutant.json" "$work/lean.txt" >/dev/null 2>&1; then
  echo "compare_walsh: the comparison accepted a reference with one negated entry" >&2
  exit 1
fi
echo "compare_walsh: gororoba-quantum $(git -C "$quantum" rev-parse HEAD), nhat_spectral.py sha256 $(sha256sum "$quantum/$source" | cut -d' ' -f1)"
