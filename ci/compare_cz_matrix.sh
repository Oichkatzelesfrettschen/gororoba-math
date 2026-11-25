#!/bin/sh
# Usage: GOROROBA_QUANTUM=PATH sh ci/compare_cz_matrix.sh
# Compares the entries of Tower.czMatrix of
# lean/GororobaMath/CayleyDickson/CzMatrix.lean with _c_matrix of
# docs/evidence/a5-kernel-attachments/holomorphic_kernel_lemma.py in the
# gororoba-quantum checkout at $GOROROBA_QUANTUM, on four integer vectors z at
# level 4 and four at level 5 drawn from a fixed seed (ci/compare_cz_matrix.py).
# Lean prints the entry formula of Tower.czMatrix_apply, since czMatrix is
# noncomputable; Python prints _c_matrix at level 4 and, at level 5, the same
# formula over cd_sign(32, ...) of cd_core.py, since _c_matrix is fixed at level
# 4. The comparison must also reject a reference whose cd_sign is negated at
# the index pair (3, 5). Runs on demand, outside ci/check.sh, because it reads
# another repository.
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool, the
# checkout or the Lean module is missing or stale. On a stale Lean module, Lake
# writes a .nobuild trace beside the module's trace in lean/.lake before the
# script exits 2; otherwise the script writes only under a temporary directory
# it removes.
set -eu

PYTHON=${PYTHON:-python3}
export PYTHON
for tool in git lake "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_cz_matrix: $tool is not on PATH" >&2
    exit 2
  }
done
[ -n "${GOROROBA_QUANTUM:-}" ] || {
  echo "compare_cz_matrix: set GOROROBA_QUANTUM to a gororoba-quantum checkout" >&2
  exit 2
}
quantum=$GOROROBA_QUANTUM
[ -f "$quantum/docs/evidence/a5-kernel-attachments/holomorphic_kernel_lemma.py" ] || {
  echo "compare_cz_matrix: $quantum holds no holomorphic_kernel_lemma.py" >&2
  exit 2
}
quantum=$(CDPATH='' cd -- "$quantum" && pwd)

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

"$PYTHON" -I "$here/compare_cz_matrix.py" cases "$work/Cz.lean"
cd "$root/lean"
lake build --no-build -q GororobaMath.CayleyDickson.CzMatrix || {
  echo "compare_cz_matrix: build the Lean library first (lake build in lean/)" >&2
  exit 2
}
lake env lean --run "$work/Cz.lean" >"$work/lean.txt"
"$PYTHON" -I "$here/compare_cz_matrix.py" reference "$quantum" "$work/reference.txt"
"$PYTHON" -I "$here/compare_cz_matrix.py" reference "$quantum" "$work/mutant.txt" mutate
"$PYTHON" -I "$here/compare_cz_matrix.py" compare "$work/lean.txt" "$work/reference.txt"
status=0
"$PYTHON" -I "$here/compare_cz_matrix.py" compare "$work/lean.txt" "$work/mutant.txt" >/dev/null 2>&1 || status=$?
[ "$status" -eq 1 ] || {
  echo "compare_cz_matrix: the comparison did not reject the mutated reference (status $status)" >&2
  exit 1
}
echo "compare_cz_matrix: the mutated reference is rejected"
echo "compare_cz_matrix: gororoba-quantum $(git -C "$quantum" rev-parse HEAD)"
