#!/bin/sh
# Usage: sh ci/compare_order_three.sh
# Compares Tower.orderThree of lean/GororobaMath/CayleyDickson/OrderThree.lean
# with OrderThreeMap.psi2 of rocq/quantum/CdTowerOrderThreeMap.v on the 16
# basis vectors of level 4 over Z[sqrt 3] (ci/compare_order_three.py, 512
# integers): Lean evaluates them in a compiled program over Zsqrtd 3 with the
# identity as star, Rocq with vm_compute after compiling the sources of
# rocq/quantum that the file requires. The comparison must also reject a Rocq
# reference whose coefficient 3 of the real part is 2. Runs on demand, outside
# ci/check.sh, because it needs the Rocq switch of ci/install_rocq.sh beside the
# Lean toolchain.
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool or
# the switch is missing or the Lean module is stale. On a stale Lean module,
# Lake writes a .nobuild trace beside the module's trace in lean/.lake before
# the script exits 2; otherwise the script writes only under a temporary
# directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
export PYTHON
for tool in git lake opam "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_order_three: $tool is not on PATH" >&2
    exit 2
  }
done
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_order_three: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

"$PYTHON" -I "$here/compare_order_three.py" closure "$root/rocq/quantum" >"$work/closure.txt"
while IFS= read -r name; do
  cp "$root/rocq/quantum/$name.v" "$work/$name.v"
done <"$work/closure.txt"
"$PYTHON" -I "$here/compare_order_three.py" cases "$work/OrderThree.lean" "$work/Psi.v" "$work/PsiMutant.v"
(
  cd "$work"
  while IFS= read -r name; do
    opam exec --switch="$switch" -- rocq compile -q -Q . "" "$name.v" >>"$work/compile.log" 2>&1
  done <"$work/closure.txt"
  opam exec --switch="$switch" -- rocq compile -q -Q . "" Psi.v >"$work/rocq.txt"
  opam exec --switch="$switch" -- rocq compile -q -Q . "" PsiMutant.v >"$work/mutant.txt"
)
cd "$root/lean"
lake build --no-build -q GororobaMath.CayleyDickson.OrderThree || {
  echo "compare_order_three: build the Lean library first (lake build in lean/)" >&2
  exit 2
}
lake env lean --run "$work/OrderThree.lean" >"$work/lean.txt"
"$PYTHON" -I "$here/compare_order_three.py" compare "$work/lean.txt" "$work/rocq.txt"
status=0
"$PYTHON" -I "$here/compare_order_three.py" compare "$work/lean.txt" "$work/mutant.txt" >/dev/null 2>&1 || status=$?
[ "$status" -eq 1 ] || {
  echo "compare_order_three: the comparison did not reject the mutated reference (status $status)" >&2
  exit 1
}
echo "compare_order_three: the mutated reference is rejected"
