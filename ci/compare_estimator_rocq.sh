#!/bin/sh
# Usage: sh ci/compare_estimator_rocq.sh
# Compares the Rocq definitions of the nullity estimator (Defs of
# rocq/quantum/KernelMapEstimator.v, instantiated with the QArith operations)
# with KernelMap.vHat, KernelMap.nHat, KernelMap.nullity, KernelMap.vBarPos and
# KernelMap.vBarNeg of lean/GororobaMath/KernelMap/Estimator.lean on the twelve
# fixed blocks of ci/compare_estimator_rocq.py, each with every bin decided
# and a bin-dependent rational contrast. Lean evaluates over the rationals in a
# compiled program, Rocq with vm_compute after compiling the source of this
# checkout; the readings agree exactly. The comparison must also reject a
# Rocq reference whose nHat divides by the unsigned mean of the contrast.
# Runs on demand, outside ci/check.sh, because it needs the Rocq switch of
# ci/install_rocq.sh beside the Lean toolchain.
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
    echo "compare_estimator_rocq: $tool is not on PATH" >&2
    exit 2
  }
done
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_estimator_rocq: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

"$PYTHON" -I "$here/compare_estimator_rocq.py" cases "$work/Estimator.lean" "$work/Bridge.v" "$work/BridgeMutant.v"
cp "$root/rocq/quantum/KernelMapEstimator.v" "$work/"
(
  cd "$work"
  opam exec --switch="$switch" -- rocq compile -q -Q . "" KernelMapEstimator.v >"$work/compile.log" 2>&1
  opam exec --switch="$switch" -- rocq compile -q -Q . "" Bridge.v >"$work/rocq.txt"
  opam exec --switch="$switch" -- rocq compile -q -Q . "" BridgeMutant.v >"$work/mutant.txt"
)
cd "$root/lean"
lake build --no-build -q GororobaMath.KernelMap.Estimator || {
  echo "compare_estimator_rocq: build the Lean library first (lake build in lean/)" >&2
  exit 2
}
lake env lean --run "$work/Estimator.lean" >"$work/lean.txt"
"$PYTHON" -I "$here/compare_estimator_rocq.py" compare "$work/lean.txt" "$work/rocq.txt" "$work/mutant.txt"
