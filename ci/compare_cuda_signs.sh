#!/bin/sh
# Usage: CUDA_HOME=PATH CUDA_BUILD_DIR=PATH [CUDA_ARCH=sm_NN] sh ci/compare_cuda_signs.sh [LEVEL...]
# Compares the sign table that cuda/SignTable.lean computes on a CUDA device
# with the table of CayleyDickson.Tower.sign (printed by
# lean/audit/SignTable.lean) on every index pair of each LEVEL (default 3 4 5
# 6; level 5 is A_5, 1024 pairs). The Lean table is the reference. The device
# program also evaluates its own definition on the host and exits 3 when a
# device entry differs from it.
# CUDA_HOME names a CUDA 13 toolkit (bin/nvcc, lib64/libcudart.so),
# CUDA_BUILD_DIR a directory outside the checkout that receives the Lake tree
# of the cuda package, and CUDA_ARCH the device architecture (default sm_89;
# the pinned toolchain compiles its device runtime for sm_80 and sm_89 and
# fails for sm_75). Each LEVEL lies between 1 and 10, the range the device
# program accepts. A cmp of the first level's
# Lean table against the device table with its first entry negated must
# report a difference before any verdict counts.
# Runs on demand, outside ci/check.sh, because it needs an NVIDIA device and
# the toolchain that cuda/lean-toolchain names.
# Exit status: 0 every table identical, 1 a table differs or the comparison
# accepted the negated table, 2 a tool, the toolkit or a table producer is
# missing or fails, a LEVEL is out of range, or CUDA_BUILD_DIR resolves
# inside the checkout; a failing mkdir, mktemp or cp ends the script with
# that utility's status. Writes under CUDA_BUILD_DIR and a temporary
# directory it removes.
set -eu

for tool in git lake cmp awk mkdir mktemp cp cat tail dirname; do
  command -v "$tool" >/dev/null || {
    echo "compare_cuda_signs: $tool is not on PATH" >&2
    exit 2
  }
done
[ -n "${CUDA_HOME:-}" ] && [ -x "$CUDA_HOME/bin/nvcc" ] || {
  echo "compare_cuda_signs: set CUDA_HOME to a CUDA 13 toolkit holding bin/nvcc" >&2
  exit 2
}
[ -n "${CUDA_BUILD_DIR:-}" ] || {
  echo "compare_cuda_signs: set CUDA_BUILD_DIR to a directory outside the checkout" >&2
  exit 2
}
arch=${CUDA_ARCH:-sm_89}
[ "$#" -gt 0 ] || set -- 3 4 5 6
for level in "$@"; do
  case "$level" in
  *[!0-9]* | "")
    echo "compare_cuda_signs: level $level is not a natural number" >&2
    exit 2
    ;;
  esac
  # The reference table holds 4 ^ LEVEL entries, so the bound is read
  # before either producer runs.
  [ "${#level}" -le 2 ] && [ "$level" -ge 1 ] && [ "$level" -le 10 ] || {
    echo "compare_cuda_signs: level $level is outside 1 to 10" >&2
    exit 2
  }
done

# Both paths are compared in physical form, since a symbolic link outside the
# checkout can name a directory inside it. The nearest existing ancestor is
# read before mkdir, and the directory itself again after it.
root=$(CDPATH='' cd -- "$(git -C "$(dirname "$0")" rev-parse --show-toplevel)" && pwd -P)
inside() {
  case "$1/" in
  "$root"/*) return 0 ;;
  esac
  return 1
}
ancestor=$CUDA_BUILD_DIR
while [ ! -d "$ancestor" ]; do
  parent=$(dirname -- "$ancestor")
  [ "$parent" != "$ancestor" ] || break
  ancestor=$parent
done
if [ ! -d "$ancestor" ] || inside "$(CDPATH='' cd -- "$ancestor" && pwd -P)"; then
  echo "compare_cuda_signs: CUDA_BUILD_DIR resolves inside the checkout or under no directory" >&2
  exit 2
fi
mkdir -p -- "$CUDA_BUILD_DIR"
build=$(CDPATH='' cd -- "$CUDA_BUILD_DIR" && pwd -P)
if inside "$build"; then
  echo "compare_cuda_signs: CUDA_BUILD_DIR resolves inside the checkout" >&2
  exit 2
fi
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

# Under WSL the driver's libcuda loads libnvidia-ptxjitcompiler.so.1 by
# soname and its matching copy sits only in the driver store, so that
# directory goes first on the loader path when it exists.
for jit in /usr/lib/wsl/drivers/*/libnvidia-ptxjitcompiler.so.1; do
  if [ -e "$jit" ]; then
    LD_LIBRARY_PATH="$(dirname "$jit")${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"
    export LD_LIBRARY_PATH
    break
  fi
done

cp "$root/cuda/SignTable.lean" "$root/cuda/lakefile.lean" "$root/cuda/lean-toolchain" "$build/"
(
  cd "$build"
  PATH="$CUDA_HOME/bin:$PATH" lake build --wfail -Karch="$arch" -KcudaLib="$CUDA_HOME/lib64"
) >"$work/build.log" 2>&1 || {
  tail -n 30 "$work/build.log" >&2
  echo "compare_cuda_signs: the cuda package does not build for $arch" >&2
  exit 2
}

status=0
calibrated=0
for level in "$@"; do
  (cd "$root/lean" && lake env lean --run audit/SignTable.lean "$level") >"$work/lean.txt" || {
    echo "compare_cuda_signs: the Lean table of level $level was not produced" >&2
    exit 2
  }
  code=0
  "$build/.lake/build/bin/sign-table" "$level" >"$work/device.txt" 2>"$work/device.err" || code=$?
  if [ "$code" -ne 0 ] && [ "$code" -ne 3 ]; then
    cat "$work/device.err" >&2
    echo "compare_cuda_signs: the device table of level $level was not produced (status $code)" >&2
    exit 2
  fi
  if [ "$calibrated" -eq 0 ]; then
    awk 'NR == 1 { $1 = ($1 == "1" ? "-1" : "1") } { print }' "$work/device.txt" >"$work/mutated.txt"
    if cmp -s "$work/lean.txt" "$work/mutated.txt"; then
      echo "compare_cuda_signs: the comparison accepted a table with a negated first entry" >&2
      exit 1
    fi
    calibrated=1
  fi
  pairs=$(awk '{ n += NF } END { print n + 0 }' "$work/lean.txt")
  if [ "$code" -eq 0 ] && cmp -s "$work/lean.txt" "$work/device.txt"; then
    echo "compare_cuda_signs: level $level: $pairs signs identical on the device, on its host and in Tower.sign"
  else
    echo "compare_cuda_signs: level $level: the device table differs ($(cat "$work/device.err"))" >&2
    status=1
  fi
done
state=
[ -z "$(git -C "$root" status --porcelain -- cuda ci/compare_cuda_signs.sh lean)" ] || state=" with uncommitted changes"
echo "compare_cuda_signs: gororoba-math $(git -C "$root" rev-parse HEAD)$state, architecture $arch, toolchain $(cat "$root/cuda/lean-toolchain")"
exit "$status"
