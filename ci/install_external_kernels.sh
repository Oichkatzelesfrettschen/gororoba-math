#!/bin/sh
# Usage: EXTERNAL_KERNELS_DIR=DIR sh ci/install_external_kernels.sh
# Builds the external checkers of ci/check_external_kernels.sh in DIR, a
# directory outside the checkout: lean4export at the tag equal to the toolchain
# of lean/lean-toolchain (the export format the checker reads is tied to that
# Lean version), and nanoda_bin of nanoda_lib at the commit NANODA_COMMIT below,
# which reads lean4export's NDJSON format 3.1.0 (the release v0.3.2 expects an
# older export format and rejects its configuration keys, measured 2026-11-20).
# An existing DIR/lean4export or DIR/nanoda_lib is checked out again at the
# pinned revision and rebuilt.
# Needs git, lake (elan) and cargo on PATH. Exit status: 0 both tools built,
# 1 a build failed, 2 a tool is missing or DIR is unset or inside the checkout.
set -eu

NANODA_COMMIT=0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929
for tool in git lake cargo; do
  command -v "$tool" >/dev/null || {
    echo "install_external_kernels: $tool is not on PATH" >&2
    exit 2
  }
done
root=$(git rev-parse --show-toplevel)
dir=${EXTERNAL_KERNELS_DIR:-}
[ -n "$dir" ] || { echo "install_external_kernels: set EXTERNAL_KERNELS_DIR" >&2; exit 2; }
mkdir -p "$dir"
dir=$(cd "$dir" && pwd)
case "$dir/" in
  "$root"/*) echo "install_external_kernels: $dir lies inside the checkout" >&2; exit 2 ;;
esac
toolchain=$(cat "$root/lean/lean-toolchain")
tag=${toolchain#leanprover/lean4:}

[ -d "$dir/lean4export" ] || git clone -q https://github.com/leanprover/lean4export "$dir/lean4export"
git -C "$dir/lean4export" fetch -q --tags origin
git -C "$dir/lean4export" checkout -q "$tag"
(cd "$dir/lean4export" && lake build) || { echo "install_external_kernels: lean4export $tag failed to build" >&2; exit 1; }

[ -d "$dir/nanoda_lib" ] || git clone -q https://github.com/ammkrn/nanoda_lib "$dir/nanoda_lib"
git -C "$dir/nanoda_lib" fetch -q origin
git -C "$dir/nanoda_lib" checkout -q "$NANODA_COMMIT"
(cd "$dir/nanoda_lib" && cargo build --release -q) || { echo "install_external_kernels: nanoda failed to build" >&2; exit 1; }

echo "install_external_kernels: lean4export $tag and nanoda $NANODA_COMMIT built in $dir"
