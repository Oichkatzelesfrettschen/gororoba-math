#!/bin/sh
# Usage: sh ci/compare_schreier.sh
# Compares Tower.schreier of lean/GororobaMath/CayleyDickson/SignCode.lean with
# schreier of rocq/open/theories/SchreierSignCode.v on every triple (l, r, x)
# of indices below 2^k for each order k from 1 to 5 (37448 triples,
# ci/compare_schreier.py): Lean evaluates them in a compiled program, Rocq with
# vm_compute after compiling the source, which imports only the standard
# library. The comparison must also reject a Rocq reference that swaps the first
# two arguments. Runs on demand, outside ci/check.sh, because it needs the Rocq
# switch of ci/install_rocq.sh beside the Lean toolchain.
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
    echo "compare_schreier: $tool is not on PATH" >&2
    exit 2
  }
done
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_schreier: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

cp "$root/rocq/open/theories/SchreierSignCode.v" "$work/SchreierSignCode.v"
"$PYTHON" -I "$here/compare_schreier.py" cases "$work/Schreier.lean" "$work/Table.v" "$work/TableMutant.v"
(
  cd "$work"
  opam exec --switch="$switch" -- rocq compile -q -Q . "" SchreierSignCode.v >"$work/compile.log" 2>&1
  opam exec --switch="$switch" -- rocq compile -q -Q . "" Table.v >"$work/rocq.txt"
  opam exec --switch="$switch" -- rocq compile -q -Q . "" TableMutant.v >"$work/mutant.txt"
)
cd "$root/lean"
lake build --no-build -q GororobaMath.CayleyDickson.SignCode || {
  echo "compare_schreier: build the Lean library first (lake build in lean/)" >&2
  exit 2
}
lake env lean --run "$work/Schreier.lean" >"$work/lean.txt"
status=0
"$PYTHON" -I "$here/compare_schreier.py" compare "$work/lean.txt" "$work/mutant.txt" >/dev/null 2>&1 || status=$?
[ "$status" -eq 1 ] || {
  echo "compare_schreier: the comparison did not reject the mutated reference (status $status)" >&2
  exit 1
}
echo "compare_schreier: the mutated reference is rejected"
"$PYTHON" -I "$here/compare_schreier.py" compare "$work/lean.txt" "$work/rocq.txt"
