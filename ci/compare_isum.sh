#!/bin/sh
# Usage: PYTHON=PATH sh ci/compare_isum.sh
# Compares the imaginary sum e_1 + ... + e_(2^k - 1) in two implementations on the same
# inputs (ci/compare_isum.py): the coordinates of Tower.isum Int k of
# lean/GororobaMath/CayleyDickson/ImaginarySum.lean, and coord k (isum k) i of
# rocq/quantum/CdImaginarySumConference.v, at the levels 1 to 6, 126 coordinates. Lean
# runs as a program under lake env lean --run, and Rocq evaluates with vm_compute after
# compiling the closure of the Rocq source from a copy of rocq/quantum of this checkout. Before
# the verdict counts, the comparison must reject a copy of the Rocq Fixpoint isum that drops the
# term one j. The Rocq sources are in this repository, so the script reads no other checkout.
# Runs on demand, outside ci/check.sh, because it needs the Rocq switch of ci/install_rocq.sh
# beside the Lean toolchain with a built lean/.lake (the script runs lake build --no-build,
# which builds nothing).
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool or the switch is
# missing, a source does not compile or the Lean module is stale. On a stale Lean module, Lake
# writes a .nobuild trace beside the module's trace in lean/.lake before the script exits 2;
# otherwise the script writes only under a temporary directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
export PYTHON
for tool in git lake opam "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_isum: $tool is not on PATH" >&2
    exit 2
  }
done
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_isum: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

mkdir "$work/quantum"
git -C "$root" ls-files -z -- 'rocq/quantum/*.v' | (cd "$root" && xargs -0 cp -t "$work/quantum")
"$PYTHON" -I -B "$here/compare_isum.py" cases "$work/CompareIsum.lean" "$work/quantum/CompareIsum.v" \
  "$work/quantum/CompareIsumMutant.v" || exit 2
(
  cd "$work/quantum"
  opam exec --switch="$switch" -- rocq dep -Q . "" ./*.v >"$work/dep.txt" 2>"$work/dep.log" || {
    echo "compare_isum: rocq dep failed" >&2
    exit 2
  }
  "$PYTHON" -I "$here/compare_isum.py" closure CdTowerBasisSign.v <"$work/dep.txt" >"$work/closure.txt" || exit 2
  echo "compare_isum: compiling $(grep -c . "$work/closure.txt") sources"
  while IFS= read -r source; do
    opam exec --switch="$switch" -- rocq compile -q -Q . "" "$source" >>"$work/compile.log" 2>&1 || {
      echo "compare_isum: $source does not compile" >&2
      exit 2
    }
  done <"$work/closure.txt"
  opam exec --switch="$switch" -- rocq compile -q -Q . "" CompareIsum.v >"$work/rocq.txt" 2>&1 || {
    echo "compare_isum: the Rocq evaluation fails:" >&2
    tail -n 20 "$work/rocq.txt" >&2
    exit 2
  }
  opam exec --switch="$switch" -- rocq compile -q -Q . "" CompareIsumMutant.v >"$work/mutant.txt" 2>&1 || {
    echo "compare_isum: the mutated Rocq evaluation fails:" >&2
    tail -n 20 "$work/mutant.txt" >&2
    exit 2
  }
)
cd "$root/lean"
lake build --no-build -q GororobaMath.CayleyDickson.ImaginarySum >&2 || {
  echo "compare_isum: build the Lean library first (lake build in lean/)" >&2
  exit 2
}
lake env lean --run "$work/CompareIsum.lean" >"$work/lean.txt" || {
  echo "compare_isum: the Lean program failed" >&2
  exit 2
}
status=0
"$PYTHON" -I -B "$here/compare_isum.py" compare "$work/lean.txt" "$work/mutant.txt" >/dev/null 2>&1 ||
  status=$?
[ "$status" -eq 1 ] || {
  echo "compare_isum: the comparison did not reject the mutated Rocq reference (status $status)" >&2
  exit 1
}
echo "compare_isum: the Rocq reference without the term one j is rejected"
"$PYTHON" -I -B "$here/compare_isum.py" compare "$work/lean.txt" "$work/rocq.txt" || exit $?
