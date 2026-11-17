#!/bin/sh
# Usage: sh ci/compare_aligned_pair_forms.sh
# Compares four Lean definitions with their Rocq partners on the same inputs
# (ci/compare_aligned_pair_forms.py names the tables and their ranges):
# Tower.alignedPairCountMultiplicity with AlignedPairSpectrum.multiplicity of
# rocq/quantum/CdTowerAlignedPairSpectrum.v; Tower.closedForm,
# Tower.clearedXorBit, Tower.DegenerateSplit and Tower.clearedXorParity with
# the closed_form, cleared_xor_bit, degenerate_split and cleared_xor_parity
# (at every t from 0 to k) of
# rocq/quantum/CdTowerAlignedPairClosedForm.v; Tower.associates with
# AssociatorSign.associates of rocq/quantum/CdTowerAssociatorSpace.v; and
# KernelMap.binContract with TwoTermBins.bin_contract of
# rocq/quantum/CdTowerTwoTermBins.v. Lean evaluates them in a program run by
# lake env lean --run, Rocq with vm_compute after compiling the closure of the
# Rocq sources from a copy of rocq/quantum of this checkout. The comparison
# first rejects a mutated Rocq reference on every table and only then
# compares and reports the agreement. Runs on demand,
# outside ci/check.sh, because it needs the Rocq switch of
# ci/install_rocq.sh beside the Lean toolchain with a built lean/.lake (the
# script runs lake build --no-build, which builds nothing).
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool or
# the switch is missing, a source does not compile or the Lean module is
# stale. On a stale Lean module, Lake writes a .nobuild trace beside the
# module's trace in lean/.lake before the script exits 2; otherwise the
# script writes only under a temporary directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
export PYTHON
for tool in git lake opam "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_aligned_pair_forms: $tool is not on PATH" >&2
    exit 2
  }
done
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_aligned_pair_forms: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
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
"$PYTHON" -I "$here/compare_aligned_pair_forms.py" cases "$work/Forms.lean" "$work/quantum/Forms.v" \
  "$work/quantum/FormsMutant.v"
(
  cd "$work/quantum"
  opam exec --switch="$switch" -- rocq dep -Q . "" ./*.v >"$work/dep.txt" 2>"$work/dep.log" || {
    echo "compare_aligned_pair_forms: rocq dep failed" >&2
    exit 2
  }
  "$PYTHON" -I "$here/compare_aligned_pair_count.py" closure Forms.v <"$work/dep.txt" >"$work/closure.txt" || exit 2
  grep -v -x -F Forms.v "$work/closure.txt" >"$work/sources.txt" || true
  echo "compare_aligned_pair_forms: compiling $(grep -c . "$work/sources.txt") sources"
  while IFS= read -r source; do
    opam exec --switch="$switch" -- rocq compile -q -Q . "" "$source" >>"$work/compile.log" 2>&1 || {
      echo "compare_aligned_pair_forms: $source does not compile" >&2
      exit 2
    }
  done <"$work/sources.txt"
  # The two evaluations run side by side.
  opam exec --switch="$switch" -- rocq compile -q -Q . "" Forms.v >"$work/rocq.txt" 2>&1 &
  forms=$!
  opam exec --switch="$switch" -- rocq compile -q -Q . "" FormsMutant.v >"$work/mutant.txt" 2>&1 &
  mutant=$!
  wait "$forms" || {
    echo "compare_aligned_pair_forms: the Rocq definitions do not evaluate:" >&2
    tail -n 20 "$work/rocq.txt" >&2
    exit 2
  }
  wait "$mutant" || {
    echo "compare_aligned_pair_forms: the mutated Rocq definitions do not evaluate:" >&2
    tail -n 20 "$work/mutant.txt" >&2
    exit 2
  }
)
cd "$root/lean"
lake build --no-build -q GororobaMath.CayleyDickson.AlignedPairSpectrum GororobaMath.CayleyDickson.AlignedPairClosedForm \
  GororobaMath.CayleyDickson.AssociatorSpace GororobaMath.KernelMap.TwoTermBins >&2 || {
  echo "compare_aligned_pair_forms: build the Lean library first (lake build in lean/)" >&2
  exit 2
}
lake env lean --run "$work/Forms.lean" >"$work/lean.txt" || {
  echo "compare_aligned_pair_forms: the Lean program failed" >&2
  exit 2
}
status=0
"$PYTHON" -I "$here/compare_aligned_pair_forms.py" reject "$work/lean.txt" "$work/mutant.txt" || status=$?
[ "$status" -eq 0 ] || {
  echo "compare_aligned_pair_forms: the comparison did not reject the mutated reference (status $status)" >&2
  exit 1
}
"$PYTHON" -I "$here/compare_aligned_pair_forms.py" compare "$work/lean.txt" "$work/rocq.txt"
