#!/bin/sh
# Usage: sh ci/compare_open_tree.sh
# Compares the open-tree spellings of two Cayley-Dickson functions with their Lean
# definitions on the same inputs (ci/compare_open_tree.py):
# Tower.anfCoeff, Tower.anfEval and Tower.anfDegree of
# lean/GororobaMath/CayleyDickson/BooleanAnf.lean against anf_evaluate (the canonical
# ANF, whose correctness and uniqueness are canonical_anf_correct and canonical_anf_unique)
# and anf_degree of rocq/open/theories/BooleanANFDegree.v, on every truth table of 0 to 3
# variables, a bent function and 64 xorshift tables of 4 variables and 32 of 5 variables;
# and Tower.assocPhase p q x of lean/GororobaMath/CayleyDickson/AssociatorPhase.lean against
# associator_phase of rocq/open/theories/CDAssociatorDoubling.v on every triple of indices
# below 2^k for each order k from 1 to 5 (37448 triples). Lean runs as a program under
# lake env lean --run; Rocq evaluates with vm_compute after compiling copies of
# SchreierSignCode.v, BooleanANFDegree.v and CDAssociatorDoubling.v of this checkout, which
# import only the standard library and each other, so no build tree of rocq/open is read.
# Before the verdict counts, the comparison must reject a Rocq coefficient transform whose
# upper half reads the lower half of the table, a Rocq degree one smaller than anf_degree and a
# Rocq reference with the last two arguments of the phase swapped. Runs on demand, outside
# ci/check.sh, because it needs the Rocq switch of ci/install_rocq.sh beside the Lean
# toolchain with a built lean/.lake (the script runs lake build --no-build, which builds
# nothing).
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool or the switch is
# missing, a source does not compile or the Lean module is stale. On a stale Lean module,
# Lake writes a .nobuild trace beside the module's trace in lean/.lake before the script
# exits 2; otherwise the script writes only under a temporary directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
export PYTHON
for tool in git lake opam "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_open_tree: $tool is not on PATH" >&2
    exit 2
  }
done
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_open_tree: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

for source in SchreierSignCode BooleanANFDegree CDAssociatorDoubling; do
  cp "$root/rocq/open/theories/$source.v" "$work/$source.v"
done
"$PYTHON" -I -B "$here/compare_open_tree.py" cases "$work/CompareOpenTree.lean" "$work" || exit 2
(
  cd "$work"
  for source in SchreierSignCode BooleanANFDegree CDAssociatorDoubling; do
    opam exec --switch="$switch" -- rocq compile -q -Q . OpenGororoba "$source.v" >>"$work/compile.log" 2>&1 || {
      echo "compare_open_tree: $source.v does not compile" >&2
      exit 2
    }
  done
  for name in Anf AnfMutant AnfDegreeMutant Assoc AssocMutant; do
    opam exec --switch="$switch" -- rocq compile -q -Q . OpenGororoba "CompareOpen$name.v" >"$work/$name.txt" 2>&1 || {
      echo "compare_open_tree: the Rocq evaluation CompareOpen$name fails:" >&2
      tail -n 20 "$work/$name.txt" >&2
      exit 2
    }
  done
)
cd "$root/lean"
lake build --no-build -q GororobaMath.CayleyDickson.BooleanAnf GororobaMath.CayleyDickson.AssociatorPhase >&2 || {
  echo "compare_open_tree: build the Lean library first (lake build in lean/)" >&2
  exit 2
}
lake env lean --run "$work/CompareOpenTree.lean" >"$work/lean.txt" || {
  echo "compare_open_tree: the Lean program failed" >&2
  exit 2
}
for pair in "anf AnfMutant" "anf AnfDegreeMutant" "assoc AssocMutant"; do
  # shellcheck disable=SC2086
  set -- $pair
  status=0
  "$PYTHON" -I -B "$here/compare_open_tree.py" compare "$1" "$work/lean.txt" "$work/$2.txt" >/dev/null 2>&1 ||
    status=$?
  [ "$status" -eq 1 ] || {
    echo "compare_open_tree: the comparison did not reject the Rocq reference $2 (status $status)" >&2
    exit 1
  }
done
echo "compare_open_tree: the mutated coefficient transform, the mutated degree and the swapped phase arguments are rejected"
"$PYTHON" -I -B "$here/compare_open_tree.py" compare anf "$work/lean.txt" "$work/Anf.txt" || exit $?
"$PYTHON" -I -B "$here/compare_open_tree.py" compare assoc "$work/lean.txt" "$work/Assoc.txt" || exit $?
