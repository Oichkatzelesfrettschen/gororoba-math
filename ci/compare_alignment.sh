#!/bin/sh
# Usage: ROCQ_BUILD_TREE=PATH sh ci/compare_alignment.sh
# Compares Tower.partner, Tower.alignedAdd and Tower.alignedSub of
# lean/GororobaMath/CayleyDickson/TwoTerm.lean with partner, aligned_add and
# aligned_sub of IntegerTwoTermBridge in rocq/quantum/CdTowerTwoTermBridge.v
# on every triple (i, j, x) with i, j and x below 2^k, for each level k from 0
# to 6 (299593 triples, ci/compare_alignment.py): Lean evaluates them in
# lean --run, Rocq with vm_compute against the objects of the build tree. The
# comparison must reject three mutated Rocq references (partner without its
# second operand, aligned_add without the negation of its first conjunct,
# aligned_sub with the argument order of one neg_sign call swapped) before
# the verdict counts. ROCQ_BUILD_TREE names the rocq directory of a build tree
# that make rocq compiled (BUILD_DIR/rocq, holding open/ and quantum/ with
# their .vo files); a tracked source of rocq/quantum, rocq/open/theories or
# rocq/open/verified that differs from its copy in the tree, or an object
# older than its source, is status 2. Runs on demand, outside ci/check.sh,
# because it needs the Rocq switch of ci/install_rocq.sh, a build tree and the
# Lean toolchain with a built lean/.lake (the script runs lake build --no-build
# and writes nothing there).
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool,
# the switch or the build tree is missing or stale, or a table producer
# fails. Writes only under a temporary directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
export PYTHON
switch=rocq-9.3
for tool in git lake opam "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_alignment: $tool is not on PATH" >&2
    exit 2
  }
done
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_alignment: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}
[ -n "${ROCQ_BUILD_TREE:-}" ] || {
  echo "compare_alignment: set ROCQ_BUILD_TREE to the rocq directory of a build tree that make rocq compiled" >&2
  exit 2
}
tree=$ROCQ_BUILD_TREE
[ -f "$tree/quantum/CdTowerTwoTermBridge.vo" ] || {
  echo "compare_alignment: $tree/quantum/CdTowerTwoTermBridge.vo does not exist; run make rocq first" >&2
  exit 2
}
tree=$(CDPATH='' cd -- "$tree" && pwd)

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

# The tables come from the objects of the build tree, so every tracked source
# of the three project-listed directories must equal its copy there and no
# object may be older than its source.
git -C "$root" ls-files -- 'rocq/quantum/*.v' 'rocq/open/theories/*.v' 'rocq/open/verified/*.v' >"$work/sources.txt"
while IFS= read -r source; do
  copy="$tree/${source#rocq/}"
  if ! cmp -s "$root/$source" "$copy" || [ ! -f "${copy%.v}.vo" ] || [ "${copy%.v}.vo" -ot "$copy" ]; then
    echo "compare_alignment: $copy differs from the tracked $source or has no current object; run make rocq again" >&2
    exit 2
  fi
done <"$work/sources.txt"

mkdir "$work/rocq"
"$PYTHON" -I "$here/compare_alignment.py" cases "$work/Alignment.lean" "$work/rocq/Alignment.v" \
  "$work/rocq/MutantPartner.v" "$work/rocq/MutantAdd.v" "$work/rocq/MutantSub.v"
for name in Alignment MutantPartner MutantAdd MutantSub; do
  (
    cd "$work/rocq"
    opam exec --switch="$switch" -- rocq compile -q -Q "$tree/quantum" "" \
      -R "$tree/open/verified" OpenGororobaVerified -Q "$tree/open/theories" OpenGororoba "$name.v"
  ) >"$work/$name.txt" 2>"$work/$name.err" || {
    cat "$work/$name.err" >&2
    echo "compare_alignment: $name.v does not compile against $tree" >&2
    exit 2
  }
done

cd "$root/lean"
lake build --no-build -q GororobaMath.CayleyDickson.TwoTerm >&2 || {
  echo "compare_alignment: build the Lean library first (lake build in lean/)" >&2
  exit 2
}
lake env lean --run "$work/Alignment.lean" >"$work/lean.txt" || {
  echo "compare_alignment: the Lean tables were not produced" >&2
  exit 2
}

for name in MutantPartner MutantAdd MutantSub; do
  status=0
  "$PYTHON" -I "$here/compare_alignment.py" compare "$work/lean.txt" "$work/$name.txt" >/dev/null 2>&1 || status=$?
  [ "$status" -eq 1 ] || {
    echo "compare_alignment: the comparison did not reject the mutated reference $name (status $status)" >&2
    exit 1
  }
done
echo "compare_alignment: the three mutated references are rejected"

status=0
"$PYTHON" -I "$here/compare_alignment.py" compare "$work/lean.txt" "$work/Alignment.txt" || status=$?
state=
[ -z "$(git -C "$root" status --porcelain -- rocq ci/compare_alignment.sh ci/compare_alignment.py lean)" ] || state=" with uncommitted changes"
echo "compare_alignment: gororoba-math $(git -C "$root" rev-parse HEAD)$state, every tracked Rocq source equal to the build tree"
exit "$status"
