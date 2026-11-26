#!/bin/sh
# Usage: AGDA_STDLIB=DIR [AGDA=PATH] [AGDA_BUILD_DIR=DIR] sh ci/check_agda.sh
# Type-checks the Agda library under agda/ (library gororoba-math, root
# module GororobaMath.CayleyDickson.OctonionMoufangLoop) with Agda 2.8.0.2
# and agda-stdlib v2.4, the checkout AGDA_STDLIB names, under -Werror and the
# --safe --without-K options each source sets. The check runs on a copy of
# agda/ in a temporary directory, so the interface files Agda writes beside a
# library stay outside the checkout. Before the verdict counts, the check must
# reject two planted copies: one whose root module claims that the octonion
# product associates, an identity whose difference normalizes to a nonzero
# integer polynomial, and one with a postulate, which --safe refuses.
# Runs on demand, outside ci/check.sh and ci/check_rocq.sh; on the
# workstation it runs under the heavy-job lease (measured times and memory:
# agda/README.md).
# Exit status: 0 the library checks and both planted copies fail, 1 the
# library fails or a planted copy is accepted, 2 a tool or the library is
# missing or has another version. Writes only under a temporary directory it
# removes, and the interface files of agda-stdlib under AGDA_STDLIB/_build.
set -eu

AGDA=${AGDA:-agda}
command -v "$AGDA" >/dev/null || {
  echo "check_agda: $AGDA is not on PATH" >&2
  exit 2
}
# A path with a slash resolves against the caller's directory before the
# script changes directory.
case $AGDA in
*/*) AGDA=$(CDPATH='' cd -- "$(dirname -- "$AGDA")" && pwd)/$(basename -- "$AGDA") ;;
esac
: "${AGDA_STDLIB:?check_agda: AGDA_STDLIB names a checkout of agda-stdlib v2.4}"
version=$("$AGDA" --version | sed -n 1p)
[ "$version" = "Agda version 2.8.0.2" ] || {
  echo "check_agda: need Agda version 2.8.0.2, found: $version" >&2
  exit 2
}
stdlib=$(CDPATH='' cd -- "$AGDA_STDLIB" && pwd)
grep -q -x -F 'name: standard-library-2.4' "$stdlib/standard-library.agda-lib" 2>/dev/null || {
  echo "check_agda: $stdlib holds no agda-stdlib v2.4 library file" >&2
  exit 2
}
[ -e "$stdlib/.git" ] || {
  echo "check_agda: $stdlib is not a git checkout of agda-stdlib v2.4" >&2
  exit 2
}
command -v git >/dev/null || {
  echo "check_agda: git is not on PATH to read the agda-stdlib commit" >&2
  exit 2
}
head=$(git -C "$stdlib" rev-parse HEAD)
[ "$head" = 2a5a0dec0a3cb5c87468ce101388a513d39dbf10 ] || {
  echo "check_agda: $stdlib is at $head, not the v2.4 commit 2a5a0dec0a3c" >&2
  exit 2
}
# The tracked sources must equal the commit; _build, which Agda writes, is
# untracked and outside this comparison.
git -C "$stdlib" diff --quiet HEAD -- || {
  echo "check_agda: $stdlib has tracked files that differ from 2a5a0dec0a3c" >&2
  exit 2
}

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(CDPATH='' cd -- "$here/.." && pwd)
work=
cleanup() {
  [ -z "$work" ] || rm -r "$work" </dev/null || :
}
trap cleanup EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
work=$(mktemp -d "${AGDA_BUILD_DIR:-${TMPDIR:-/tmp}}/gororoba-math-agda.XXXXXXXX")

main=src/GororobaMath/CayleyDickson/OctonionMoufangLoop.agda
doubling=src/GororobaMath/CayleyDickson/Doubling.agda

# copy_tree NAME: a copy of agda/ without interface files, at $work/NAME.
copy_tree() {
  cp -R "$root/agda" "$work/$1"
  [ ! -d "$work/$1/_build" ] || rm -r "$work/$1/_build" </dev/null
}

# check_tree NAME: type-checks the root module of the copy $work/NAME, with
# its output in $work/NAME.log.
check_tree() {
  printf '%s\n' "$stdlib/standard-library.agda-lib" "$work/$1/gororoba-math.agda-lib" \
    >"$work/$1.libraries"
  (cd "$work/$1" && "$AGDA" --library-file="$work/$1.libraries" -Werror "$main") \
    >"$work/$1.log" 2>&1
}

copy_tree pilot
if ! check_tree pilot; then
  cat "$work/pilot.log" >&2
  echo "check_agda: the library does not type-check" >&2
  exit 1
fi

# Planted copy 1: the root module ends with agda/planted/associativity.agda-fragment,
# a claim that the product associates, discharged like the true identities;
# the check must reject it at the claim's proof, the last line of the copy.
copy_tree assoc
cat "$work/assoc/planted/associativity.agda-fragment" >>"$work/assoc/$main"
line=$(wc -l <"$work/assoc/$main")
if check_tree assoc; then
  echo "check_agda: the copy that claims associativity type-checks" >&2
  exit 1
fi
# The rejection names the planted line and the empty type that the
# nonzero normal form of a coordinate reduces Zero (norm ...) to.
if ! grep -q -F "OctonionMoufangLoop.agda:$line." "$work/assoc.log" ||
  ! grep -q -F '[UnequalTerms]' "$work/assoc.log" ||
  ! grep -q -F 'Data.Irrelevant.Irrelevant Data.Empty.Empty' "$work/assoc.log" ||
  ! grep -q -F 'Zero (norm' "$work/assoc.log"; then
  cat "$work/assoc.log" >&2
  echo "check_agda: the associativity copy failed off its normal form, line $line" >&2
  exit 1
fi

# Planted copy 2: a postulate, which --safe refuses.
copy_tree postulate
printf '%s\n' '' 'postulate planted : {A : Set} -> A' >>"$work/postulate/$doubling"
if check_tree postulate; then
  echo "check_agda: the copy with a postulate type-checks" >&2
  exit 1
fi
pline=$(wc -l <"$work/postulate/$doubling")
if ! grep -q -F "Doubling.agda:$pline." "$work/postulate.log" ||
  ! grep -q -F '[SafeFlagPostulate]' "$work/postulate.log"; then
  cat "$work/postulate.log" >&2
  echo "check_agda: the copy with a postulate failed for another reason" >&2
  exit 1
fi

echo "check_agda: the library type-checks; both planted copies fail"
