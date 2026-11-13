#!/bin/sh
# Usage: sh ci/check.sh
# The Lean half of the admission gate of gororoba-math. From any directory of
# the checkout:
#   1. every tracked shell script passes the lint at severity error;
#   2. every tracked module under lean/GororobaMath/, taken from git's file
#      list, and the audit command build with warnings as errors;
#   3. the axiom audit accepts a generated file that imports each of those
#      modules, so the audit covers a module whatever lean/GororobaMath.lean
#      imports;
#   4. lean/GororobaMath.lean imports each of those modules, read from
#      Lean's own listing of the file's imports (lean --deps), and the same
#      check reports a module whose import sits inside a block comment;
#   5. the axiom audit rejects its known-bad inputs: lean/AuditFixture.lean,
#      naming sorryAx, the declared axiom and the native_decide axiom, and
#      a root that matches no module (lean/audit/UnknownRoot.lean).
# Needs git, shellcheck and lake (elan, with the toolchain of
# lean/lean-toolchain) on PATH. Exit status: 0 every check passed, 1 a check failed,
# 2 a tool is missing. Writes only under a temporary directory it removes.
set -eu

for tool in git lake shellcheck; do
  command -v "$tool" >/dev/null || {
    echo "check: $tool is not on PATH (README.md, Toolchain)" >&2
    exit 2
  }
done

root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work"' EXIT INT TERM

cd "$root"
git ls-files -- '*.sh' >"$work/scripts.txt"
[ -s "$work/scripts.txt" ] || {
  echo "check: git tracks no shell script; this script is one, so commit before the gate" >&2
  exit 1
}
while IFS= read -r script; do
  shellcheck -S error "$script"
done <"$work/scripts.txt"
echo "check: shellcheck passed on $(wc -l <"$work/scripts.txt") script(s)"

git ls-files -- ':(glob)lean/GororobaMath/**/*.lean' |
  sed -e 's|^lean/||' -e 's|\.lean$||' -e 's|/|.|g' | LC_ALL=C sort >"$work/modules.txt"
[ -s "$work/modules.txt" ] || {
  echo "check: git tracks no module under lean/GororobaMath" >&2
  exit 1
}

cd "$root/lean"
# shellcheck disable=SC2046 # one build target per module name
lake build --wfail $(cat "$work/modules.txt") GororobaMath AxiomAudit
echo "check: $(wc -l <"$work/modules.txt") tracked module(s) built with no warning"

{
  sed 's/^/import /' "$work/modules.txt"
  echo "import AxiomAudit"
  echo "#audit_axioms GororobaMath"
} >"$work/AllModules.lean"
lake env lean "$work/AllModules.lean"

# Prints each module of the sorted list file $2 that the Lean file $1 does
# not import, and fails when it printed one. Lean reads the import header,
# so a commented import counts as absent.
missing_imports() {
  lake env lean --deps "$1" |
    sed -n -e 's|^.*/lib/lean/\(GororobaMath/.*\)\.olean$|\1|p' | sed 's|/|.|g' | LC_ALL=C sort -u >"$work/imports.txt"
  LC_ALL=C comm -23 "$2" "$work/imports.txt" >"$work/missing.txt"
  [ ! -s "$work/missing.txt" ] || {
    cat "$work/missing.txt"
    return 1
  }
}
missing_imports GororobaMath.lean "$work/modules.txt" >"$work/missing-root.txt" || {
  echo "check: lean/GororobaMath.lean does not import:" >&2
  cat "$work/missing-root.txt" >&2
  exit 1
}
first=$(sed -n 1p "$work/modules.txt")
{
  echo "/-"
  echo "import $first"
  echo "-/"
  sed -e 1d -e 's/^/import /' "$work/modules.txt"
} >"$work/CommentedImport.lean"
if missing_imports "$work/CommentedImport.lean" "$work/modules.txt" >"$work/missing-commented.txt"; then
  echo "check: the import check accepted an import inside a block comment" >&2
  exit 1
fi
[ "$(cat "$work/missing-commented.txt")" = "$first" ] || {
  cat "$work/missing-commented.txt" >&2
  echo "check: the import check misreported its commented import of $first" >&2
  exit 1
}
echo "check: root file imports all tracked modules; a commented import is reported"

lake build AuditFixture >"$work/fixture-build.log" 2>&1 || {
  cat "$work/fixture-build.log" >&2
  echo "check: the audit fixture failed to build" >&2
  exit 1
}
if lake env lean audit/Fixture.lean >"$work/fixture.out" 2>&1; then
  cat "$work/fixture.out" >&2
  echo "check: the axiom audit accepted its known-bad fixture" >&2
  exit 1
fi
for axiom in sorryAx AuditFixture.declaredAxiom native_decide; do
  grep -q -F "$axiom" "$work/fixture.out" || {
    cat "$work/fixture.out" >&2
    echo "check: the axiom audit did not name $axiom in its fixture" >&2
    exit 1
  }
done
if lake env lean audit/UnknownRoot.lean >"$work/unknown.out" 2>&1; then
  cat "$work/unknown.out" >&2
  echo "check: the axiom audit accepted a root that matches no module" >&2
  exit 1
fi
echo "check: axiom audit rejected the fixture and the unknown root"
echo "check: passed"
