#!/bin/sh
# Usage: sh ci/check.sh
# The admission gate of gororoba-math. From any directory of the checkout:
#   1. every tracked shell script passes the lint at severity error;
#   2. lean/GororobaMath.lean imports every tracked module under
#      lean/GororobaMath/, so the build and the audit cover each one, and
#      the same check rejects a module the root file omits;
#   3. the Lean library and the audit command build with warnings as errors;
#   4. the axiom audit accepts the library (lean/audit/Library.lean);
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

# Prints each module of the list file $2 (one module name per line) that the
# root file $1 does not import, and returns 1 when it printed one.
missing_imports() {
  awk 'NR == FNR { if ($1 == "public" && $2 == "import") seen[$3] = 1; else if ($1 == "import") seen[$2] = 1; next }
       !($1 in seen) { print; missing = 1 }
       END { exit missing }' "$1" "$2"
}
git ls-files -- 'lean/GororobaMath/*.lean' |
  sed -e 's|^lean/||' -e 's|\.lean$||' -e 's|/|.|g' >"$work/modules.txt"
[ -s "$work/modules.txt" ] || {
  echo "check: git tracks no module under lean/GororobaMath" >&2
  exit 1
}
missing_imports lean/GororobaMath.lean "$work/modules.txt" >"$work/missing.txt" || {
  echo "check: lean/GororobaMath.lean does not import:" >&2
  cat "$work/missing.txt" >&2
  exit 1
}
{
  cat "$work/modules.txt"
  echo GororobaMath.OmittedModuleCalibration
} >"$work/modules-bad.txt"
if missing_imports lean/GororobaMath.lean "$work/modules-bad.txt" >"$work/missing-bad.txt"; then
  echo "check: the import check accepted a module the root file omits" >&2
  exit 1
fi
[ "$(cat "$work/missing-bad.txt")" = GororobaMath.OmittedModuleCalibration ] || {
  cat "$work/missing-bad.txt" >&2
  echo "check: the import check misreported its calibration module" >&2
  exit 1
}
echo "check: root file imports all $(wc -l <"$work/modules.txt") tracked module(s)"

cd "$root/lean"
lake build --wfail GororobaMath AxiomAudit
echo "check: library built with no warning"

lake env lean audit/Library.lean

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
