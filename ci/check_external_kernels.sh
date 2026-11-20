#!/bin/sh
# Usage: EXTERNAL_KERNELS_DIR=DIR sh ci/check_external_kernels.sh
# Checks every Lean row of ci/headline-results.tsv with an external kernel.
# For each solution module, lean4export writes its headline theorems together
# with every declaration they depend on, Mathlib and Lean core included, and
# nanoda (a type checker for Lean written independently in Rust) checks that
# file. Only propext, Classical.choice and Quot.sound are permitted, and any
# other axiom in the file is a hard error. Calibration comes first: nanoda must
# reject ReplayFixture.bogus of lean/ReplayFixture.lean (type False, added with
# the kernel switched off) and accept CayleyDickson.Tower.e_mul_e.
# nanoda accepts with status 0 and reports a rejection as a panic of its type
# checker (status 101, "panicked at src/tc.rs"); any other outcome is a tool
# error. Runs on demand, outside ci/check.sh. DIR holds the tools that
# ci/install_external_kernels.sh builds. The export of one module's closure
# ran to 3.2 million lines (HalfFold); the 34 modules took about 10 minutes
# on 12 checker threads (measured 2026-11-20, Lean 4.35.0).
# Needs git and lake (elan, with the toolchain of lean/lean-toolchain). Exit
# status: 0 every theorem accepted, 1 a theorem rejected, 2 calibration failed,
# a tool is missing or its version differs from lean/lean-toolchain. Writes
# only under a temporary directory it removes, besides Lake's build outputs.
set -eu

for tool in git lake; do
  command -v "$tool" >/dev/null || {
    echo "check_external_kernels: $tool is not on PATH" >&2
    exit 2
  }
done
root=$(git rev-parse --show-toplevel)
dir=${EXTERNAL_KERNELS_DIR:-}
export_bin=$dir/lean4export/.lake/build/bin/lean4export
nanoda_bin=$dir/nanoda_lib/target/release/nanoda_bin
for bin in "$export_bin" "$nanoda_bin"; do
  [ -n "$dir" ] && [ -x "$bin" ] || {
    echo "check_external_kernels: $bin is missing; run ci/install_external_kernels.sh" >&2
    exit 2
  }
done
toolchain=$(cat "$root/lean/lean-toolchain")
version=${toolchain#leanprover/lean4:v}

work=''
trap 'status=$?; [ -z "$work" ] || rm -r "$work" </dev/null || :; exit "$status"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
work=$(mktemp -d)

cd "$root/lean"
lake build GororobaMath ReplayFixture >"$work/build.log" 2>&1 || {
  echo "check_external_kernels: lake build failed (log follows)" >&2
  tail -20 "$work/build.log" >&2
  exit 2
}

# check MODULE THEOREM...: prints accepted, rejected or error; exit 0, 1 or 2.
check() {
  module=$1
  shift
  lake env "$export_bin" "$module" -- "$@" >"$work/export.ndjson" 2>"$work/export.err" || {
    echo error
    return 2
  }
  head -n 1 "$work/export.ndjson" | grep -q "\"version\":\"$version\"" || {
    echo error
    return 2
  }
  printf '{"export_file_path": "%s", "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"], "unpermitted_axiom_hard_error": true, "nat_extension": true, "string_extension": true, "num_threads": 8}\n' "$work/export.ndjson" >"$work/config.json"
  if "$nanoda_bin" "$work/config.json" >"$work/nanoda.log" 2>&1; then
    echo accepted
    return 0
  else
    rc=$?
  fi
  if [ "$rc" = 101 ] && grep -q 'panicked at src/tc.rs' "$work/nanoda.log"; then
    echo rejected
    return 1
  fi
  echo error
  return 2
}

verdict=$(check ReplayFixture ReplayFixture.bogus) || :
[ "$verdict" = rejected ] || {
  echo "check_external_kernels: calibration: ReplayFixture.bogus was $verdict, expected rejected" >&2
  cat "$work/nanoda.log" "$work/export.err" >&2 2>/dev/null || :
  exit 2
}
verdict=$(check GororobaMath.CayleyDickson.Tower CayleyDickson.Tower.e_mul_e) || :
[ "$verdict" = accepted ] || {
  echo "check_external_kernels: calibration: CayleyDickson.Tower.e_mul_e was $verdict, expected accepted" >&2
  cat "$work/nanoda.log" "$work/export.err" >&2 2>/dev/null || :
  exit 2
}

awk -F '\t' 'NR > 1 && $1 == "lean" { sub(/^lean\//, "", $2); sub(/\.lean$/, "", $2); gsub(/\//, ".", $2); print $2, $3 }' \
  "$root/ci/headline-results.tsv" | sort >"$work/rows.txt"
cut -d ' ' -f 1 "$work/rows.txt" | uniq >"$work/modules.txt"
failed=0
while IFS= read -r module; do
  theorems=$(awk -v m="$module" '$1 == m { print $2 }' "$work/rows.txt")
  # shellcheck disable=SC2086 # one argument per theorem name
  verdict=$(check "$module" $theorems) || :
  echo "check_external_kernels: $module ($(echo "$theorems" | wc -l) theorems): $verdict"
  case $verdict in
    accepted) ;;
    rejected) failed=1 ;;
    *) cat "$work/nanoda.log" "$work/export.err" >&2 2>/dev/null || :; exit 2 ;;
  esac
done <"$work/modules.txt"
[ "$failed" = 0 ] || exit 1
echo "check_external_kernels: every headline theorem accepted by nanoda"
