#!/bin/sh
# Usage: sh ci/check_external_kernels.sh
# Checks every Lean row of ci/headline-results.tsv with the external checkers
# that the Lean toolchain of lean/lean-toolchain bundles (Lean 4.35.0 ships
# them in its bin directory). For each solution module, leanexport writes the
# module's headline theorems together with every declaration they depend on,
# Mathlib and Lean core included, and three checkers read that file:
#   - con-leche --verified, a checker written in Lean whose main theorem
#     states that a file declaring a theorem of type False is never accepted
#     in this mode (ConLeche.no_False_declaration);
#   - con-ron --verified, a Rust checker with the same statement proved about
#     its pipeline on an Aeneas model;
#   - nanoda_bin, a type checker for Lean written independently in Rust, with
#     propext, Classical.choice and Quot.sound as the only permitted axioms.
# The soundness statements above are those of each tool's --help text; con-ron
# states that its proofs still assume, as hypotheses, that the driver runs the
# extracted stages in the order it does on the file's bytes.
# ci/external_kernel_export.py first requires each requested theorem to be
# declared as a theorem in the export and the export to declare no axiom
# beyond those three, so the axiom rule does not rest on any one checker
# (con-leche and con-ron decline a non-standard axiom with status 2, and nanoda
# exits 1 under its hard-error rule; measured on AuditFixture.declaredAxiom).
# Calibration comes first: every checker must reject ReplayFixture.bogus of
# lean/ReplayFixture.lean (type False, added with the kernel switched off),
# and con-leche and con-ron must name it; the export check must refuse
# AuditFixture.usesDeclaredAxiom of lean/AuditFixture.lean; and every checker
# must accept CayleyDickson.Tower.e_mul_e.
# Runs on demand, outside ci/check.sh. The largest closure, that of
# CayleyDickson.HalfFold, ran to 3.2 million export lines (measured 2026-11-20,
# Lean 4.35.0, docs/archive/measurements/external-kernels.md).
# Needs git, lake (elan, with the toolchain of lean/lean-toolchain) and Python 3
# (PYTHON, default python3). Exit status: 0 every theorem accepted by every
# checker, 1 a checker rejected a theorem, 2 calibration failed, a tool is
# missing, an export does not match its request, or a checker failed to run.
# Writes only under a temporary directory it removes, besides Lake's build
# outputs.
set -eu

PYTHON=${PYTHON:-python3}
for tool in git lake "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "check_external_kernels: $tool is not on PATH" >&2
    exit 2
  }
done
root=$(git rev-parse --show-toplevel) || exit 2

work=''
trap 'status=$?; [ -z "$work" ] || rm -r "$work" </dev/null || :; exit "$status"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
work=$(mktemp -d) || exit 2

cd "$root/lean" || exit 2
prefix=$(lake env lean --print-prefix) || exit 2
bin=$prefix/bin
for tool in leanexport con-leche con-ron nanoda_bin; do
  [ -x "$bin/$tool" ] || {
    echo "check_external_kernels: $bin/$tool is missing; the toolchain of lean/lean-toolchain bundles no external checkers" >&2
    exit 2
  }
done
lake build GororobaMath ReplayFixture AuditFixture >"$work/build.log" 2>&1 || {
  echo "check_external_kernels: lake build failed (log follows)" >&2
  tail -20 "$work/build.log" >&2
  exit 2
}

# check MODULE THEOREM...: prints accepted, rejected or error, and returns
# 0, 1 or 2; the checkers' output stays in $work for the caller.
check() {
  module=$1
  shift
  lake env "$bin/leanexport" "$module" -- "$@" >"$work/export.ndjson" 2>"$work/export.err" || {
    echo error
    return 2
  }
  "$PYTHON" -I "$root/ci/external_kernel_export.py" "$work/export.ndjson" "$@" >"$work/export.txt" 2>>"$work/export.err" || {
    echo error
    return 2
  }
  printf '{"export_file_path": "%s", "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"], "unpermitted_axiom_hard_error": true, "nat_extension": true, "string_extension": true, "num_threads": 8}\n' "$work/export.ndjson" >"$work/nanoda.json" || {
    echo error
    return 2
  }
  rejected=0
  : >"$work/verdicts.txt"
  if "$bin/con-leche" --verified --jobs=8 "$work/export.ndjson" >"$work/con-leche.log" 2>&1; then
    echo "con-leche accept" >>"$work/verdicts.txt"
  elif grep -q '^con-leche: invalid: ' "$work/con-leche.log"; then
    rejected=1
    echo "con-leche reject" >>"$work/verdicts.txt"
  else
    echo error
    return 2
  fi
  if "$bin/con-ron" --verified --jobs=8 "$work/export.ndjson" >"$work/con-ron.log" 2>&1; then
    echo "con-ron accept" >>"$work/verdicts.txt"
  elif grep -q '^con-ron: rejected: ' "$work/con-ron.log"; then
    rejected=1
    echo "con-ron reject" >>"$work/verdicts.txt"
  else
    echo error
    return 2
  fi
  if "$bin/nanoda_bin" "$work/nanoda.json" >"$work/nanoda.log" 2>&1; then
    echo "nanoda accept" >>"$work/verdicts.txt"
  else
    rejected=1
    echo "nanoda reject" >>"$work/verdicts.txt"
  fi
  if [ "$rejected" = 1 ]; then
    echo rejected
    return 1
  fi
  echo accepted
}

show_logs() {
  for log in export.err con-leche.log con-ron.log nanoda.log; do
    [ -s "$work/$log" ] && { echo "--- $log" >&2; tail -5 "$work/$log" >&2; }
  done
  return 0
}

verdict=$(check ReplayFixture ReplayFixture.bogus) || :
named=$(grep -l 'ReplayFixture.bogus' "$work/con-leche.log" "$work/con-ron.log" | wc -l) || :
rejects=$(grep -c ' reject$' "$work/verdicts.txt") || :
if [ "$verdict" != rejected ] || [ "$rejects" != 3 ] || [ "$named" != 2 ]; then
  echo "check_external_kernels: calibration: ReplayFixture.bogus was $verdict ($(tr '\n' ' ' <"$work/verdicts.txt")), named by $named of con-leche and con-ron; expected rejected by all three and named by both" >&2
  show_logs
  exit 2
fi
verdict=$(check AuditFixture AuditFixture.usesDeclaredAxiom) || :
grep -q 'axioms outside the allow list: AuditFixture.declaredAxiom' "$work/export.err" || {
  echo "check_external_kernels: calibration: the export check did not refuse AuditFixture.declaredAxiom (verdict $verdict)" >&2
  show_logs
  exit 2
}
verdict=$(check GororobaMath.CayleyDickson.Tower CayleyDickson.Tower.e_mul_e) || :
accepts=$(grep -c ' accept$' "$work/verdicts.txt") || :
[ "$verdict" = accepted ] && [ "$accepts" = 3 ] || {
  echo "check_external_kernels: calibration: CayleyDickson.Tower.e_mul_e was $verdict ($(tr '\n' ' ' <"$work/verdicts.txt")), expected accepted by all three" >&2
  show_logs
  exit 2
}

awk -F '\t' 'NR > 1 && $1 == "lean" { sub(/^lean\//, "", $2); sub(/\.lean$/, "", $2); gsub(/\//, ".", $2); print $2, $3 }' \
  "$root/ci/headline-results.tsv" >"$work/rows.txt" || exit 2
sort -o "$work/rows.txt" "$work/rows.txt" || exit 2
rows=$(wc -l <"$work/rows.txt")
[ "$rows" -gt 0 ] || {
  echo "check_external_kernels: ci/headline-results.tsv lists no Lean row" >&2
  exit 2
}
cut -d ' ' -f 1 "$work/rows.txt" | uniq >"$work/modules.txt" || exit 2
failed=0
checked=0
while IFS= read -r module; do
  theorems=$(awk -v m="$module" '$1 == m { print $2 }' "$work/rows.txt")
  count=$(printf '%s\n' "$theorems" | wc -l)
  # shellcheck disable=SC2086 # one argument per theorem name
  verdict=$(check "$module" $theorems) || :
  echo "check_external_kernels: $module ($count theorems): $verdict; $(cat "$work/export.txt" 2>/dev/null)"
  case $verdict in
    accepted) checked=$((checked + count)) ;;
    rejected) failed=1; checked=$((checked + count)); cat "$work/verdicts.txt" >&2; show_logs ;;
    *) show_logs; exit 2 ;;
  esac
done <"$work/modules.txt"
[ "$checked" = "$rows" ] || {
  echo "check_external_kernels: checked $checked of $rows theorems" >&2
  exit 2
}
[ "$failed" = 0 ] || exit 1
echo "check_external_kernels: all $rows headline theorems accepted by con-leche, con-ron and nanoda"
