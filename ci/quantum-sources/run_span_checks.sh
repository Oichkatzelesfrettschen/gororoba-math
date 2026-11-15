#!/bin/sh
# Usage: sh run_span_checks.sh BUILD_DIRECTORY
# Compiles the three span sources in BUILD_DIRECTORY (which holds the compiled sources they import), then runs
# the assumption queries, the kernel checker and the mutants. Writes span-checks-record.txt there: tool and
# source identity, each command with its time, and one verdict line. Exit status: 0 every expectation held,
# 1 an expectation failed, 2 a tool or input is missing.
set -eu
B=${1:?build directory}
R="$HOME/.opam/rocq-9.3/bin/rocq"
PYTHON=${PYTHON:-python3}
export PYTHON
[ -x "$R" ] || { echo "run_span_checks: no rocq at the rocq-9.3 switch" >&2; exit 2; }
cd "$B"
B=$(pwd)
rec=span-checks-record.txt
fail() { echo "verdict: FAIL $*" >> "$rec"; echo "run_span_checks: $*" >&2; exit 1; }
{
  echo "rocq: $("$R" --version | head -1)"
  echo "machine: $(nproc) threads, $(uname -m)"
  sha256sum MatrixSplittingCertificate.v CdTowerLeibnizSystem.v CdTowerG2DerivationSpan.v SpanQueries.v \
    make_span_mutants.py
} > "$rec"
for f in MatrixSplittingCertificate CdTowerLeibnizSystem CdTowerG2DerivationSpan; do
  /usr/bin/time -f "compile $f.v: %es %MKB" -o time.tmp "$R" compile -q -w @all -Q . "" "$f.v" > "compile-$f.log" 2>&1 \
    || fail "$f.v does not compile"
  cat time.tmp >> "$rec"
  [ -s "compile-$f.log" ] && fail "$f.v compiles with output"
  echo "compile $f.v: empty output" >> "$rec"
done
"$R" compile -q -w @all -Q . "" SpanQueries.v > span-queries-output.txt 2>&1 || fail "the queries do not compile"
closed=$(grep -c '^Closed under the global context$' span-queries-output.txt || true)
asked=$(grep -c '^Print Assumptions' SpanQueries.v)
echo "queries: $closed closed of $asked asked" >> "$rec"
[ "$closed" -eq "$asked" ] && [ "$asked" -gt 0 ] || fail "an assumption query is not closed"
grep -q 'Axioms:' span-queries-output.txt && fail "a query lists an axiom"
/usr/bin/time -f "kernel check: %es %MKB" -o time.tmp "$R" check -silent -o -Q . "" \
  MatrixSplittingCertificate CdTowerLeibnizSystem CdTowerG2DerivationSpan > span-kernel-check-output.txt 2>&1 \
  || fail "the kernel checker rejects a module"
cat time.tmp >> "$rec"
grep -q '^\* Axioms: <none>$' span-kernel-check-output.txt || fail "the kernel checker reports an axiom"
echo "kernel check: Axioms: <none>" >> "$rec"
mutants=$(mktemp -d "$PWD/mutants-span.XXXXXX")
trap 'rm -r "$mutants"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
"$PYTHON" make_span_mutants.py CdTowerG2DerivationSpan.v "$mutants"
# The mutant compiles are independent: each runs as its own job in its own directory and leaves its exit
# status in status.txt; the loop below reads the statuses after every job has ended.
for d in "$mutants"/*/; do
  (
    cd "$d"
    status=0
    "$R" compile -q -w @all -Q "$B" "" -Q . "" CdTowerG2DerivationSpan.v > compile.log 2>&1 || status=$?
    echo "$status" > status.txt
  ) &
done
wait
count=0
for d in "$mutants"/*/; do
  n=$(basename "$d")
  [ -s "$d/status.txt" ] || fail "mutant $n left no exit status"
  status=$(cat "$d/status.txt")
  line=$(grep -m1 -oE 'line [0-9]+' "$d/compile.log" | grep -oE '[0-9]+' || true)
  lemma=$(awk -v L="${line:-0}" 'NR<=L && /^(Lemma|Theorem) /{name=$2} END{print name}' "$d/CdTowerG2DerivationSpan.v")
  expected=$(cat "$d/expected-lemma.txt")
  echo "mutant $n: exit $status, rejected in ${lemma:-none}, expected $expected" >> "$rec"
  [ "$status" -ne 0 ] || fail "mutant $n compiles"
  [ "$lemma" = "$expected" ] || fail "mutant $n is rejected in ${lemma:-none}, not $expected"
  count=$((count + 1))
done
[ "$count" -eq 6 ] || fail "expected 6 mutants, ran $count"
rm -f time.tmp
echo "verdict: PASS" >> "$rec"
