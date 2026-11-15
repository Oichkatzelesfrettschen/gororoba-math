#!/bin/sh
# Usage: GOROROBA_QUANTUM=PATH sh ci/check_quantum_sources.sh
# Renders the eight generated sources of rocq/quantum again from the
# gororoba-quantum checkout at $GOROROBA_QUANTUM and requires each rendering
# to equal the tracked file. Seven generators in ci/quantum-sources/ render
# them (gaussian_certificates.py renders two); each runs with --check and
# reads gororoba_quantum/cd_core.py, parallel.py and the evidence records of
# that checkout (python-flint under $PYTHON). A --check writes nothing.
# Calibration follows: for each rendered source the generator is run once
# more against a scratch copy of rocq/quantum, made through
# QUANTUM_SOURCES_ROCQ, in which that source holds one changed digit, and
# must reject it with status 1. Four further calibrations follow. (1) Input
# side: a scratch quantum checkout (the gororoba_quantum package and docs/
# by links, cd_core.py by copy) must be accepted with status 0 by the four
# generators whose rendering depends on cd_core.py (cd_sign_rocq_ast,
# cd_sign_source_ast, stiefel_witness_certificate, kernel_certificates);
# the same checkout with `half >>= 2` for `half >>= 1` in cd_core.py must
# be rejected by each with status 1 and its own rejection message
# (cd_sign_source_ast rejects by raising its UnsupportedValue). (2) The
# stiefel_witness_certificate --package-cross-check output, an independent
# implementation (python-hypercomplex), must equal the retained
# docs/evidence/stiefel_witness/package_cross_check.json of the checkout;
# without hypercomplex under $PYTHON that check is reported as skipped and
# the status is unchanged. (3) Write containment: a write with
# QUANTUM_SOURCES_ROCQ, with --output (also behind an abbreviated write flag),
# with an unknown flag, into a linked
# source or into a linked rocq/quantum (run from a scratch copy of this
# directory) must exit 2 and change nothing, and a plain --write in a
# scratch copy with no link must exit 0 and restore a source with one
# changed digit to the tracked bytes. (4) make_mutants.py and
# make_span_mutants.py (the controls run_span_checks.sh compiles) must
# build their mutants from the tracked sources, and make_span_mutants.py must
# fail on a source that lacks its anchor. Prints one line per check, then the
# summary, the gororoba-quantum commit and the sha256 of cd_core.py.
# Runs on demand, outside ci/check.sh, because it reads another repository.
# Exit status: 0 every rendering equal and every perturbed copy rejected,
# 1 a difference or an accepted copy, 2 a tool, a Python module or the
# checkout is missing, or a generator refused its arguments.
# Writes only under a temporary directory it removes, also on INT and TERM.
set -eu

PYTHON=${PYTHON:-python3}
for tool in git sha256sum "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "check_quantum_sources: $tool is not on PATH" >&2
    exit 2
  }
done
"$PYTHON" -B -c 'import flint' 2>/dev/null || {
  echo "check_quantum_sources: $PYTHON cannot import flint (python-flint, the pin of gororoba-quantum requirements.txt)" >&2
  exit 2
}
quantum=${GOROROBA_QUANTUM:?check_quantum_sources: set GOROROBA_QUANTUM to a gororoba-quantum checkout}
core="$quantum/gororoba_quantum/cd_core.py"
[ -f "$core" ] || {
  echo "check_quantum_sources: $core does not exist" >&2
  exit 2
}
quantum=$(CDPATH='' cd -- "$quantum" && pwd)
export GOROROBA_QUANTUM=$quantum
export PYTHONDONTWRITEBYTECODE=1
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

# generator:source that it renders, one pair per rendered source
pairs='cd_sign_rocq_ast:CdSignPythonSemantics.v
cd_sign_source_ast:CdSignSourceCertificate.v
target_flip_certificate:TargetFlipN21.v
kernel_certificates:CdTowerCanonicalKernels.v
gaussian_certificates:CdTowerG2Derivations.v
gaussian_certificates:A5W8ArcMatrixRanks.v
render_span:CdTowerG2DerivationSpan.v
stiefel_witness_certificate:StiefelWitnessInvertible.v'

# Fails with status 2 when the log $1 shows a missing Python module or a refused argument (status $2 was 2).
tool_failure() {
  [ "$2" -eq 2 ] || grep -q -E 'ModuleNotFoundError|ImportError' "$1"
}

status=0
count=0
for generator in $(printf '%s\n' "$pairs" | cut -d: -f1 | sort -u); do
  count=$((count + 1))
  rc=0
  "$PYTHON" -B -W error "$root/ci/quantum-sources/$generator.py" --check >"$work/$generator.log" 2>&1 || rc=$?
  if [ "$rc" -eq 0 ]; then
    echo "check_quantum_sources: $generator: rendering equals the tracked source"
  else
    echo "check_quantum_sources: $generator: --check exited $rc" >&2
    tail -n 5 "$work/$generator.log" >&2
    if tool_failure "$work/$generator.log" "$rc"; then
      exit 2
    fi
    status=1
  fi
done

rejected=0
for pair in $pairs; do
  generator=${pair%%:*}
  source=${pair#*:}
  scratch="$work/scratch-$generator-$source"
  mkdir "$scratch"
  cp "$root"/rocq/quantum/*.v "$scratch/"
  "$PYTHON" -B "$root/ci/quantum-sources/perturb.py" "$root/rocq/quantum/$source" "$scratch/$source"
  cmp -s "$root/rocq/quantum/$source" "$scratch/$source" && {
    echo "check_quantum_sources: calibration copy of $source equals the original" >&2
    exit 1
  }
  rc=0
  QUANTUM_SOURCES_ROCQ=$scratch "$PYTHON" -B -W error "$root/ci/quantum-sources/$generator.py" --check \
    >"$work/$generator.bad.log" 2>&1 || rc=$?
  if [ "$rc" -eq 1 ] && ! tool_failure "$work/$generator.bad.log" 1; then
    rejected=$((rejected + 1))
  else
    echo "check_quantum_sources: $generator exited $rc on a copy of $source with a changed digit, not 1" >&2
    tail -n 5 "$work/$generator.bad.log" >&2
    if tool_failure "$work/$generator.bad.log" "$rc"; then
      exit 2
    fi
    status=1
  fi
done

# (1) Input-side calibration.
grep -q 'half >>= 1' "$core" || {
  echo "check_quantum_sources: $core holds no 'half >>= 1' to change" >&2
  exit 2
}
qin="$work/quantum-perturbed"
mkdir -p "$qin/gororoba_quantum"
for entry in "$quantum"/gororoba_quantum/*; do
  [ "$(basename "$entry")" = cd_core.py ] || ln -s "$entry" "$qin/gororoba_quantum/$(basename "$entry")"
done
ln -s "$quantum/docs" "$qin/docs"
# generator:text of its rejection of a changed cd_core.py
input_pairs='cd_sign_rocq_ast:regenerate cd_sign_ast
cd_sign_source_ast:UnsupportedValue: the loop shift of cd_sign
stiefel_witness_certificate:differs from a fresh render
kernel_certificates:L V = 0'
inputs_accepted=0
inputs_rejected=0
cp "$core" "$qin/gororoba_quantum/cd_core.py"
for changed in 0 1; do
  [ "$changed" -eq 0 ] || sed 's/half >>= 1/half >>= 2/' "$core" >"$qin/gororoba_quantum/cd_core.py"
  while IFS=: read -r generator message; do
    rc=0
    GOROROBA_QUANTUM=$qin "$PYTHON" -B -W error "$root/ci/quantum-sources/$generator.py" --check >"$work/$generator.in$changed.log" 2>&1 || rc=$?
    if [ "$changed" -eq 0 ] && [ "$rc" -eq 0 ]; then
      inputs_accepted=$((inputs_accepted + 1))
    elif [ "$changed" -eq 1 ] && [ "$rc" -eq 1 ] && grep -q -F "$message" "$work/$generator.in$changed.log" &&
      ! tool_failure "$work/$generator.in$changed.log" 1; then
      inputs_rejected=$((inputs_rejected + 1))
    else
      echo "check_quantum_sources: $generator exited $rc on the scratch checkout (cd_core.py changed: $changed), or without its rejection message" >&2
      tail -n 5 "$work/$generator.in$changed.log" >&2
      status=1
    fi
  done <<EOF_PAIRS
$input_pairs
EOF_PAIRS
done

# (2) Package cross-check against the retained record.
retained="$quantum/docs/evidence/stiefel_witness/package_cross_check.json"
if "$PYTHON" -B -c 'import hypercomplex' 2>/dev/null; then
  [ -f "$retained" ] || {
    echo "check_quantum_sources: $retained does not exist" >&2
    exit 2
  }
  rc=0
  "$PYTHON" -B -W error "$root/ci/quantum-sources/stiefel_witness_certificate.py" --package-cross-check \
    >"$work/cross-check.json" 2>"$work/cross-check.err" || rc=$?
  if [ "$rc" -eq 0 ] && cmp -s "$work/cross-check.json" "$retained"; then
    echo "check_quantum_sources: package cross-check equals the retained package_cross_check.json"
  else
    echo "check_quantum_sources: package cross-check exited $rc or differs from the retained record" >&2
    status=1
  fi
else
  echo "check_quantum_sources: skipped package cross-check: python package hypercomplex is not installed under $PYTHON"
fi

# (3) Write containment, from a scratch copy of this directory so that no tracked file is at risk.
st="$work/selftest"
mkdir -p "$st/ci/quantum-sources" "$st/rocq/quantum" "$work/elsewhere"
cp "$root"/ci/quantum-sources/*.py "$st/ci/quantum-sources/"
cp "$root"/rocq/quantum/*.v "$st/rocq/quantum/"
cp "$root/rocq/quantum/CdSignPythonSemantics.v" "$work/elsewhere/linked.v"
mv "$st/rocq/quantum/CdSignPythonSemantics.v" "$work/elsewhere/original.v"
ln -s "$work/elsewhere/linked.v" "$st/rocq/quantum/CdSignPythonSemantics.v"
st2="$work/selftest-dir"
mkdir -p "$st2/ci/quantum-sources" "$work/realdir"
cp "$root"/ci/quantum-sources/*.py "$st2/ci/quantum-sources/"
cp "$root"/rocq/quantum/*.v "$work/realdir/"
mkdir "$st2/rocq"
ln -s "$work/realdir" "$st2/rocq/quantum"
contained=0
refused() { # NAME DIRECTORY-OF-THE-COPY GENERATOR ARGUMENT...; the environment of the caller applies
  name=$1
  copy=$2
  generator=$3
  shift 3
  rc=0
  "$PYTHON" -B -W error "$copy/ci/quantum-sources/$generator.py" "$@" >"$work/refused.log" 2>&1 || rc=$?
  if [ "$rc" -eq 2 ]; then
    contained=$((contained + 1))
  else
    echo "check_quantum_sources: a write with $name exited $rc, not 2" >&2
    status=1
  fi
}
QUANTUM_SOURCES_ROCQ="$work/outside" refused "an override" "$st" cd_sign_rocq_ast --write
refused "--output" "$st" target_flip_certificate --write --output "$work/out/y.v"
refused "an unknown flag" "$st" cd_sign_rocq_ast --write --bogus
refused "an abbreviated write flag with --output" "$st" target_flip_certificate --writ --output "$work/out/y.v"
refused "a linked source" "$st" cd_sign_rocq_ast --write
refused "a linked rocq/quantum" "$st2" cd_sign_rocq_ast --write
QUANTUM_SOURCES_ROCQ="$work/missing" refused "an override that names no directory in a check" "$st" cd_sign_rocq_ast --check
if [ -e "$work/outside" ] || [ -e "$work/out" ] || ! cmp -s "$work/elsewhere/linked.v" "$work/elsewhere/original.v" ||
  ! cmp -s "$work/realdir/CdSignPythonSemantics.v" "$root/rocq/quantum/CdSignPythonSemantics.v"; then
  echo "check_quantum_sources: a refused write created or changed a file" >&2
  status=1
fi
# The guard admits the one write it is for: a scratch copy with no link, a source with one changed digit.
st3="$work/selftest-plain"
mkdir -p "$st3/ci/quantum-sources" "$st3/rocq/quantum"
cp "$root"/ci/quantum-sources/*.py "$st3/ci/quantum-sources/"
cp "$root"/rocq/quantum/*.v "$st3/rocq/quantum/"
"$PYTHON" -B "$root/ci/quantum-sources/perturb.py" "$root/rocq/quantum/CdSignPythonSemantics.v" "$st3/rocq/quantum/CdSignPythonSemantics.v"
admitted=0
rc=0
"$PYTHON" -B -W error "$st3/ci/quantum-sources/cd_sign_rocq_ast.py" --write >"$work/admitted.log" 2>&1 || rc=$?
if [ "$rc" -eq 0 ] && cmp -s "$st3/rocq/quantum/CdSignPythonSemantics.v" "$root/rocq/quantum/CdSignPythonSemantics.v"; then
  admitted=1
else
  echo "check_quantum_sources: a plain write in a scratch copy exited $rc or did not restore the tracked bytes" >&2
  tail -n 5 "$work/admitted.log" >&2
  status=1
fi

# (4) The mutation controls of the span and Gaussian certificates.
mutants_ok=0
"$PYTHON" -B "$root/ci/quantum-sources/make_mutants.py" "$root/rocq/quantum" "$work/mutants-a" >/dev/null 2>&1 && mutants_ok=$((mutants_ok + 1))
"$PYTHON" -B "$root/ci/quantum-sources/make_span_mutants.py" "$root/rocq/quantum/CdTowerG2DerivationSpan.v" "$work/mutants-b" >/dev/null 2>&1 && mutants_ok=$((mutants_ok + 1))
sed 's/Definition scalar : Z \* Z := (6, 0)\./Definition scalar : Z * Z := (7, 0)./' "$root/rocq/quantum/CdTowerG2DerivationSpan.v" >"$work/Span.v"
if "$PYTHON" -B "$root/ci/quantum-sources/make_span_mutants.py" "$work/Span.v" "$work/mutants-c" >/dev/null 2>&1; then
  echo "check_quantum_sources: make_span_mutants.py accepted a source without its anchor" >&2
  status=1
fi
[ "$mutants_ok" -eq 2 ] || {
  echo "check_quantum_sources: a mutant script failed on the tracked sources" >&2
  status=1
}

echo "check_quantum_sources: $count generators checked, $rejected perturbed copies rejected, $inputs_accepted scratch inputs accepted, $inputs_rejected perturbed inputs rejected, $contained refused writes, $admitted plain write admitted, $mutants_ok mutant scripts built"
echo "check_quantum_sources: gororoba-quantum $(git -C "$quantum" rev-parse HEAD 2>/dev/null || echo unknown), cd_core.py sha256 $(sha256sum "$core" | cut -d' ' -f1)"
exit "$status"
