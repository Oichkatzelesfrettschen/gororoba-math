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
# must reject it with status 1. Prints one line per generator, then the
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

echo "check_quantum_sources: $count generators checked, $rejected perturbed copies rejected"
echo "check_quantum_sources: gororoba-quantum $(git -C "$quantum" rev-parse HEAD 2>/dev/null || echo unknown), cd_core.py sha256 $(sha256sum "$core" | cut -d' ' -f1)"
exit "$status"
