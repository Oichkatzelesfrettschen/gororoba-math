#!/bin/sh
# Usage: GOROROBA_QUANTUM=PATH sh ci/check_quantum_sources.sh
# Renders the seven generated sources of rocq/quantum again from the
# gororoba-quantum checkout at $GOROROBA_QUANTUM and requires each rendering
# to equal the tracked file. The generators live in ci/quantum-sources/;
# each runs with --check and reads gororoba_quantum/cd_core.py, parallel.py
# and the evidence records of that checkout (python-flint and qiskit under
# $PYTHON). Calibration follows: every generator is run once more against a
# scratch copy of rocq/quantum whose source it renders holds one changed
# digit, and must reject it with status 1. Prints one line per generator,
# then the summary, the gororoba-quantum commit and the sha256 of cd_core.py.
# Runs on demand, outside ci/check.sh, because it reads another repository.
# Exit status: 0 every rendering equal and every perturbed copy rejected,
# 1 a difference or an accepted copy, 2 a tool or the checkout is missing.
# Writes only under a temporary directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
for tool in git sha256sum "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "check_quantum_sources: $tool is not on PATH" >&2
    exit 2
  }
done
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
trap 'rm -r "$work"' EXIT INT TERM

# generator:source that the generator renders (the first of its sources)
pairs='cd_sign_rocq_ast:CdSignPythonSemantics.v
cd_sign_source_ast:CdSignSourceCertificate.v
target_flip_certificate:TargetFlipN21.v
kernel_certificates:CdTowerCanonicalKernels.v
gaussian_certificates:CdTowerG2Derivations.v
render_span:CdTowerG2DerivationSpan.v
stiefel_witness_certificate:StiefelWitnessInvertible.v'

status=0
count=0
for pair in $pairs; do
  generator=${pair%%:*}
  count=$((count + 1))
  if "$PYTHON" -B -W error "$root/ci/quantum-sources/$generator.py" --check >"$work/$generator.log" 2>&1; then
    echo "check_quantum_sources: $generator: rendering equals the tracked source"
  else
    rc=$?
    echo "check_quantum_sources: $generator: --check exited $rc" >&2
    tail -n 5 "$work/$generator.log" >&2
    status=1
  fi
done

rejected=0
for pair in $pairs; do
  generator=${pair%%:*}
  source=${pair#*:}
  scratch="$work/scratch-$generator"
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
  if [ "$rc" -eq 1 ]; then
    rejected=$((rejected + 1))
  else
    echo "check_quantum_sources: $generator exited $rc on a copy of $source with a changed digit, not 1" >&2
    tail -n 5 "$work/$generator.bad.log" >&2
    status=1
  fi
done

echo "check_quantum_sources: $count generators checked, $rejected perturbed copies rejected"
echo "check_quantum_sources: gororoba-quantum $(git -C "$quantum" rev-parse HEAD 2>/dev/null || echo unknown), cd_core.py sha256 $(sha256sum "$core" | cut -d' ' -f1)"
exit "$status"
