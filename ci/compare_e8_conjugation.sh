#!/bin/sh
# Usage: GOROROBA_QUANTUM=PATH sh ci/compare_e8_conjugation.sh
# Compares the generator lists of lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean (jm and jp) with the
# "ideal J=" lines of conjugation_map.sing of the gororoba-quantum checkout at $GOROROBA_QUANTUM: the generator
# ci/quantum-sources/e8_conjugation_ideal_lean.py renders the module again from that file (pinned by sha256, and
# equal to the lists of the retained v2 Rees scripts) and requires the tracked module to equal the rendering. The
# calibrations follow: a copy of the module with one changed digit must be rejected with status 1, and a scratch
# checkout whose conjugation_map.sing has one changed digit must be refused by its pinned sha256 (the same scratch
# checkout with the file unchanged is accepted first, as the control).
# Runs on demand, outside ci/check.sh, because it reads another repository.
# Exit status: 0 the module equals the rendering and both changed inputs are rejected, 1 a difference or an
# accepted copy (a difference of the module ends the run before the calibrations), 2 a tool or the checkout is missing.
# Writes only under a temporary directory it removes, also on INT and TERM.
set -eu

PYTHON=${PYTHON:-python3}
for tool in "$PYTHON" awk cmp ln cp mkdir; do
  command -v "$tool" >/dev/null || {
    echo "compare_e8_conjugation: $tool is not on PATH" >&2
    exit 2
  }
done
: "${GOROROBA_QUANTUM:?compare_e8_conjugation: set GOROROBA_QUANTUM to a gororoba-quantum checkout}"
export GOROROBA_QUANTUM
export PYTHONDONTWRITEBYTECODE=1
root=$(CDPATH='' cd -- "$(dirname "$0")/.." && pwd)
module=$root/lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean
generator=$root/ci/quantum-sources/e8_conjugation_ideal_lean.py
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

status=0
rc=0
"$PYTHON" -B -W error "$generator" --check >"$work/check.log" 2>&1 || rc=$?
cat "$work/check.log"
if [ "$rc" -eq 2 ]; then
  exit 2
elif [ "$rc" -ne 0 ]; then
  exit 1
fi

# The first coefficient 8 of generator 0 of J_N- becomes 9.
awk -v old='  8 * i * s8 + 8 * s2 * s7 + s4 ^ 2' -v new='  9 * i * s8 + 8 * s2 * s7 + s4 ^ 2' '
  !done && (p = index($0, old)) { $0 = substr($0, 1, p - 1) new substr($0, p + length(old)); done = 1 }
  { print }' "$module" >"$work/mutated.lean"
if cmp -s "$module" "$work/mutated.lean"; then
  echo "compare_e8_conjugation: the calibration copy equals the module" >&2
  exit 2
fi
rc=0
"$PYTHON" -B -W error "$generator" --check --source "$work/mutated.lean" >"$work/mutated.log" 2>&1 || rc=$?
if [ "$rc" -eq 1 ]; then
  echo "compare_e8_conjugation: the copy with one changed coefficient is rejected"
else
  echo "compare_e8_conjugation: the copy with one changed coefficient exited $rc, not 1" >&2
  status=1
fi

# A scratch checkout holds the files the generator reads: cd_core.py by link, the two retained v2 scripts by a linked
# directory, and conjugation_map.sing by copy, once unchanged (control) and once with its first digit of an "ideal J="
# line raised by one.
runs=docs/evidence/a5-exceptional-fibers/working/runs
conj=$runs/e8-rees-fibers-v3-open-cells/conjugation/conjugation_map.sing
for entry in "$GOROROBA_QUANTUM/$runs/e8-rees-fibers-v2-p32009" "$GOROROBA_QUANTUM/$conj" "$GOROROBA_QUANTUM/gororoba_quantum/cd_core.py"; do
  [ -e "$entry" ] || {
    echo "compare_e8_conjugation: $entry is missing" >&2
    exit 2
  }
done
for variant in control changed; do
  scratch=$work/q-$variant
  mkdir -p "$scratch/gororoba_quantum" "$scratch/$runs" "$scratch/$(dirname "$conj")"
  ln -s "$GOROROBA_QUANTUM/gororoba_quantum/cd_core.py" "$scratch/gororoba_quantum/cd_core.py"
  ln -s "$GOROROBA_QUANTUM/$runs/e8-rees-fibers-v2-p32009" "$scratch/$runs/e8-rees-fibers-v2-p32009"
  if [ "$variant" = control ]; then
    cp "$GOROROBA_QUANTUM/$conj" "$scratch/$conj"
  else
    awk '
      !done && /ideal J=/ && (p = match($0, /ideal J=[^0-9]*[0-9]/)) {
        d = substr($0, p + RLENGTH - 1, 1)
        $0 = substr($0, 1, p + RLENGTH - 2) ((d + 1) % 10) substr($0, p + RLENGTH)
        done = 1
      }
      { print }' "$GOROROBA_QUANTUM/$conj" >"$scratch/$conj"
    if cmp -s "$GOROROBA_QUANTUM/$conj" "$scratch/$conj"; then
      echo "compare_e8_conjugation: the changed sing copy equals the original" >&2
      exit 2
    fi
  fi
  rc=0
  GOROROBA_QUANTUM=$scratch "$PYTHON" -B -W error "$generator" --check >"$work/$variant.log" 2>&1 || rc=$?
  if [ "$variant" = control ]; then
    if [ "$rc" -ne 0 ]; then
      echo "compare_e8_conjugation: the unchanged scratch checkout exited $rc, not 0" >&2
      cat "$work/control.log" >&2
      exit 1
    fi
  elif [ "$rc" -eq 1 ] && grep -q 'has sha256' "$work/changed.log"; then
    echo "compare_e8_conjugation: the sing copy with one changed digit is refused by its pinned sha256"
  else
    echo "compare_e8_conjugation: the sing copy with one changed digit exited $rc without the digest refusal" >&2
    cat "$work/changed.log" >&2
    status=1
  fi
done
exit "$status"
