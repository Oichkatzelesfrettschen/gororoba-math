#!/bin/sh
# Usage: GOROROBA_QUANTUM=PATH sh ci/compare_e8_conjugation.sh
# Compares the generator lists of lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean (jm and jp) with the
# "ideal J=" lines of conjugation_map.sing of the gororoba-quantum checkout at $GOROROBA_QUANTUM: the generator
# ci/quantum-sources/e8_conjugation_ideal_lean.py renders the module again from that file (pinned by sha256, and
# equal to the lists of the retained v2 Rees scripts) and requires the tracked module to equal the rendering. The
# calibration follows: a copy of the module with one changed digit must be rejected with status 1.
# Runs on demand, outside ci/check.sh, because it reads another repository.
# Exit status: 0 the module equals the rendering and the changed copy is rejected, 1 a difference or an accepted
# copy, 2 a tool or the checkout is missing.
# Writes only under a temporary directory it removes, also on INT and TERM.
set -eu

PYTHON=${PYTHON:-python3}
for tool in "$PYTHON" sed cmp; do
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
  status=1
fi

# The first coefficient 8 of generator 0 of J_N- becomes 9.
sed '0,/  8 \* i \* s8 + 8 \* s2 \* s7 + s4 \^ 2/s//  9 * i * s8 + 8 * s2 * s7 + s4 ^ 2/' "$module" >"$work/mutated.lean"
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
exit "$status"
