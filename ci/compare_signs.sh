#!/bin/sh
# Usage: GOROROBA_QUANTUM=PATH sh ci/compare_signs.sh [LEVEL...]
# Compares the basis signs of the Lean tower (CayleyDickson.Tower.sign,
# printed by lean/audit/SignTable.lean) with gororoba_quantum/cd_core.py
# cd_sign of the gororoba-quantum checkout at $GOROROBA_QUANTUM, on every
# index pair of each LEVEL (default 3 4 5 6; level 5 is A_5, 1024 pairs).
# Prints one line per level with the pair count, then the gororoba-quantum
# commit and the sha256 of cd_core.py. Runs on demand, outside ci/check.sh,
# because it reads another repository.
# Exit status: 0 every table identical, 1 a table differs, 2 a tool or the
# checkout is missing. Writes only under a temporary directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
for tool in git lake cmp sha256sum "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_signs: $tool is not on PATH" >&2
    exit 2
  }
done
quantum=${GOROROBA_QUANTUM:?compare_signs: set GOROROBA_QUANTUM to a gororoba-quantum checkout}
core="$quantum/gororoba_quantum/cd_core.py"
[ -f "$core" ] || {
  echo "compare_signs: $core does not exist" >&2
  exit 2
}
[ "$#" -gt 0 ] || set -- 3 4 5 6

root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work"' EXIT INT TERM

cd "$root/lean"
status=0
for level in "$@"; do
  case "$level" in
  *[!0-9]* | "")
    echo "compare_signs: level $level is not a natural number" >&2
    exit 2
    ;;
  esac
  lake env lean --run audit/SignTable.lean "$level" >"$work/lean.txt"
  "$PYTHON" -I -B -c '
import sys
sys.path.insert(0, sys.argv[1])
from cd_core import cd_sign
size = 1 << int(sys.argv[2])
for p in range(size):
    print(" ".join(str(cd_sign(size, p, q)) for q in range(size)))
' "$quantum/gororoba_quantum" "$level" >"$work/python.txt"
  pairs=$(awk '{ n += NF } END { print n + 0 }' "$work/lean.txt")
  if cmp -s "$work/lean.txt" "$work/python.txt"; then
    echo "compare_signs: level $level: $pairs signs identical"
  else
    echo "compare_signs: level $level: tables differ" >&2
    status=1
  fi
done
echo "compare_signs: gororoba-quantum $(git -C "$quantum" rev-parse HEAD), cd_core.py sha256 $(sha256sum "$core" | cut -d' ' -f1)"
exit "$status"
