#!/bin/sh
# Usage: GOROROBA_QUANTUM=PATH ROCQ_BUILD_TREE=PATH sh ci/compare_signs.sh [LEVEL...]
# Compares four sign tables on every index pair of each LEVEL (default 3 4 5
# 6; level 5 is A_5, 1024 pairs): the Lean tower (CayleyDickson.Tower.sign,
# printed by lean/audit/SignTable.lean), gororoba_quantum/cd_core.py cd_sign
# of the gororoba-quantum checkout at $GOROROBA_QUANTUM, and the two Rocq
# sign functions that rocq/quantum/SignBridge.v proves equal,
# CdTowerBasisSign.sigma and open_cube_sign (printed by ci/audit/SignTable.v).
# The Lean table is the reference; each other table must equal it line by
# line. ROCQ_BUILD_TREE names the rocq directory of a build tree that
# `make rocq` compiled (BUILD_DIR/rocq, holding open/ and quantum/ with their
# .vo files); the script compiles one audit source against that tree and
# changes nothing in it; a tracked source of rocq/quantum, rocq/open/theories
# or rocq/open/verified that differs from its copy in the tree, or an object
# older than its source, is status 2. A cmp of the first level's Lean table against a
# copy of the first Rocq table with its first entry negated must report a
# difference before any verdict counts.
# Prints one line per level with the pair count and the tables compared,
# then the gororoba-quantum commit and the sha256 of cd_core.py. Runs on
# demand, outside ci/check.sh, because it reads another repository.
# Exit status: 0 every table identical, 1 a table differs, 2 a tool, the
# checkout, the build tree or its SignBridge.vo is missing or stale, a table
# producer fails, or the audit source does not compile. Writes only under a temporary directory it
# removes.
set -eu

PYTHON=${PYTHON:-python3}
switch=rocq-9.3
for tool in git lake cmp awk sha256sum opam "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_signs: $tool is not on PATH" >&2
    exit 2
  }
done
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_signs: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}
[ -n "${GOROROBA_QUANTUM:-}" ] || {
  echo "compare_signs: set GOROROBA_QUANTUM to a gororoba-quantum checkout" >&2
  exit 2
}
[ -n "${ROCQ_BUILD_TREE:-}" ] || {
  echo "compare_signs: set ROCQ_BUILD_TREE to the rocq directory of a build tree that make rocq compiled" >&2
  exit 2
}
quantum=$GOROROBA_QUANTUM
core="$quantum/gororoba_quantum/cd_core.py"
[ -f "$core" ] || {
  echo "compare_signs: $core does not exist" >&2
  exit 2
}
quantum=$(CDPATH='' cd -- "$quantum" && pwd)
core="$quantum/gororoba_quantum/cd_core.py"
tree=$ROCQ_BUILD_TREE
[ -f "$tree/quantum/SignBridge.vo" ] || {
  echo "compare_signs: $tree/quantum/SignBridge.vo does not exist; run make rocq first" >&2
  exit 2
}
tree=$(CDPATH='' cd -- "$tree" && pwd)
[ "$#" -gt 0 ] || set -- 3 4 5 6
for level in "$@"; do
  case "$level" in
  *[!0-9]* | "")
    echo "compare_signs: level $level is not a natural number" >&2
    exit 2
    ;;
  esac
done

root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

# The tables come from the objects of the build tree, so every tracked source of the three project-listed
# directories must equal its copy there and no object may be older than its source.
git -C "$root" ls-files -- 'rocq/quantum/*.v' 'rocq/open/theories/*.v' 'rocq/open/verified/*.v' >"$work/sources.txt"
while IFS= read -r source; do
  copy="$tree/${source#rocq/}"
  if ! cmp -s "$root/$source" "$copy" || [ ! -f "${copy%.v}.vo" ] || [ "${copy%.v}.vo" -ot "$copy" ]; then
    echo "compare_signs: $copy differs from the tracked $source or has no current object; run make rocq again" >&2
    exit 2
  fi
done <"$work/sources.txt"

# One compilation prints, in level order, the sigma table and then the
# open_cube_sign table of every level as Rocq string literals; awk cuts the
# literals into rocq-sigma-N.txt and rocq-open-N.txt, one row per line.
mkdir "$work/rocq"
{
  cat "$root/ci/audit/SignTable.v"
  for level in "$@"; do
    printf 'Eval vm_compute in sigma_text %s.\nEval vm_compute in open_text %s.\n' "$level" "$level"
  done
} >"$work/rocq/SignTable.v"
(
  cd "$work/rocq"
  opam exec --switch="$switch" -- rocq compile -q -Q "$tree/quantum" "" \
    -R "$tree/open/verified" OpenGororobaVerified -Q "$tree/open/theories" OpenGororoba SignTable.v
) >"$work/rocq.out" 2>"$work/rocq.err" || {
  cat "$work/rocq.err" >&2
  echo "compare_signs: ci/audit/SignTable.v does not compile against $tree" >&2
  exit 2
}
awk -v dir="$work" -v levels="$*" '
  BEGIN { n = split(levels, level, " "); block = 0; inside = 0 }
  !inside && /^ +=  *"/ { sub(/^ +=  *"/, ""); inside = 1; text = "" }
  inside && /^ +: string$/ {
    sub(/"$/, "", text)
    file = dir "/rocq-" (block % 2 == 0 ? "sigma" : "open") "-" level[int(block / 2) + 1] ".txt"
    print text > file
    close(file)
    block++
    inside = 0
    next
  }
  inside { text = (text == "" ? $0 : text "\n" $0) }
  END { if (block != 2 * n) { print "compare_signs: the Rocq output holds " block " tables, expected " 2 * n > "/dev/stderr"; exit 1 } }
' "$work/rocq.out" || exit 2

cd "$root/lean"
status=0
calibrated=0
for level in "$@"; do
  lake env lean --run audit/SignTable.lean "$level" >"$work/lean.txt" || {
    echo "compare_signs: the Lean table of level $level was not produced" >&2
    exit 2
  }
  "$PYTHON" -I -B -c '
import sys
sys.path.insert(0, sys.argv[1])
from cd_core import cd_sign
size = 1 << int(sys.argv[2])
for p in range(size):
    print(" ".join(str(cd_sign(size, p, q)) for q in range(size)))
' "$quantum/gororoba_quantum" "$level" >"$work/python.txt" || {
    echo "compare_signs: the Python table of level $level was not produced" >&2
    exit 2
  }
  pairs=$(awk '{ n += NF } END { print n + 0 }' "$work/lean.txt")
  if [ "$calibrated" -eq 0 ]; then
    awk 'NR == 1 { $1 = ($1 == "1" ? "-1" : "1") } { print }' "$work/rocq-sigma-$level.txt" >"$work/mutated.txt"
    if cmp -s "$work/lean.txt" "$work/mutated.txt"; then
      echo "compare_signs: the comparison accepted a table with a negated first entry" >&2
      exit 1
    fi
    calibrated=1
  fi
  same=1
  for other in "$work/python.txt" "$work/rocq-sigma-$level.txt" "$work/rocq-open-$level.txt"; do
    cmp -s "$work/lean.txt" "$other" || {
      echo "compare_signs: level $level: $(basename "$other" .txt) differs from the Lean table" >&2
      same=0
    }
  done
  if [ "$same" -eq 1 ]; then
    echo "compare_signs: level $level: $pairs signs identical in Lean, Python, Rocq sigma and Rocq open_cube_sign"
  else
    status=1
  fi
done
echo "compare_signs: gororoba-math $(git -C "$root" rev-parse HEAD), every tracked Rocq source equal to the build tree"
echo "compare_signs: gororoba-quantum $(git -C "$quantum" rev-parse HEAD), cd_core.py sha256 $(sha256sum "$core" | cut -d' ' -f1)"
exit "$status"
