#!/bin/sh
# Usage: GOROROBA_OPEN=PATH sh ci/check_delegation_sources.sh
# Renders Inventory512.v, Inventory1024.v and Inventory2048.v of
# rocq/delegation again from the statement inventories of the gororoba-open
# checkout at $GOROROBA_OPEN (curated/01_theory_frameworks/
# confine_theorems_N.v) and requires, for each N:
#   - the inventory has the sha256 recorded below (the bytes of
#     gororoba-open commit aa5166e0);
#   - the rendering equals the tracked source;
#   - the statements of the tracked source, with the proof lines removed,
#     are the bytes of the inventory, with one final newline added where
#     the inventory ends without one (all three do).
# Calibration: an inventory whose first statement concludes a different
# action than it assumes must be refused by the generator with status 1,
# and an inventory whose first statement names another action throughout
# must render to a file that differs from the tracked source.
# Runs on demand, outside the admission gate, because it reads another
# repository. Exit status: 0 every check passed, 1 a check failed, 2 a tool
# or the checkout is missing. Writes only under a temporary directory it
# removes, also on INT and TERM.
set -eu

PYTHON=${PYTHON:-python3}
for tool in git sha256sum cmp sed grep cut cp tail dirname mktemp "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "check_delegation_sources: $tool is not on PATH" >&2
    exit 2
  }
done
open=${GOROROBA_OPEN:?check_delegation_sources: set GOROROBA_OPEN to a gororoba-open checkout}
inventories="$open/curated/01_theory_frameworks"
[ -d "$inventories" ] || {
  echo "check_delegation_sources: $inventories does not exist" >&2
  exit 2
}
root=$(git -C "$(dirname "$0")" rev-parse --show-toplevel)
generator="$root/ci/delegation-sources/render_inventory.py"
work=$(mktemp -d "${TMPDIR:-/tmp}/gororoba-math-delegation.XXXXXXXX")
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

digest_of() {
  case $1 in
    512) echo 1f2692197664818ad58653d9b169dbc6f9e533c5ed1edaf4e6c06642bb567ff4 ;;
    1024) echo 1dc09c4c8ec99701dbb9bf232214a42be4250ada7f1e2f456cec0879b72bb1c5 ;;
    2048) echo f3d9266e59fde4b2d45e7d86a89db3dc31c10896e89ea4ae02c27e81f2c72b81 ;;
  esac
}

status=0
for size in 512 1024 2048; do
  inventory="$inventories/confine_theorems_$size.v"
  tracked="$root/rocq/delegation/Inventory$size.v"
  [ -f "$inventory" ] || {
    echo "check_delegation_sources: $inventory does not exist" >&2
    exit 2
  }
  found=$(sha256sum "$inventory" | cut -d ' ' -f 1)
  if [ "$found" != "$(digest_of "$size")" ]; then
    echo "check_delegation_sources: $inventory has sha256 $found, not the recorded $(digest_of "$size")" >&2
    status=1
    continue
  fi
  "$PYTHON" -B "$generator" "$inventory" "$size" >"$work/Inventory$size.v"
  if cmp -s "$work/Inventory$size.v" "$tracked"; then
    echo "check_delegation_sources: Inventory$size.v equals its rendering"
  else
    echo "check_delegation_sources: Inventory$size.v differs from its rendering" >&2
    status=1
  fi
  # The statements: the lines after "Import R D." and its blank line, up
  # to the blank line before the comment that opens the list stated,
  # without the proof lines.
  sed -n '/^Import R D\.$/,/^(\* A right together with a proof/p' "$tracked" |
    sed '1,2d; $d' | sed '$d' |
    grep -v -x -F 'Proof. exact (rd_direct _ _ _). Qed.' >"$work/statements-$size.v"
  cp "$inventory" "$work/inventory-$size.v"
  [ -z "$(tail -c 1 "$inventory")" ] || echo >>"$work/inventory-$size.v"
  if cmp -s "$work/statements-$size.v" "$work/inventory-$size.v"; then
    echo "check_delegation_sources: the statements of Inventory$size.v are confine_theorems_$size.v byte for byte ($(grep -c '^Theorem ' "$work/statements-$size.v") statements)"
  else
    echo "check_delegation_sources: the statements of Inventory$size.v differ from confine_theorems_$size.v" >&2
    status=1
  fi
done

# Calibration on the 512 inventory. Its first statement is on Send.
inventory="$inventories/confine_theorems_512.v"
sed '1s/Send\.$/Grant./' "$inventory" >"$work/two-rights.v"
if cmp -s "$inventory" "$work/two-rights.v"; then
  echo "check_delegation_sources: the calibration edit changed nothing" >&2
  exit 1
fi
refusal=0
"$PYTHON" -B "$generator" "$work/two-rights.v" 512 >/dev/null 2>"$work/refusal.txt" || refusal=$?
if [ "$refusal" -eq 1 ] && grep -q 'relates two different rights' "$work/refusal.txt"; then
  echo "check_delegation_sources: the generator refuses a statement that relates two rights"
else
  echo "check_delegation_sources: the generator did not refuse a statement that relates two rights (status $refusal)" >&2
  status=1
fi
sed '1s/Send/Receive/g' "$inventory" >"$work/other-action.v"
"$PYTHON" -B "$generator" "$work/other-action.v" 512 >"$work/other-action-rendered.v"
if cmp -s "$work/other-action-rendered.v" "$root/rocq/delegation/Inventory512.v"; then
  echo "check_delegation_sources: an inventory with a changed action rendered to the tracked source" >&2
  status=1
else
  echo "check_delegation_sources: an inventory with a changed action renders to a different source"
fi

[ "$status" -eq 0 ] || exit 1
echo "check_delegation_sources: passed against gororoba-open $(git -C "$open" rev-parse --short HEAD 2>/dev/null || echo "(no git checkout)")"
