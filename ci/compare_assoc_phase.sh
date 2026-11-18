#!/bin/sh
# Usage: PYTHON=PATH GOROROBA_QUANTUM=PATH sh ci/compare_assoc_phase.sh
# Compares the associator phase of three basis units in three implementations on
# the same inputs (ci/compare_assoc_phase.py): Tower.assocPhase p q x of
# lean/GororobaMath/CayleyDickson/AssociatorPhase.lean, assoc k p q x of
# rocq/quantum/CdAssociatorAnf.v, and associator_phase(2^k, p, q)[x] of
# gororoba_quantum/predict.py in the gororoba-quantum checkout at
# $GOROROBA_QUANTUM, on every triple p, q, x below 2^k at the levels 1 to 5,
# 37448 values; Lean and Rocq read true as the sign -1 and Python reads -1.
# Lean runs as a program under lake env lean --run, and Rocq evaluates with
# vm_compute after compiling the closure of the Rocq source from a copy of
# rocq/quantum of this checkout. predict.py imports numpy, so PYTHON names an
# interpreter that has it; the script exits 2 with a message when the import
# fails. The open-tree spelling associator_phase of
# rocq/open/theories/CDAssociatorDoubling.v is outside the comparison, since its
# cube carrier needs the compiled open tree. Before the verdict counts, the
# comparison must reject a Rocq reference with its last two arguments swapped
# (assoc k p x q) and a Python reference with one sign negated. Prints the
# gororoba-quantum commit and the sha256 of the Python files read. Runs on
# demand, outside ci/check.sh, because it reads another repository and needs the
# Rocq switch of ci/install_rocq.sh beside the Lean toolchain with a built
# lean/.lake (the script runs lake build --no-build, which builds nothing).
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool, the
# switch or the checkout is missing, numpy does not import, a source does not
# compile or the Lean module is stale. On a stale Lean module, Lake writes a
# .nobuild trace beside the module's trace in lean/.lake before the script exits
# 2; otherwise the script writes only under a temporary directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
export PYTHON
for tool in git lake opam "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_assoc_phase: $tool is not on PATH" >&2
    exit 2
  }
done
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_assoc_phase: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}
[ -n "${GOROROBA_QUANTUM:-}" ] || {
  echo "compare_assoc_phase: set GOROROBA_QUANTUM to a gororoba-quantum checkout" >&2
  exit 2
}
[ -f "$GOROROBA_QUANTUM/gororoba_quantum/predict.py" ] || {
  echo "compare_assoc_phase: $GOROROBA_QUANTUM/gororoba_quantum/predict.py does not exist" >&2
  exit 2
}
quantum=$(CDPATH='' cd -- "$GOROROBA_QUANTUM" && pwd)

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

"$PYTHON" -I -B "$here/compare_assoc_phase.py" import "$quantum" || exit 2
mkdir "$work/quantum"
git -C "$root" ls-files -z -- 'rocq/quantum/*.v' | (cd "$root" && xargs -0 cp -t "$work/quantum")
"$PYTHON" -I -B "$here/compare_assoc_phase.py" cases "$work/CompareAssocPhase.lean" "$work/quantum/CompareAssocPhase.v" \
  "$work/quantum/CompareAssocPhaseMutant.v" || exit 2
(
  cd "$work/quantum"
  opam exec --switch="$switch" -- rocq dep -Q . "" ./*.v >"$work/dep.txt" 2>"$work/dep.log" || {
    echo "compare_assoc_phase: rocq dep failed" >&2
    exit 2
  }
  "$PYTHON" -I "$here/compare_assoc_phase.py" closure CdAssociatorAnf.v <"$work/dep.txt" >"$work/closure.txt" || exit 2
  echo "compare_assoc_phase: compiling $(grep -c . "$work/closure.txt") sources"
  while IFS= read -r source; do
    opam exec --switch="$switch" -- rocq compile -q -Q . "" "$source" >>"$work/compile.log" 2>&1 || {
      echo "compare_assoc_phase: $source does not compile" >&2
      exit 2
    }
  done <"$work/closure.txt"
  opam exec --switch="$switch" -- rocq compile -q -Q . "" CompareAssocPhase.v >"$work/rocq.txt" 2>&1 || {
    echo "compare_assoc_phase: the Rocq evaluation fails:" >&2
    tail -n 20 "$work/rocq.txt" >&2
    exit 2
  }
  opam exec --switch="$switch" -- rocq compile -q -Q . "" CompareAssocPhaseMutant.v >"$work/mutant.txt" 2>&1 || {
    echo "compare_assoc_phase: the mutated Rocq evaluation fails:" >&2
    tail -n 20 "$work/mutant.txt" >&2
    exit 2
  }
)
cd "$root/lean"
lake build --no-build -q GororobaMath.CayleyDickson.AssociatorPhase >&2 || {
  echo "compare_assoc_phase: build the Lean library first (lake build in lean/)" >&2
  exit 2
}
lake env lean --run "$work/CompareAssocPhase.lean" >"$work/lean.txt" || {
  echo "compare_assoc_phase: the Lean program failed" >&2
  exit 2
}
status=0
"$PYTHON" -I -B "$here/compare_assoc_phase.py" compare "$quantum" "$work/lean.txt" "$work/mutant.txt" >/dev/null 2>&1 ||
  status=$?
[ "$status" -eq 1 ] || {
  echo "compare_assoc_phase: the comparison did not reject the Rocq reference with its last two arguments swapped (status $status)" >&2
  exit 1
}
status=0
"$PYTHON" -I -B "$here/compare_assoc_phase.py" compare "$quantum" "$work/lean.txt" "$work/rocq.txt" --mutate-python \
  >/dev/null 2>&1 || status=$?
[ "$status" -eq 1 ] || {
  echo "compare_assoc_phase: the comparison did not reject the Python reference with one sign negated (status $status)" >&2
  exit 1
}
echo "compare_assoc_phase: the swapped Rocq arguments and the negated Python sign are rejected"
"$PYTHON" -I -B "$here/compare_assoc_phase.py" compare "$quantum" "$work/lean.txt" "$work/rocq.txt" || exit $?
echo "compare_assoc_phase: gororoba-quantum $(git -C "$quantum" rev-parse HEAD)"
