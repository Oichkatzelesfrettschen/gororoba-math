#!/bin/sh
# Usage: PYTHON=PATH sh ci/compare_transport.sh
# Compares the transport coordinates of lean/GororobaMath/CayleyDickson/PureDoublingTransport.lean in Lean
# and Rocq on the same inputs (ci/compare_transport.py): Tower.phi i u and Tower.phi (-i) u of u at level 5
# (the coordinates of level 4), and the same two maps of y * x for seeded u, y, x, against phi and psi of
# StiefelTransport in rocq/quantum/StiefelA5Transport.v evaluated at u and at T.mul 5 y x. The ring is
# ZMod p with p = 998244353 (p = 1 mod 4) and i = 911660635, the identity as star: Lean reads it as
# ZMod p with starRingOfComm, Rocq as Zmod p instantiated into CommutativeRingWithI. The cases are 24
# seeded triples of coordinate vectors with entries in -9 to 9 (32 coordinates each). Lean runs as a
# program under lake env lean --run, and Rocq evaluates with vm_compute after compiling the closure of
# StiefelA5Transport.v from a copy of rocq/quantum of this checkout. Before the verdict counts, the
# comparison must reject two mutated Rocq references: coordinate 3 of phi negated, and the two halves of
# each argument exchanged. The Rocq sources are in this repository, so the script reads no other
# checkout. Runs on demand, outside ci/check.sh, because it needs the Rocq switch of ci/install_rocq.sh
# beside the Lean toolchain with a built lean/.lake (the script runs lake build --no-build, which builds
# nothing).
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool or the switch is missing, a
# source does not compile, an output is empty or incomplete, or the Lean module is stale. On a stale Lean
# module, Lake writes a .nobuild trace beside the module's trace in lean/.lake before the script exits 2;
# otherwise the script writes only under a temporary directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
export PYTHON
for tool in git lake opam "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_transport: $tool is not on PATH" >&2
    exit 2
  }
done
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_transport: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(git -C "$here" rev-parse --show-toplevel)
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

mkdir "$work/quantum"
git -C "$root" ls-files -z -- 'rocq/quantum/*.v' | (cd "$root" && xargs -0 cp -t "$work/quantum")
"$PYTHON" -I -B "$here/compare_transport.py" cases "$work/CompareTransport.lean" "$work/quantum" || exit 2
(
  cd "$work/quantum"
  opam exec --switch="$switch" -- rocq dep -Q . "" ./*.v >"$work/dep.txt" 2>"$work/dep.log" || {
    echo "compare_transport: rocq dep failed" >&2
    exit 2
  }
  "$PYTHON" -I -B "$here/compare_transport.py" closure StiefelA5Transport.v <"$work/dep.txt" \
    >"$work/closure.txt" || exit 2
  echo "compare_transport: compiling $(grep -c . "$work/closure.txt") sources"
  while IFS= read -r source; do
    opam exec --switch="$switch" -- rocq compile -q -Q . "" "$source" >>"$work/compile.log" 2>&1 || {
      echo "compare_transport: $source does not compile" >&2
      tail -n 20 "$work/compile.log" >&2
      exit 2
    }
  done <"$work/closure.txt"
  for name in CompareTransport CompareTransportSign CompareTransportSwap; do
    opam exec --switch="$switch" -- rocq compile -q -Q . "" "$name.v" >"$work/$name.txt" 2>&1 || {
      echo "compare_transport: the Rocq evaluation $name fails:" >&2
      tail -n 20 "$work/$name.txt" >&2
      exit 2
    }
  done
)
cd "$root/lean"
lake build --no-build -q GororobaMath.CayleyDickson.PureDoublingTransport >&2 || {
  echo "compare_transport: build the Lean library first (lake build in lean/)" >&2
  exit 2
}
lake env lean --run "$work/CompareTransport.lean" >"$work/lean.txt" || {
  echo "compare_transport: the Lean program failed" >&2
  exit 2
}
for pair in "Sign:coordinate 3 of phi negated" "Swap:the halves of each argument exchanged"; do
  name=${pair%%:*}
  status=0
  "$PYTHON" -I -B "$here/compare_transport.py" compare "$work/lean.txt" "$work/CompareTransport$name.txt" \
    >/dev/null 2>&1 || status=$?
  [ "$status" -eq 1 ] || {
    echo "compare_transport: the comparison did not reject the mutated Rocq reference (${pair#*:}), status $status" >&2
    exit 1
  }
  echo "compare_transport: the Rocq reference with ${pair#*:} is rejected"
done
"$PYTHON" -I -B "$here/compare_transport.py" compare "$work/lean.txt" "$work/CompareTransport.txt" || exit $?
