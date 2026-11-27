#!/bin/sh
# Usage: PYTHON=PATH sh ci/compare_complexification.sh
# Compares the complexification maps of lean/GororobaMath/CayleyDickson/StiefelRealZeroDivisor.lean
# (Tower.map along the embedding of the real ring and the real and imaginary coordinates of a complex
# tower element, Tower.repr_map) in Lean and Rocq on the same inputs (ci/compare_complexification.py):
# emb, re and im of rocq/quantum/StiefelA5Real.v against the coordinates of Tower.map along
# Int.castRingHom into the Gaussian integers, and the two sides of the product identity both proofs use
# (mul_emb in Rocq; in Lean, map y * x = map (y * xr) + I * map (y * xi)), at levels 4 and 5 on 16 and 8
# seeded cases with entries -9 to 9. The real ring is the integers and the complex ring the Gaussian
# integers: Lean reads them as GI (the Gaussian integers with the identity as star, as TrivStarComplex
# does for the complex numbers), a computable instance of the generic Tower.map, while Rocq evaluates the
# actual definitions over its real numbers with vm_compute, leaves each coordinate as a term of +, - and *
# on 0, 1 and a placeholder lit n, and the comparison reads each term back as an integer. Before the
# verdict counts, the comparison must reject two mutated Rocq references: re and im exchanged, and
# coordinate 3 of the embedded real element negated. The Rocq sources are in this repository, so the
# script reads no other checkout. Runs on demand, outside ci/check.sh, because it needs the Rocq switch of
# ci/install_rocq.sh beside the Lean toolchain with a built lean/.lake (the script runs lake build
# --no-build, which builds nothing).
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool or the switch is missing, a
# source does not compile, an output is empty or incomplete, or the Lean module is stale. On a stale Lean
# module, Lake writes a .nobuild trace beside the module's trace in lean/.lake before the script exits 2;
# otherwise the script writes only under a temporary directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
export PYTHON
for tool in git lake opam "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_complexification: $tool is not on PATH" >&2
    exit 2
  }
done
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_complexification: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
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
"$PYTHON" -I -B "$here/compare_complexification.py" cases "$work/CompareComplexification.lean" "$work/quantum" || exit 2
(
  cd "$work/quantum"
  opam exec --switch="$switch" -- rocq dep -Q . "" ./*.v >"$work/dep.txt" 2>"$work/dep.log" || {
    echo "compare_complexification: rocq dep failed" >&2
    exit 2
  }
  "$PYTHON" -I -B "$here/compare_complexification.py" closure StiefelA5Real.v <"$work/dep.txt" \
    >"$work/closure.txt" || exit 2
  echo "compare_complexification: compiling $(grep -c . "$work/closure.txt") sources"
  while IFS= read -r source; do
    opam exec --switch="$switch" -- rocq compile -q -Q . "" "$source" >>"$work/compile.log" 2>&1 || {
      echo "compare_complexification: $source does not compile" >&2
      tail -n 20 "$work/compile.log" >&2
      exit 2
    }
  done <"$work/closure.txt"
  for name in CompareComplexification CompareComplexificationSwap CompareComplexificationSign; do
    opam exec --switch="$switch" -- rocq compile -q -Q . "" "$name.v" >"$work/$name.txt" 2>&1 || {
      echo "compare_complexification: the Rocq evaluation $name fails:" >&2
      tail -n 20 "$work/$name.txt" >&2
      exit 2
    }
  done
)
cd "$root/lean"
lake build --no-build -q GororobaMath.CayleyDickson.StiefelRealZeroDivisor >&2 || {
  echo "compare_complexification: build the Lean library first (lake build in lean/)" >&2
  exit 2
}
lake env lean --run "$work/CompareComplexification.lean" >"$work/lean.txt" || {
  echo "compare_complexification: the Lean program failed:" >&2
  tail -n 20 "$work/lean.txt" >&2
  exit 2
}
for pair in "Swap:re and im exchanged" "Sign:coordinate 3 of emb negated"; do
  name=${pair%%:*}
  status=0
  "$PYTHON" -I -B "$here/compare_complexification.py" compare "$work/lean.txt" "$work/CompareComplexification$name.txt" \
    >/dev/null 2>&1 || status=$?
  [ "$status" -eq 1 ] || {
    echo "compare_complexification: the comparison did not reject the mutated Rocq reference (${pair#*:}), status $status" >&2
    exit 1
  }
  echo "compare_complexification: the Rocq reference with ${pair#*:} is rejected"
done
"$PYTHON" -I -B "$here/compare_complexification.py" compare "$work/lean.txt" "$work/CompareComplexification.txt" || exit $?
