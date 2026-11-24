#!/bin/sh
# Usage: GOROROBA_QUANTUM=CHECKOUT sh ci/compare_hilbert_cell_header.sh
# Binds the J and G tables of rocq/quantum/HilbertCellA5_108.v to the canonical header of the cell A5-108,
# docs/evidence/a5-exceptional-fibers/working/build/inputs/p32029-r9115/e8-vb.sing of the gororoba-quantum
# checkout GOROROBA_QUANTUM (its sha256 is pinned in ci/compare_hilbert_cell_header.py). The helper parses
# the header with its own reader of the expanded signed-monomial format; Rocq prints a5_108_J and
# a5_108_G with vm_compute after compiling copies of HilbertCellCertificate.v and HilbertCellA5_108.v;
# the helper compares the two as lists of polynomials, term by term modulo 32029. Before the verdict counts,
# a copy of the header with the first coefficient of J changed and a copy with the first coefficient of G
# changed must each differ from the Rocq tables. Runs on demand, outside ci/check.sh, because it needs the
# Rocq switch of ci/install_rocq.sh and a gororoba-quantum checkout.
# Exit status: 0 agreement, 1 a difference or an accepted mutant, 2 a tool, the switch, the checkout or the
# header digest is missing or wrong, or a source does not compile. The script writes only under a temporary
# directory it removes.
set -eu

PYTHON=${PYTHON:-python3}
export PYTHON
for tool in opam "$PYTHON"; do
  command -v "$tool" >/dev/null || {
    echo "compare_hilbert_cell_header: $tool is not on PATH" >&2
    exit 2
  }
done
switch=rocq-9.3
opam switch list --short | grep -q -x -F "$switch" || {
  echo "compare_hilbert_cell_header: opam switch $switch does not exist; run sh ci/install_rocq.sh" >&2
  exit 2
}
: "${GOROROBA_QUANTUM:?compare_hilbert_cell_header: set GOROROBA_QUANTUM to a gororoba-quantum checkout}"
header="$GOROROBA_QUANTUM/docs/evidence/a5-exceptional-fibers/working/build/inputs/p32029-r9115/e8-vb.sing"
[ -f "$header" ] || {
  echo "compare_hilbert_cell_header: $header does not exist" >&2
  exit 2
}

here=$(CDPATH='' cd -- "$(dirname -- "$0")" && pwd)
root=$(dirname -- "$here")
work=$(mktemp -d)
trap 'rm -r "$work" </dev/null' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
helper="$here/compare_hilbert_cell_header.py"

for source in HilbertCellCertificate HilbertCellA5_108; do
  cp "$root/rocq/quantum/$source.v" "$work/$source.v"
done
cat >"$work/CompareHilbertHeader.v" <<'EOF'
From Stdlib Require Import ZArith List.
Require Import HilbertCellCertificate HilbertCellA5_108.
Import ListNotations.
Open Scope Z_scope.
Definition flat (t : list poly) : list (list (list Z * Z)) :=
  map (map (fun x => (map Z.of_nat (fst x), snd x))) t.
Eval vm_compute in (flat a5_108_J).
Eval vm_compute in (flat a5_108_G).
EOF
(
  cd "$work"
  for source in HilbertCellCertificate HilbertCellA5_108; do
    opam exec --switch="$switch" -- rocq compile -q -Q . '' "$source.v" >>"$work/compile.log" 2>&1 || {
      echo "compare_hilbert_cell_header: $source.v does not compile" >&2
      tail -n 20 "$work/compile.log" >&2
      exit 2
    }
  done
  opam exec --switch="$switch" -- rocq compile -q -Q . '' CompareHilbertHeader.v >"$work/eval.txt" 2>&1 || {
    echo "compare_hilbert_cell_header: the Rocq evaluation fails:" >&2
    tail -n 20 "$work/eval.txt" >&2
    exit 2
  }
)
"$PYTHON" -I -B "$helper" rocq "$work/eval.txt" "$work/rocq.json" || exit 2
"$PYTHON" -I -B "$helper" reference "$header" "$work/reference.json" || exit 2
for table in J G; do
  "$PYTHON" -I -B "$helper" mutate "$header" "$work/mutant$table.sing" "$table" || exit 2
  "$PYTHON" -I -B "$helper" reference-unpinned "$work/mutant$table.sing" "$work/mutant$table.json" || exit 2
  status=0
  "$PYTHON" -I -B "$helper" compare "$work/mutant$table.json" "$work/rocq.json" >/dev/null 2>&1 || status=$?
  [ "$status" -eq 1 ] || {
    echo "compare_hilbert_cell_header: the comparison did not reject the header with the first coefficient of $table changed (status $status)" >&2
    exit 1
  }
done
echo "compare_hilbert_cell_header: the headers with a changed coefficient of J and of G are rejected"
"$PYTHON" -I -B "$helper" compare "$work/reference.json" "$work/rocq.json"
