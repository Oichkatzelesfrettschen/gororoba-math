"""Six mutants of the two generated Rocq files; each must fail to compile in the lemma named beside it.

Run: "$PYTHON" make_mutants.py ROCQ_DIRECTORY OUTPUT_DIRECTORY
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

SPARSE_ITEM = re.compile(r"\((\d+)%nat, \((-?\d+), (-?\d+)\)\)")
EXPECTED = {
    "ArcEntry": "w8_nm_linear_point1_left_inverse",
    "ArcScalar": "w8_nm_series_point1_left_inverse",
    "ArcShortRow": "w8_nm_series_point1_tables_well_formed",
    "ArcDuplicateKey": "w8_nm_series_point1_tables_well_formed",
    "G2Sign": "leibniz_basis_1",
    "G2Left": "independence_left_inverse",
}


def replace_once(text: str, old: str, new: str, after: str) -> str:
    start = text.index(old, text.index(after))
    return text[:start] + new + text[start + len(old) :]


def main(argv: list[str] | None = None) -> int:
    arguments = sys.argv[1:] if argv is None else argv
    if len(arguments) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    source, target = Path(arguments[0]), Path(arguments[1])
    arcs = (source / "A5W8ArcMatrixRanks.v").read_text(encoding="utf-8")
    g2 = (source / "CdTowerG2Derivations.v").read_text(encoding="utf-8")
    mutants = {
        "ArcEntry": replace_once(arcs, "(-44, -2291)", "(-44, -2290)", "Definition w8_nm_linear_point1_matrix"),
        "ArcScalar": replace_once(
            arcs, "w8_nm_series_point1_d : Z * Z := (-3600, 0)", "w8_nm_series_point1_d : Z * Z := (3600, 0)", "Module"
        ),
        "G2Sign": replace_once(
            g2, "  | 2 => vec [(5%nat, (0, 1)%Z)]", "  | 2 => vec [(5%nat, (0, -1)%Z)]", "Definition images_1 "
        ),
    }
    item = SPARSE_ITEM.search(g2, g2.index("Definition independence_left"))
    if item is None:
        raise RuntimeError("no entry in independence_left")
    negated = f"({item.group(1)}%nat, ({-int(item.group(2))}, {-int(item.group(3))}))"
    mutants["G2Left"] = g2[: item.start()] + negated + g2[item.end() :]
    start = arcs.index("Definition w8_nm_series_point1_matrix")
    row_end = arcs.index("]", arcs.index("[\n", start) + 2)
    last = arcs.rfind("; (", start, row_end)
    mutants["ArcShortRow"] = arcs[:last] + arcs[row_end:]
    item = SPARSE_ITEM.search(arcs, arcs.index("Definition w8_nm_series_point1_left"))
    if item is None:
        raise RuntimeError("no entry in w8_nm_series_point1_left")
    mutants["ArcDuplicateKey"] = arcs[: item.end()] + "; " + item.group(0) + arcs[item.end() :]
    target.mkdir(parents=True, exist_ok=True)
    for name, text in mutants.items():
        (target / f"{name}.v").write_text(text, encoding="utf-8")
        print(f"{name} {EXPECTED[name]}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
