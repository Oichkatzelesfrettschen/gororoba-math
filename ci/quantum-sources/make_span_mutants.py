"""Six mutants of CdTowerG2DerivationSpan.v, each in its own directory with the lemma that must reject it.

Run: "$PYTHON" make_span_mutants.py SOURCE_V OUTPUT_DIRECTORY
Each mutant replaces one anchor, which must occur exactly once in the source, and writes OUTPUT_DIRECTORY/NAME/
CdTowerG2DerivationSpan.v and OUTPUT_DIRECTORY/NAME/expected-lemma.txt; run_span_checks.sh compiles them.
"""

from __future__ import annotations

import sys
from pathlib import Path

NAME = "CdTowerG2DerivationSpan.v"
# mutant -> (anchor in the source, replacement, lemma that rejects it)
MUTANTS = {
    "back-entry": ("    [(0%nat, (-6, 0))];", "    [(0%nat, (-5, 0))];", "splitting"),
    "scalar": ("Definition scalar : Z * Z := (6, 0).", "Definition scalar : Z * Z := (3, 0).", "splitting"),
    "equation-changed": ("[(0, 0, 0)%nat; (0, 0, 1)%nat;", "[(0, 0, 0)%nat; (0, 1, 1)%nat;", "splitting"),
    "equation-dropped": ("[(0, 0, 0)%nat; (0, 0, 1)%nat;", "[(0, 0, 1)%nat;", "tables_well_formed"),
    "equation-out-of-range": (
        "[(0, 0, 0)%nat; (0, 0, 1)%nat;",
        "[(0, 0, 16)%nat; (0, 0, 1)%nat;",
        "equations_in_range",
    ),
    "back-repeated-key": (
        "    [(0%nat, (-6, 0))];",
        "    [(0%nat, (-6, 0)); (0%nat, (0, 0))];",
        "tables_well_formed",
    ),
}


def mutate(source: str) -> dict[str, str]:
    """The text of each mutant; an anchor that does not occur exactly once raises."""
    texts = {}
    for name, (old, new, _lemma) in MUTANTS.items():
        if source.count(old) != 1:
            raise RuntimeError(f"{name}: the anchor occurs {source.count(old)} times")
        texts[name] = source.replace(old, new)
    return texts


def main(argv: list[str] | None = None) -> int:
    arguments = sys.argv[1:] if argv is None else argv
    if len(arguments) != 2:
        print(__doc__, file=sys.stderr)
        return 2
    source = Path(arguments[0]).read_text(encoding="ascii")
    out = Path(arguments[1])
    for name, text in mutate(source).items():
        directory = out / name
        directory.mkdir(parents=True, exist_ok=True)
        (directory / NAME).write_text(text, encoding="ascii")
        (directory / "expected-lemma.txt").write_text(MUTANTS[name][2] + "\n", encoding="ascii")
    return 0


if __name__ == "__main__":
    sys.exit(main())
