"""Write a copy of a Rocq source with one digit changed inside its generated text: perturb.py SOURCE DESTINATION.

The digit is the first one at or after the first generated-block marker `(* BEGIN`, or at the middle of a file
without a marker. ci/check_quantum_sources.sh feeds the copy to the generator that renders the file and requires
the comparison to fail. Exit status: 0 written, 2 usage error or no digit found.
"""

from __future__ import annotations

import sys
from pathlib import Path


def main(argv: list[str]) -> int:
    if len(argv) != 2:
        print("usage: perturb.py SOURCE DESTINATION", file=sys.stderr)
        return 2
    text = Path(argv[0]).read_text(encoding="utf-8")
    start = text.find("(* BEGIN")
    start = len(text) // 2 if start < 0 else start
    for position in range(start, len(text)):
        if text[position].isdigit():
            changed = text[:position] + str((int(text[position]) + 1) % 10) + text[position + 1 :]
            Path(argv[1]).write_text(changed, encoding="utf-8")
            return 0
    print("perturb.py: no digit to change", file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
