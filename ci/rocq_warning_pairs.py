"""Ratchet of the Rocq warnings outside the default set: (tree, source, warning) pairs.

Usage:

    "$PYTHON" -I ci/rocq_warning_pairs.py --tree TREE --allowed ci/rocq-warnings/allowed.tsv \
        --causes ci/rocq-warnings/causes.tsv [--observed FILE] [--new-only] LOG...

Each tree compiles with the warning option all,+default (each tree's
_RocqProject, and the recipes of rocq/open that compile outside it): a warning
of Rocq's default set is an error, and every other warning prints. This script
reads the build logs of one tree, collects each printed warning as the pair
(source path, warning name), and compares the set of pairs with the rows of the
allow-list for that tree.

Log format (Rocq 9.3.0, measured). A warning prints as a block: a line
'File "PATH", line N, characters A-B:', then text that begins with 'Warning:',
ending at a line whose last token is '[NAME,CATEGORY,...]' or '[NAME]'. PATH is
relative to the tree directory, with a leading './' that this script drops.

Verdicts. Exit 0: the observed pairs equal the allowed pairs of the tree. Exit 1:
a pair is observed and not allowed (a new warning), or allowed and not observed
(a fixed warning whose row must leave the list, so the list only shrinks); each
is printed. Exit 2: a log line that begins with 'Warning' sits outside a block
that a File line opens, a block lacks its name tag, a file is unreadable, a row
of either table is malformed, or a warning of the allow-list has no row in the
causes table (or a causes row names no allowed warning).

--new-only drops the second half of exit 1: an incremental build of a working
tree recompiles only the sources that changed, so its logs cannot show that an
allowed warning stopped. ci/check_rocq.sh builds every source of an export and
runs without it.

Calibration. Every run first parses four built-in logs: a block with a listed
pair is accepted, a block with an unlisted pair and an allow-list row with no
block are rejected with exit 1, and a warning without its File line is rejected
with exit 2. A different outcome exits 2 before any log is read.
"""

import argparse
import re
import sys
from pathlib import Path

HEADER = re.compile(r'^File "([^"]+)", line \d+, characters \d+-\d+:$')
TAG = re.compile(r"\[([A-Za-z0-9._-]+)(?:,[A-Za-z0-9._-]+)*\]$")
TREES = ("open", "quantum", "delegation")
ALLOWED_HEADER = ["tree", "path", "warning"]
CAUSES_HEADER = ["warning", "cause", "removal"]


class ParseError(Exception):
    """A log or table that the ratchet cannot read unambiguously."""


def parse_log(lines: list[str], origin: str) -> set[tuple[str, str]]:
    """Returns the (path, warning) pairs that the warning blocks of a log print."""
    pairs: set[tuple[str, str]] = set()
    path: str | None = None
    in_warning = False
    for number, raw in enumerate(lines, start=1):
        line = raw.rstrip("\n")
        header = HEADER.match(line)
        if header:
            if in_warning:
                raise ParseError(f"{origin}:{number}: a warning block ends without its name tag")
            path = header.group(1).removeprefix("./")
            continue
        if line.startswith("Warning"):
            if path is None or in_warning:
                raise ParseError(f"{origin}:{number}: a warning line follows no File line")
            in_warning = True
        elif path is not None and not in_warning:
            # The block that the File line opened is not a warning (an error).
            path = None
            continue
        if in_warning:
            tag = TAG.search(line.rstrip())
            if tag:
                pairs.add((str(path), tag.group(1)))
                path = None
                in_warning = False
    if in_warning:
        raise ParseError(f"{origin}: the last warning block ends without its name tag")
    return pairs


def read_table(path: Path, header: list[str]) -> list[list[str]]:
    """Reads a tab-separated table whose first line is the given header."""
    try:
        rows = [line.split("\t") for line in path.read_text(encoding="utf-8").splitlines()]
    except OSError as error:
        raise ParseError(f"{path}: {error}") from error
    if not rows or rows[0] != header:
        raise ParseError(f"{path}: the first line is not the header {' / '.join(header)}")
    body = rows[1:]
    for number, row in enumerate(body, start=2):
        if len(row) != len(header) or not all(cell.strip() for cell in row):
            raise ParseError(f"{path}:{number}: a row needs {len(header)} non-empty cells")
    if len({tuple(row) for row in body}) != len(body):
        raise ParseError(f"{path}: a row repeats")
    return body


def check_trees(rows: list[list[str]], path: str) -> None:
    """Rejects an allow-list row whose tree is not one of TREES, since no run compares it."""
    for number, row in enumerate(rows, start=2):
        if row[0] not in TREES:
            raise ParseError(f"{path}:{number}: tree {row[0]!r} is not one of {', '.join(TREES)}")


def compare(observed: set[tuple[str, str]], allowed: set[tuple[str, str]]) -> list[str]:
    """Lists each pair that is new (+) or no longer observed (-)."""
    new = [f"+ {path}\t{name}" for path, name in sorted(observed - allowed)]
    stale = [f"- {path}\t{name}" for path, name in sorted(allowed - observed)]
    return new + stale


def calibrate() -> None:
    """Checks the parser and the comparison on built-in logs; raises ParseError otherwise."""
    block = [
        'File "./theories/A.v", line 3, characters 0-34:',
        "Warning:",
        'Use of "( _ | _ )" Notation is deprecated as it is inconsistent with pattern syntax.',
        "[disj-pattern-notation,syntax]",
        'File "./theories/B.v", line 9, characters 0-12:',
        "Error: The reference x was not found in the current environment.",
    ]
    allowed = {("theories/A.v", "disj-pattern-notation")}
    if compare(parse_log(block, "calibration"), allowed):
        raise ParseError("calibration: a listed pair was not accepted")
    unlisted = [line.replace("A.v", "C.v") for line in block]
    if not compare(parse_log(unlisted, "calibration"), allowed):
        raise ParseError("calibration: an unlisted pair was accepted")
    if not compare(set(), allowed):
        raise ParseError("calibration: an allowed pair that no log prints was accepted")
    try:
        check_trees([["quantm", "Ghost.v", "disj-pattern-notation"]], "calibration")
    except ParseError:
        pass
    else:
        raise ParseError("calibration: an allow-list row of an unknown tree was accepted")
    try:
        parse_log(block[1:4], "calibration")
    except ParseError:
        return
    raise ParseError("calibration: a warning without its File line was accepted")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--tree", required=True, choices=TREES)
    parser.add_argument("--allowed", required=True, type=Path)
    parser.add_argument("--causes", required=True, type=Path)
    parser.add_argument("--observed", type=Path, help="write the observed pairs of the tree here")
    parser.add_argument("--new-only", action="store_true", help="report new pairs only (incremental builds)")
    parser.add_argument("logs", nargs="+", type=Path)
    arguments = parser.parse_args()
    try:
        calibrate()
        allowed_rows = read_table(arguments.allowed, ALLOWED_HEADER)
        check_trees(allowed_rows, str(arguments.allowed))
        causes_rows = read_table(arguments.causes, CAUSES_HEADER)
        named = {row[0] for row in causes_rows}
        listed = {row[2] for row in allowed_rows}
        if len(named) != len(causes_rows):
            raise ParseError(f"{arguments.causes}: a warning has two rows")
        if listed - named:
            raise ParseError(f"{arguments.causes}: no row for {', '.join(sorted(listed - named))}")
        if named - listed:
            raise ParseError(f"{arguments.causes}: no allowed pair names {', '.join(sorted(named - listed))}")
        observed: set[tuple[str, str]] = set()
        for log in arguments.logs:
            try:
                lines = log.read_text(encoding="utf-8", errors="strict").splitlines()
            except (OSError, UnicodeDecodeError) as error:
                raise ParseError(f"{log}: {error}") from error
            observed |= parse_log(lines, str(log))
    except ParseError as error:
        print(f"rocq_warning_pairs: {error}", file=sys.stderr)
        return 2
    if arguments.observed is not None:
        table = ["\t".join(ALLOWED_HEADER)]
        table += [f"{arguments.tree}\t{path}\t{name}" for path, name in sorted(observed)]
        arguments.observed.write_text("\n".join(table) + "\n", encoding="utf-8")
    allowed = {(row[1], row[2]) for row in allowed_rows if row[0] == arguments.tree}
    difference = compare(observed, allowed)
    if arguments.new_only:
        difference = [line for line in difference if line.startswith("+ ")]
    if difference:
        message = f"rocq_warning_pairs: {arguments.tree}: the observed warnings differ from the allow-list"
        print(message, file=sys.stderr)
        print("\n".join(difference), file=sys.stderr)
        return 1
    print(f"rocq_warning_pairs: {arguments.tree}: {len(observed)} pairs, all allowed")
    return 0


if __name__ == "__main__":
    sys.exit(main())
