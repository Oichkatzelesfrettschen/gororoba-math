"""Expected claims of the ledger, read from the pinned commits of the two source repositories.

Usage:

    GOROROBA_OPEN=PATH GOROROBA_QUANTUM=PATH "$PYTHON" -I ci/claims/expected_sources.py [--write]

ci/claims/expected-sources.tsv lists the claims that ci/claims/ledger.tsv must
hold: the source locator, the commit of its repository at which the claim was
read, and the sha256 of the source text there. ci/check_claims_ledger.py, in the
admission gate, requires the ledger sources to equal the listed ones. This
script runs on demand, because it reads two other repositories; it reads each
file with `git show COMMIT:PATH`, never the working tree of a checkout.

Source text. `gororoba-open:C-NNN` is the `statement` of that claim in
registry/claims.toml; `gororoba-open:doc:PATH.md:LINE` is line LINE of
docs/PATH.md; `gororoba-quantum:docs/PATH:LINE#LABEL` is line LINE of
docs/PATH. The digest is the sha256 of the UTF-8 text without a line end.

Without an option the script checks, for every listed source:

1. it resolves at its commit, and the digest equals the listed one;
2. a line locator names a nonempty line that is no first-level heading, and a
   label of the form A5-NNN is the first cell of its line;
3. the commit is the one PINS names for its file;
4. every row of a findings ledger (a .tsv source file) at its commit is listed,
   so the list holds the whole file and not a part of it;
5. the ledger statement of a registry claim is the registry statement with
   surrounding `**` removed and whitespace collapsed, cut to 30 words with
   `...` appended when it is longer;
6. a registry claim whose status is Refuted, Superseded or begins `Closed`
   does not read `proved` in the ledger.

`--write` writes the list again from the sources of the ledger: commits from
PINS, digests from the repositories. A claim joins the ledger by a new ledger
row and a `--write`; the commit of a file moves by an edit of PINS.

Calibration. Before a verdict counts the checks run on known-bad copies (a
changed digest, a listed line moved to a heading, a findings-ledger row left
out, a drifted ledger statement, a refuted claim marked proved) and must
report each.

Exit status: 0 the list matches the repositories (or was written); 1 a check
failed; 2 a checkout, a commit or a tool is missing, or the calibration failed.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import subprocess  # noqa: S404 - git show on the two named checkouts
import sys
from functools import cache
from pathlib import Path

import tomllib

ROOT = Path(__file__).resolve().parent.parent.parent
LEDGER = ROOT / "ci" / "claims" / "ledger.tsv"
EXPECTED = ROOT / "ci" / "claims" / "expected-sources.tsv"
HEADER = ["source", "commit", "sha256"]
OPEN_COMMIT = "f81aba2b4e9f18fef4ac751422972bf1d8f3a764"
QUANTUM_COMMIT = "78c780bc6993dcb1f14e72c3d9dd1e4e23da4ba3"
QUANTUM_LATER = "b7c2b373ca05be1f7096694d50f0c4638231b778"
# Files of gororoba-quantum read at the later commit: the findings ledger, whose rows A5-565 to
# A5-571 the earlier commit lacks, and the two topic notes of the second pass.
PINS = {
    "docs/evidence/a5-exceptional-fibers/ledger.tsv": QUANTUM_LATER,
    "docs/notes/topics/cd-star-lattice-tower.md": QUANTUM_LATER,
    "docs/notes/topics/c5-zero-divisor-code-falsification.md": QUANTUM_LATER,
}
CLAIM = re.compile(r"^gororoba-open:(C-[0-9]+)$")
DOCUMENT = re.compile(r"^gororoba-open:doc:([A-Za-z0-9_./-]+\.md):([1-9][0-9]*)$")
QUANTUM = re.compile(r"^gororoba-quantum:(docs/[A-Za-z0-9_./-]+\.(?:md|tsv)):([1-9][0-9]*)#(\S(?:.*\S)?)$")
FINDING = re.compile(r"^A5-[0-9]+$")
NOT_ASSERTED = ("Refuted", "Superseded")
MAX_WORDS = 30


class SourceError(Exception):
    """A condition under which no verdict is given."""


def checkout(variable: str) -> Path:
    named = os.environ.get(variable)
    if not named or not (Path(named) / ".git").exists():
        raise SourceError(f"set {variable} to a checkout of that repository")
    return Path(named)


@cache
def show(repository: Path, commit: str, path: str) -> str:
    done = subprocess.run(  # noqa: S603
        ["git", "-C", str(repository), "show", f"{commit}:{path}"],  # noqa: S607
        capture_output=True,
        check=False,
    )
    if done.returncode != 0:
        raise SourceError(
            f"{repository.name} holds no {path} at {commit}: {done.stderr.decode(errors='replace').strip()}"
        )
    return done.stdout.decode("utf-8")


class Repositories:
    """The two checkouts, read at the pinned commits."""

    def __init__(self, open_checkout: Path, quantum_checkout: Path) -> None:
        self.open = open_checkout
        self.quantum = quantum_checkout

    @cache  # noqa: B019 - one instance per run
    def claims(self) -> dict[str, dict[str, str]]:
        table = tomllib.loads(show(self.open, OPEN_COMMIT, "registry/claims.toml"))
        return {claim["id"]: claim for claim in table["claim"]}

    def lines(self, repository: Path, commit: str, path: str) -> list[str]:
        return show(repository, commit, path).split("\n")

    def locate(self, source: str) -> tuple[str, str]:
        """The commit of a source and its text there."""
        if match := CLAIM.match(source):
            claim = self.claims().get(match.group(1))
            if claim is None or "statement" not in claim:
                raise SourceError(f"{source}: registry/claims.toml holds no such claim with a statement")
            return OPEN_COMMIT, claim["statement"]
        if match := DOCUMENT.match(source):
            return OPEN_COMMIT, self.line(self.open, OPEN_COMMIT, "docs/" + match.group(1), int(match.group(2)), source)
        if match := QUANTUM.match(source):
            commit = PINS.get(match.group(1), QUANTUM_COMMIT)
            return commit, self.line(self.quantum, commit, match.group(1), int(match.group(2)), source)
        raise SourceError(f"{source}: none of the three locator forms")

    def line(self, repository: Path, commit: str, path: str, number: int, source: str) -> str:
        lines = self.lines(repository, commit, path)
        if number > len(lines):
            raise SourceError(f"{source}: {path} has {len(lines)} lines at {commit}")
        return lines[number - 1]


def digest(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def ledger_statement(registry_statement: str) -> str:
    """The ledger form of a registry statement: bold marks removed, at most 30 words, a cut marked."""
    words = registry_statement.strip().removeprefix("**").removesuffix("**").split()
    if len(words) <= MAX_WORDS:
        return " ".join(words)
    return " ".join(words[:MAX_WORDS]) + "..."


def read_table(path: Path) -> list[list[str]]:
    return [line.split("\t") for line in path.read_text(encoding="utf-8").splitlines() if line]


def check(repositories: Repositories, expected: list[list[str]], ledger: list[list[str]]) -> list[str]:
    failures: list[str] = []
    if not expected or expected[0] != HEADER:
        return ["expected-sources.tsv: the header is not " + "\t".join(HEADER)]
    rows = {row[0]: row for row in ledger[1:]}
    listed_by_file: dict[tuple[str, str], set[str]] = {}
    for number, row in enumerate(expected[1:], start=2):
        where = f"expected-sources.tsv:{number}"
        if len(row) != len(HEADER):
            failures.append(f"{where}: {len(row)} columns")
            continue
        source, commit, listed = row
        try:
            pinned, text = repositories.locate(source)
        except SourceError as error:
            failures.append(f"{where}: {error}")
            continue
        if commit != pinned:
            failures.append(f"{where}: {source} lists commit {commit}, and PINS names {pinned}")
        if digest(text) != listed:
            failures.append(f"{where}: the text of {source} at {pinned} has another sha256")
        if match := QUANTUM.match(source):
            path, label = match.group(1), match.group(3)
            if not text.strip() or text.startswith("# "):
                failures.append(f"{where}: {source} names an empty line or a first-level heading")
            if FINDING.match(label) and text.split("\t")[0] != label:
                failures.append(f"{where}: line of {source} does not begin with {label}")
            if path.endswith(".tsv"):
                listed_by_file.setdefault((path, pinned), set()).add(label)
        elif DOCUMENT.match(source):
            if not text.strip() or text.startswith("# "):
                failures.append(f"{where}: {source} names an empty line or a first-level heading")
        elif match := CLAIM.match(source):
            claim = repositories.claims()[match.group(1)]
            held = rows.get(source)
            if held is not None:
                if held[1] != ledger_statement(text):
                    failures.append(f"{where}: the ledger statement of {source} is not the registry statement")
                status = claim.get("status", "")
                if held[5] == "proved" and (status in NOT_ASSERTED or status.startswith("Closed")):
                    failures.append(f"{where}: {source} reads proved, and the registry status is {status}")
    for (path, commit), labels in sorted(listed_by_file.items()):
        lines = repositories.lines(repositories.quantum, commit, path)
        present = {line.split("\t")[0] for line in lines[1:] if line}
        absent = sorted(present - labels)
        if absent:
            failures.append(f"expected-sources.tsv: {len(absent)} rows of {path} are not listed, the first {absent[0]}")
    return failures


def build(repositories: Repositories, ledger: list[list[str]]) -> list[list[str]]:
    table = [HEADER]
    for row in ledger[1:]:
        commit, text = repositories.locate(row[0])
        table.append([row[0], commit, digest(text)])
    return table


def mutants(expected: list[list[str]], ledger: list[list[str]]) -> dict[str, tuple[list[list[str]], list[list[str]]]]:
    """Known-bad copies of the list and the ledger, each with one defect the checks must report."""

    def index_of(table: list[list[str]], pattern: re.Pattern[str]) -> int:
        for index, row in enumerate(table[1:], start=1):
            if pattern.match(row[0]):
                return index
        raise SourceError("the calibration needs a row of each locator form")

    cases = {}
    changed = [list(row) for row in expected]
    changed[1][2] = changed[1][2][:-1] + ("0" if changed[1][2][-1] != "0" else "1")
    cases["a changed digest"] = (changed, ledger)
    heading = [list(row) for row in expected]
    line = index_of(heading, re.compile(r"^gororoba-quantum:docs/[^#]+\.md:[0-9]+#"))
    heading[line][0] = re.sub(r":[0-9]+#", ":1#", heading[line][0], count=1)
    cases["a listed line moved to a heading"] = (heading, ledger)
    finding = index_of(expected, re.compile(r".*#A5-[0-9]+$"))
    cases["a findings-ledger row left out"] = ([*expected[:finding], *expected[finding + 1 :]], ledger)
    claim = index_of(ledger, CLAIM)
    drifted = [list(row) for row in ledger]
    drifted[claim][1] = drifted[claim][1] + " also"
    cases["a drifted ledger statement"] = (expected, drifted)
    return cases


def run(write: bool) -> int:
    repositories = Repositories(checkout("GOROROBA_OPEN"), checkout("GOROROBA_QUANTUM"))
    ledger = read_table(LEDGER)
    if write:
        table = build(repositories, ledger)
        EXPECTED.write_text("".join("\t".join(row) + "\n" for row in table), encoding="utf-8")
        print(f"expected_sources: wrote {len(table) - 1} sources")
        return 0
    expected = read_table(EXPECTED)
    baseline = check(repositories, expected, ledger)
    for label, (bad_expected, bad_ledger) in mutants(expected, ledger).items():
        if len(check(repositories, bad_expected, bad_ledger)) <= len(baseline):
            print(f"expected_sources: calibration accepted {label}", file=sys.stderr)
            return 2
    claims = repositories.claims()
    refuted = next(
        (
            index
            for index, row in enumerate(ledger)
            if (match := CLAIM.match(row[0]))
            and claims[match.group(1)].get("status") == "Refuted"
            and row[5] != "proved"
        ),
        None,
    )
    if refuted is None:
        print("expected_sources: calibration needs a ledger claim that the registry marks Refuted", file=sys.stderr)
        return 2
    marked = [list(row) for row in ledger]
    marked[refuted][5] = "proved"
    if len(check(repositories, expected, marked)) <= len(baseline):
        print("expected_sources: calibration accepted a refuted claim marked proved", file=sys.stderr)
        return 2
    for failure in baseline:
        print(failure, file=sys.stderr)
    if baseline:
        return 1
    print(
        f"expected_sources: {len(expected) - 1} listed sources match the commits of gororoba-open and gororoba-quantum"
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--write", action="store_true", help="write the list from the ledger sources")
    args = parser.parse_args()
    try:
        return run(args.write)
    except (SourceError, OSError, KeyError, ValueError) as error:
        print(f"expected_sources: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
