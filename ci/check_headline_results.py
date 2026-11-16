"""Headline-result registry check: ci/headline-results.tsv against the library, README.md and the Rocq trees.

Usage:

    "$PYTHON" -I ci/check_headline_results.py

A headline result is a row of ci/headline-results.tsv (AGENTS.md, "Statements
and proofs"). The columns are prover, path, theorem, partner and tracking. This
script checks, from the repository root it sits under:

1. Each row of prover lean names a tracked file under lean/GororobaMath/ that
   declares the theorem: a theorem or lemma command whose name, prefixed by
   the namespaces open at that command, is the row's theorem.
2. The rows of prover lean are exactly the theorems the "Lean library" table
   of README.md names: each backquoted identifier in the Result column of a
   module's row that names a theorem of that module (by its full name, or by
   a suffix that starts after a dot) has a row with that module's path, and
   each row's theorem is named so in the table of its module. A backquoted
   dotted name with an upper-case first component that names no declaration
   of the module is an error, so a misspelled theorem name in the table fails.
3. The partner column is owed, with an issue URL in the tracking column, or
   PATH:NAME, optionally followed by " narrower: REASON". PATH is a source
   listed in the _RocqProject of its tree (rocq/open, rocq/quantum or
   rocq/delegation), and the source holds a Theorem, Lemma, Corollary,
   Proposition, Fact or Remark command named by the last component of NAME,
   inside a Module named by each earlier component.

Calibration. Before the verdict on the repository counts, the script runs the
same checks on five known-bad copies of the inputs (a row whose theorem the file
lacks, a README theorem without a row, a partner whose theorem the source
lacks, a partner source the project file omits, an owed row without an issue
URL) and requires each to fail, and on the repository inputs.

Exit status: 0 every check passed; 1 a check failed (each failure printed);
2 the calibration failed or an input is unreadable.
"""

from __future__ import annotations

import re
import subprocess
import sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HEADER = ["prover", "path", "theorem", "partner", "tracking"]
ISSUE_URL = re.compile(r"^https://github\.com/Oichkatzelesfrettschen/gororoba-math/issues/[0-9]+$")
PARTNER = re.compile(r"^(rocq/(?:open|quantum|delegation)/[A-Za-z0-9_/]+\.v):([A-Za-z0-9_.']+)(?: narrower: (.+))?$")
LEAN_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|public|nonrec)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|structure|class|inductive)\s+([^\s:({\[]+)"
)
LEAN_NAMESPACE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.']+)\s*$")
LEAN_SECTION = re.compile(r"^\s*(?:noncomputable\s+)?section(?:\s+([A-Za-z0-9_.']+))?\s*$")
LEAN_END = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_.']+))?\s*$")
ROCQ_THEOREM = re.compile(r"^\s*(?:Theorem|Lemma|Corollary|Proposition|Fact|Remark)\s+([A-Za-z0-9_']+)\b")
ROCQ_MODULE = re.compile(r"^\s*Module\s+(?:Type\s+)?([A-Za-z0-9_']+)\b")
TOKEN = re.compile(r"`([^`]+)`")
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_.']*$")


@dataclass
class Inputs:
    rows: list[list[str]]
    readme: str
    lean: dict[str, str]
    rocq: dict[str, str]
    projects: dict[str, set[str]] = field(default_factory=dict)


def lean_declarations(text: str) -> dict[str, str]:
    """Full name to kind ('theorem' for theorem and lemma) of each declaration of a Lean file."""
    scopes: list[tuple[str, list[str]]] = []
    found: dict[str, str] = {}
    in_comment = 0
    for line in text.splitlines():
        stripped = line
        if in_comment or "/-" in stripped:
            in_comment += stripped.count("/-") - stripped.count("-/")
            if in_comment > 0 or stripped.strip().startswith("/-"):
                continue
        match = LEAN_NAMESPACE.match(stripped)
        if match:
            scopes.append(("namespace", match.group(1).split(".")))
            continue
        match = LEAN_SECTION.match(stripped)
        if match:
            scopes.append(("section", []))
            continue
        match = LEAN_END.match(stripped)
        if match and scopes:
            scopes.pop()
            continue
        match = LEAN_DECL.match(stripped)
        if match:
            kind = "theorem" if match.group(1) in ("theorem", "lemma") else match.group(1)
            prefix = [part for _, parts in scopes for part in parts]
            found[".".join([*prefix, match.group(2)])] = kind
    return found


def rocq_theorems(text: str) -> set[str]:
    """Names Module.Sub.name of the theorem-like commands of a Rocq file, with every enclosing module prefix."""
    names: set[str] = set()
    modules: list[str] = []
    for line in text.splitlines():
        match = ROCQ_MODULE.match(line)
        if match and ":=" not in line:
            modules.append(match.group(1))
            continue
        end = re.match(r"^\s*End\s+([A-Za-z0-9_']+)\s*\.", line)
        if end and modules and modules[-1] == end.group(1):
            modules.pop()
            continue
        match = ROCQ_THEOREM.match(line)
        if match:
            names.add(".".join([*modules, match.group(1)]))
    return names


def readme_table(readme: str) -> dict[str, list[str]]:
    """Module path to the backquoted tokens of its Result column in the Lean library table."""
    table: dict[str, list[str]] = {}
    inside = False
    for line in readme.splitlines():
        if line.startswith("## "):
            inside = line.strip() == "## Lean library"
            continue
        if not inside or not line.startswith("| `GororobaMath."):
            continue
        cells = [cell.strip() for cell in re.split(r"(?<!\\)\|", line.strip().strip("|"))]
        module = cells[0].strip("`")
        path = "lean/" + module.replace(".", "/") + ".lean"
        table[path] = TOKEN.findall(cells[1])
    return table


def check(inputs: Inputs) -> list[str]:
    failures: list[str] = []
    if not inputs.rows or inputs.rows[0] != HEADER:
        return ["ci/headline-results.tsv: the header is not " + "\t".join(HEADER)]
    table = readme_table(inputs.readme)
    declared = {path: lean_declarations(text) for path, text in inputs.lean.items()}
    lean_rows: set[tuple[str, str]] = set()
    for number, row in enumerate(inputs.rows[1:], start=2):
        where = f"ci/headline-results.tsv:{number}"
        if len(row) != len(HEADER):
            failures.append(f"{where}: {len(row)} columns")
            continue
        prover, path, theorem, partner, tracking = row
        if prover != "lean":
            failures.append(f"{where}: prover {prover!r}; the registry holds Lean rows")
            continue
        lean_rows.add((path, theorem))
        if path not in declared:
            failures.append(f"{where}: {path} is not a tracked module under lean/GororobaMath/")
        elif declared[path].get(theorem) != "theorem":
            failures.append(f"{where}: {path} declares no theorem {theorem}")
        if partner == "owed":
            if not ISSUE_URL.match(tracking):
                failures.append(f"{where}: an owed partner needs the issue URL that tracks it, not {tracking!r}")
            continue
        if tracking != "-" and not ISSUE_URL.match(tracking):
            failures.append(f"{where}: tracking {tracking!r} is neither - nor an issue URL")
        match = PARTNER.match(partner)
        if not match:
            failures.append(f"{where}: partner {partner!r} is neither owed nor PATH:NAME[ narrower: REASON]")
            continue
        source, name = match.group(1), match.group(2)
        tree = "/".join(source.split("/")[:2])
        listed = inputs.projects.get(tree, set())
        if source[len(tree) + 1 :] not in listed:
            failures.append(f"{where}: {source} is not listed in {tree}/_RocqProject")
        elif name not in rocq_theorems(inputs.rocq.get(source, "")):
            failures.append(f"{where}: {source} holds no theorem {name}")
    for path, tokens in sorted(table.items()):
        names = declared.get(path)
        if names is None:
            failures.append(f"README.md: the Lean library table names {path}, which is not a tracked module")
            continue
        for token in tokens:
            if not IDENT.match(token):
                continue
            hits = [full for full in names if full == token or full.endswith("." + token)]
            theorems = [full for full in hits if names[full] == "theorem"]
            if not hits and "." in token and token[0].isupper() and not token.startswith("GororobaMath."):
                failures.append(f"README.md: {token} in the row of {path} names no declaration of that module")
            for full in theorems:
                if (path, full) not in lean_rows:
                    failures.append(f"README.md: {full} ({path}) is a theorem the table names and has no row")
    for path, theorem in sorted(lean_rows):
        tokens = table.get(path, [])
        if not any(theorem == token or theorem.endswith("." + token) for token in tokens):
            failures.append(f"ci/headline-results.tsv: {theorem} is not named in the README row of {path}")
    return failures


def read_inputs() -> Inputs:
    tracked = subprocess.run(  # noqa: S603
        ["git", "-C", str(ROOT), "ls-files", "--", "lean/GororobaMath", "rocq"],  # noqa: S607
        check=True,
        capture_output=True,
        text=True,
    ).stdout.split()
    lean = {p: (ROOT / p).read_text(encoding="utf-8") for p in tracked if p.endswith(".lean")}
    rocq = {p: (ROOT / p).read_text(encoding="utf-8") for p in tracked if p.endswith(".v")}
    projects: dict[str, set[str]] = {}
    for tree in ("rocq/open", "rocq/quantum", "rocq/delegation"):
        lines = (ROOT / tree / "_RocqProject").read_text(encoding="utf-8").splitlines()
        projects[tree] = {line.strip() for line in lines if line.strip().endswith(".v")}
    rows_text = (ROOT / "ci/headline-results.tsv").read_text(encoding="utf-8")
    rows = [line.split("\t") for line in rows_text.splitlines() if line]
    return Inputs(rows, (ROOT / "README.md").read_text(encoding="utf-8"), lean, rocq, projects)


def mutants(good: Inputs) -> dict[str, Inputs]:
    """Five known-bad copies of the inputs, each with one defect the checks must report."""

    def copy(rows: list[list[str]] | None = None, projects: dict[str, set[str]] | None = None) -> Inputs:
        return Inputs(
            [list(r) for r in (rows if rows is not None else good.rows)],
            good.readme,
            good.lean,
            good.rocq,
            projects if projects is not None else good.projects,
        )

    first = good.rows[1]
    with_partner = next((r for r in good.rows[1:] if r[3] != "owed"), None)
    owed = next((r for r in good.rows[1:] if r[3] == "owed"), None)
    if with_partner is None or owed is None:
        raise SystemExit("check_headline_results: calibration needs one owed row and one row with a partner")
    cases: dict[str, Inputs] = {}
    rows = [list(r) for r in good.rows]
    rows[1][2] = first[2] + "_missing"
    cases["a row whose theorem the file lacks"] = copy(rows)
    cases["a README theorem without a row"] = copy([good.rows[0], *good.rows[2:]])
    rows = [list(r) for r in good.rows]
    index = good.rows.index(with_partner)
    rows[index][3] = with_partner[3].split(" ")[0] + "_missing"
    cases["a partner whose theorem the source lacks"] = copy(rows)
    source = PARTNER.match(with_partner[3]).group(1)
    tree = "/".join(source.split("/")[:2])
    projects = {k: set(v) for k, v in good.projects.items()}
    projects[tree].discard(source[len(tree) + 1 :])
    cases["a partner source the project file omits"] = copy(projects=projects)
    rows = [list(r) for r in good.rows]
    rows[good.rows.index(owed)][4] = "-"
    cases["an owed row without an issue URL"] = copy(rows)
    return cases


def main() -> int:
    try:
        good = read_inputs()
    except (OSError, subprocess.CalledProcessError) as error:
        print(f"check_headline_results: {error}", file=sys.stderr)
        return 2
    for label, bad in mutants(good).items():
        if not check(bad):
            print(f"check_headline_results: calibration accepted {label}", file=sys.stderr)
            return 2
    failures = check(good)
    for failure in failures:
        print(failure, file=sys.stderr)
    if failures:
        return 1
    print(f"check_headline_results: {len(good.rows) - 1} rows match the library, README.md and the Rocq trees")
    return 0


if __name__ == "__main__":
    sys.exit(main())
