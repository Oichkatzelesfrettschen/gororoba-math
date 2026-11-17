"""Claims ledger check: ci/claims/ledger.tsv against the library and the Rocq trees.

Usage:

    "$PYTHON" -I ci/check_claims_ledger.py

The ledger (ci/claims/README.md) holds one row per stated mathematical claim of
gororoba-open and gororoba-quantum, with its placement and its formal status.
This script checks, from the repository root it sits under:

1. The header line and the eight columns of every row.
2. The sources: each is gororoba-open: or gororoba-quantum: followed by an
   identifier, and the sources are unique and in ascending byte order.
3. The enumerations: the quantifier (every-level, fixed-dimension N, ring-class,
   concrete-table, numeric, other), the placement (lean, rocq, both, none), the
   clause (one of CLAUSES, each with the placements it decides) and the status
   (proved, partial, owed, no-proof-owed).
4. The status rules: proved and partial rows name a proof, owed and
   no-proof-owed rows hold "-", and the placement none holds with the status
   no-proof-owed only.
5. The statement (at most 30 words) and the note ("-" when empty).
6. Each proof entry PATH:NAME names a declaration: a theorem, lemma or instance
   of a tracked module under lean/GororobaMath/, or a proved theorem-like command
   of a source that a _RocqProject lists. The lexers and the resolvers are those
   of ci/check_headline_results.py.
7. ci/claims/unlinked-proof-files.tsv: its sources are ledger rows, in ascending
   order, and each file is a project-listed Rocq source.

Calibration. Before the verdict on the repository counts, the script runs the
same checks on known-bad copies of the inputs, one per rule (the mutants
function lists them), and requires each to fail; it runs them on known-good
copies (the controls function) and requires each to add no failure to those of
the repository inputs.

Exit status: 0 every check passed; 1 a check failed (each failure printed);
2 the calibration failed or an input is unreadable.
"""

from __future__ import annotations

import importlib.util
import re
import sys
from dataclasses import dataclass, replace
from pathlib import Path
from types import ModuleType

ROOT = Path(__file__).resolve().parent.parent
HEADER = ["source", "statement", "quantifier", "placement", "clause", "status", "proof", "note"]
LIST_HEADER = ["source", "proof_file"]
QUANTIFIERS = ("every-level", "ring-class", "concrete-table", "numeric", "other")
PLACEMENTS = ("lean", "rocq", "both", "none")
STATUSES = ("proved", "partial", "owed", "no-proof-owed")
MAX_STATEMENT_WORDS = 30
MAX_CLAUSE_WORDS = 12
SOURCE = re.compile(r"^gororoba-(?:open|quantum):\S.*$")
FIXED_DIMENSION = re.compile(r"^fixed-dimension [0-9]+$")
ROCQ_SOURCE = re.compile(r"^rocq/(?:open|quantum|delegation)/[A-Za-z0-9_/]+\.v$")
LEAN_PROOF_KINDS = ("theorem", "instance")
OUTSIDE = "Outside the clauses: physics, software, data or measurement"
# Clause text to the placements it decides (AGENTS.md, "Statements and proofs"; ci/claims/README.md).
CLAUSES: dict[str, tuple[str, ...]] = {
    "Statement over every level or ring class: Lean on Mathlib": ("lean",),
    "Fixed algebra instancing a Lean theorem: stays beside it": ("lean",),
    "Fixed finite structure decided by evaluation: Rocq": ("rocq",),
    "Certificate evaluated by vm_compute or extracted code: Rocq": ("rocq",),
    "Finite group or combinatorial structure: its library prover": ("lean", "rocq"),
    "Both axes: general Lean theorem and Rocq certificate": ("both",),
    "Result already in a proof tree stays where it is": ("lean", "rocq", "both"),
    OUTSIDE: ("none",),
    "Outside the clauses: analogy or interpretation, no mathematical statement": ("none",),
}
LEAN_EXTRA = 'def calibrationString : String := "/- \\" -/ -- \\\\"\n-- /- a line comment that opens a block\n'
ROCQ_EXTRA = (
    "(* Module Bogus. Theorem fake : True. Proof. Qed. *)\n"
    'Definition calibration_string := "say ""(*"" and ""*)"" ".\n'
    "Module Type CalibrationT.\n  Parameter calibration_p : nat.\nEnd CalibrationT.\n"
)


def load_headline() -> ModuleType:
    """The module ci/check_headline_results.py, imported from its path (the -I flag leaves ci/ off sys.path)."""
    path = ROOT / "ci" / "check_headline_results.py"
    spec = importlib.util.spec_from_file_location("check_headline_results", path)
    if spec is None or spec.loader is None:
        raise ImportError(f"cannot load {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules["check_headline_results"] = module
    spec.loader.exec_module(module)
    return module


H = load_headline()


@dataclass
class Inputs:
    rows: list[list[str]]
    unlinked: list[list[str]]
    lean: dict[str, str]
    rocq: dict[str, str]
    projects: dict[str, set[str]]


def split_table(text: str) -> list[list[str]]:
    """The tab-separated lines of a table, empty lines dropped."""
    return [line.split("\t") for line in text.splitlines() if line]


def split_proof(entry: str) -> tuple[str, str]:
    """PATH and NAME of a proof entry; a path holds no colon."""
    path, _, name = entry.partition(":")
    return path, name


def proof_entries(row: list[str]) -> list[str]:
    return [] if row[6] == "-" else row[6].split(";")


def check_proof_entry(where: str, entry: str, inputs: Inputs, declared: dict, proved: dict) -> list[str]:
    path, name = split_proof(entry)
    if not name:
        return [f"{where}: proof entry {entry!r} is not PATH:NAME"]
    if path.endswith(".lean"):
        if path not in declared:
            return [f"{where}: {path} is not a tracked module under lean/GororobaMath/"]
        if declared[path].get(name) not in LEAN_PROOF_KINDS:
            return [f"{where}: {path} declares no public theorem or instance {name}"]
        return []
    if not ROCQ_SOURCE.match(path):
        return [f"{where}: proof path {path!r} is no Lean module and no Rocq source of the three trees"]
    tree = "/".join(path.split("/")[:2])
    if path[len(tree) + 1 :] not in inputs.projects.get(tree, set()):
        return [f"{where}: {path} is not listed in {tree}/_RocqProject"]
    if name not in proved.get(path, set()):
        return [f"{where}: {path} holds no theorem {name} that ends in Qed or Defined"]
    return []


def check_row(where: str, row: list[str], inputs: Inputs, declared: dict, proved: dict) -> list[str]:
    if len(row) != len(HEADER):
        return [f"{where}: {len(row)} columns, not {len(HEADER)}"]
    source, statement, quantifier, placement, clause, status, proof, note = row
    failures: list[str] = []
    if not SOURCE.match(source):
        failures.append(f"{where}: source {source!r} is not gororoba-open:ID or gororoba-quantum:ID")
    words = len(statement.split())
    if words == 0 or words > MAX_STATEMENT_WORDS:
        failures.append(f"{where}: the statement holds {words} words, not 1 to {MAX_STATEMENT_WORDS}")
    if quantifier not in QUANTIFIERS and not FIXED_DIMENSION.match(quantifier):
        failures.append(f"{where}: quantifier {quantifier!r} is not in the enumeration")
    if placement not in PLACEMENTS:
        failures.append(f"{where}: placement {placement!r} is not lean, rocq, both or none")
    if clause not in CLAUSES:
        failures.append(f"{where}: clause {clause!r} is not a placement clause of ci/claims/README.md")
    elif len(clause.split()) > MAX_CLAUSE_WORDS or placement not in CLAUSES[clause]:
        failures.append(f"{where}: clause {clause!r} does not decide the placement {placement}")
    if status not in STATUSES:
        failures.append(f"{where}: status {status!r} is not in the enumeration")
    if not note:
        failures.append(f"{where}: the note is empty (write - for none)")
    holds_proof = proof != "-"
    if status in ("proved", "partial") and not holds_proof:
        failures.append(f"{where}: status {status} needs a proof")
    if status in ("owed", "no-proof-owed") and holds_proof:
        failures.append(f"{where}: status {status} holds - in the proof column")
    if (placement == "none") != (status == "no-proof-owed"):
        failures.append(f"{where}: placement none and status no-proof-owed go together, not {placement}, {status}")
    for entry in proof_entries(row):
        failures.extend(check_proof_entry(where, entry, inputs, declared, proved))
    return failures


def check_unlinked(inputs: Inputs, sources: set[str]) -> list[str]:
    where = "ci/claims/unlinked-proof-files.tsv"
    if not inputs.unlinked or inputs.unlinked[0] != LIST_HEADER:
        return [f"{where}: the header is not " + "\t".join(LIST_HEADER)]
    failures: list[str] = []
    listed = [row[0] for row in inputs.unlinked[1:]]
    for number, row in enumerate(inputs.unlinked[1:], start=2):
        if len(row) != len(LIST_HEADER):
            failures.append(f"{where}:{number}: {len(row)} columns, not {len(LIST_HEADER)}")
            continue
        source, proof_file = row
        if source not in sources:
            failures.append(f"{where}:{number}: {source} is not a row of the ledger")
        tree = "/".join(proof_file.split("/")[:2])
        if not ROCQ_SOURCE.match(proof_file) or proof_file[len(tree) + 1 :] not in inputs.projects.get(tree, set()):
            failures.append(f"{where}:{number}: {proof_file} is not a project-listed Rocq source")
    for number, (before, after) in enumerate(zip(listed, listed[1:], strict=False), start=3):
        if before >= after:
            failures.append(f"{where}:{number}: the source {after} does not sort after {before}")
    return failures


def check(inputs: Inputs) -> list[str]:
    if not inputs.rows or inputs.rows[0] != HEADER:
        return ["ci/claims/ledger.tsv: the header is not " + "\t".join(HEADER)]
    declared = {path: H.lean_declarations(text) for path, text in inputs.lean.items()}
    proved = {path: H.rocq_theorems(text) for path, text in inputs.rocq.items()}
    failures: list[str] = []
    for number, row in enumerate(inputs.rows[1:], start=2):
        failures.extend(check_row(f"ci/claims/ledger.tsv:{number}", row, inputs, declared, proved))
    sources = [row[0] for row in inputs.rows[1:]]
    for number, (before, after) in enumerate(zip(sources, sources[1:], strict=False), start=3):
        if before == after:
            failures.append(f"ci/claims/ledger.tsv:{number}: the source {after} repeats")
        elif before > after:
            failures.append(f"ci/claims/ledger.tsv:{number}: the source {after} sorts before {before}")
    failures.extend(check_unlinked(inputs, set(sources)))
    return failures


def read_inputs() -> Inputs:
    base = H.read_inputs()
    rows = split_table((ROOT / "ci/claims/ledger.tsv").read_text(encoding="utf-8"))
    unlinked = split_table((ROOT / "ci/claims/unlinked-proof-files.tsv").read_text(encoding="utf-8"))
    return Inputs(rows, unlinked, base.lean, base.rocq, base.projects)


def first_proof(good: Inputs, suffix: str) -> tuple[int, str, str]:
    """Row index, path and name of the first ledger proof entry in a file that ends with suffix."""
    for index, row in enumerate(good.rows[1:], start=1):
        for entry in proof_entries(row):
            path, name = split_proof(entry)
            if path.endswith(suffix):
                return index, path, name
    raise SystemExit(f"check_claims_ledger: calibration needs a ledger proof entry in a {suffix} file")


def find_row(good: Inputs, status: str, placement: str | None = None) -> int:
    for index, row in enumerate(good.rows[1:], start=1):
        if row[5] == status and (placement is None or row[3] == placement):
            return index
    raise SystemExit(f"check_claims_ledger: calibration needs a {status} row")


def mutants(good: Inputs) -> dict[str, Inputs]:
    """Known-bad copies of the inputs, each with one defect the checks must report."""
    cases: dict[str, Inputs] = {}

    def with_rows(rows: list[list[str]]) -> Inputs:
        return replace(good, rows=rows)

    def edit(index: int, column: int, value: str) -> Inputs:
        rows = [list(row) for row in good.rows]
        rows[index][column] = value
        return with_rows(rows)

    lean_row, lean_path, lean_name = first_proof(good, ".lean")
    rocq_row, rocq_path, rocq_name = first_proof(good, ".v")
    proved = find_row(good, "proved")
    owed = find_row(good, "owed")
    none = find_row(good, "no-proof-owed")
    lean_placed = find_row(good, "partial", "lean")
    proof = good.rows[proved][6]
    cases["a wrong header"] = with_rows([[*good.rows[0][:-1], "notes"], *good.rows[1:]])
    cases["a row of seven columns"] = with_rows([*good.rows, good.rows[1][:-1]])
    swapped = [list(row) for row in good.rows]
    swapped[1], swapped[2] = swapped[2], swapped[1]
    cases["sources out of order"] = with_rows(swapped)
    cases["a repeated source"] = with_rows([*good.rows[:2], list(good.rows[1]), *good.rows[2:]])
    cases["a source of no repository"] = edit(1, 0, "gororoba-other:" + good.rows[1][0].split(":", 1)[1])
    cases["an empty statement"] = edit(1, 1, "")
    cases["a statement of 31 words"] = edit(1, 1, " ".join(["word"] * (MAX_STATEMENT_WORDS + 1)))
    cases["a quantifier outside the enumeration"] = edit(1, 2, "every level")
    cases["a fixed-dimension quantifier without its number"] = edit(1, 2, "fixed-dimension")
    cases["a placement outside the enumeration"] = edit(1, 3, "either")
    cases["a clause outside the list"] = edit(1, 4, "Placed by the author")
    cases["a clause that decides another placement"] = edit(lean_placed, 4, OUTSIDE)
    cases["a status outside the enumeration"] = edit(1, 5, "done")
    cases["a proved row without a proof"] = edit(proved, 6, "-")
    cases["an owed row with a proof"] = edit(owed, 6, proof)
    cases["a no-proof-owed row with a proof"] = edit(none, 6, proof)
    cases["placement none with the status owed"] = edit(none, 5, "owed")
    cases["status no-proof-owed with a Lean placement"] = edit(none, 3, "lean")
    cases["an empty note"] = edit(1, 7, "")
    cases["a proof entry without a name"] = edit(proved, 6, proof.split(";")[0].rsplit(":", 1)[0])
    cases["a proof entry in an untracked module"] = edit(proved, 6, "lean/GororobaMath/Missing.lean:missing")
    cases["a proof entry outside the trees"] = edit(proved, 6, "docs/README.md:missing")
    cases["a Lean proof entry whose declaration is missing"] = edit(lean_row, 6, f"{lean_path}:{lean_name}_missing")
    cases["a Rocq proof entry whose theorem is missing"] = edit(rocq_row, 6, f"{rocq_path}:{rocq_name}_missing")
    short = lean_name.rsplit(".", 1)[-1]
    renamed = good.lean[lean_path].replace(short, short + "_gone")
    cases["a Lean declaration renamed in its source"] = replace(good, lean={**good.lean, lean_path: renamed})
    commented = "/- " + good.lean[lean_path] + " -/"
    cases["a Lean module that a block comment holds"] = replace(good, lean={**good.lean, lean_path: commented})
    quoted = "(* " + good.rocq[rocq_path] + " *)"
    cases["a Rocq source that a block comment holds"] = replace(good, rocq={**good.rocq, rocq_path: quoted})
    projects = {tree: set(files) for tree, files in good.projects.items()}
    tree = "/".join(rocq_path.split("/")[:2])
    projects[tree].discard(rocq_path[len(tree) + 1 :])
    cases["a Rocq proof source the project file omits"] = replace(good, projects=projects)
    head, first, second, rest = good.unlinked[0], good.unlinked[1], good.unlinked[2], good.unlinked[3:]
    missing = [head, [first[0], "rocq/open/theories/Missing.v"]]
    cases["a listed file that no project lists"] = replace(good, unlinked=missing)
    extra = [*good.unlinked, ["gororoba-open:zzz", first[1]]]
    cases["a listed source that the ledger lacks"] = replace(good, unlinked=extra)
    cases["listed sources out of order"] = replace(good, unlinked=[head, second, first, *rest])
    cases["a list header that is wrong"] = replace(good, unlinked=[["source", "file"], first, second, *rest])
    return cases


def controls(good: Inputs) -> dict[str, Inputs]:
    """Known-good copies that stress the lexers; each must add no failure to those of the repository inputs."""
    _, lean_path, _ = first_proof(good, ".lean")
    _, rocq_path, _ = first_proof(good, ".v")
    cases: dict[str, Inputs] = {}
    lean = {**good.lean, lean_path: LEAN_EXTRA + good.lean[lean_path]}
    cases["Lean string and comment text that holds delimiters"] = replace(good, lean=lean)
    rocq = {**good.rocq, rocq_path: ROCQ_EXTRA + good.rocq[rocq_path]}
    cases["Rocq comments, strings and blocks before the proof"] = replace(good, rocq=rocq)
    cases["the ledger rows read back unchanged"] = replace(good, rows=[list(row) for row in good.rows])
    return cases


def main() -> int:
    try:
        good = read_inputs()
    except (OSError, ValueError) as error:
        print(f"check_claims_ledger: {error}", file=sys.stderr)
        return 2
    if len(good.rows) < 4 or len(good.unlinked) < 4:
        print("check_claims_ledger: the calibration needs at least three rows in each table", file=sys.stderr)
        return 2
    baseline = check(good)
    for label, bad in mutants(good).items():
        if not check(bad):
            print(f"check_claims_ledger: calibration accepted {label}", file=sys.stderr)
            return 2
    for label, fine in controls(good).items():
        added = [failure for failure in check(fine) if failure not in baseline]
        if added:
            print(f"check_claims_ledger: calibration rejected {label}: {added[0]}", file=sys.stderr)
            return 2
    for failure in baseline:
        print(failure, file=sys.stderr)
    if baseline:
        return 1
    print(f"check_claims_ledger: {len(good.rows) - 1} ledger rows match the library and the Rocq trees")
    return 0


if __name__ == "__main__":
    sys.exit(main())
