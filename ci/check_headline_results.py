"""Headline-result registry check: ci/headline-results.tsv against the library, README.md and the Rocq trees.

Usage:

    "$PYTHON" -I ci/check_headline_results.py

A headline result is a row of ci/headline-results.tsv (AGENTS.md, "Statements
and proofs"). The columns are prover, path, theorem, partner and tracking. This
script checks, from the repository root it sits under:

1. Each row of prover lean names a tracked file under lean/GororobaMath/ that
   declares the theorem: a theorem or lemma command whose name, prefixed by
   the namespaces open at that command, is the row's theorem. The scan lexes
   the file first: line comments, nested block comments (docstrings
   included), string literals and character literals hold no declaration;
   mutual blocks and sections close with their own end; a private
   declaration has no public name and counts for nothing. A (path, theorem)
   pair appears in one row at most.
2. The rows of prover lean are exactly the theorems the "Lean library" table
   of README.md names: each backquoted identifier in the Result column of a
   module's row names a declaration of that module (by its full name, or by a
   suffix that starts after a dot) or appears in NON_DECLARATION_TOKENS with
   its reason; each identifier that names a theorem has a row with that
   module's path, and each row's theorem is named so in the table of its
   module. A module has one row in the table, and a table row is recognized
   after its leading whitespace. A NON_DECLARATION_TOKENS entry that the
   table no longer holds is an error.
3. The partner column is owed, with an issue URL in the tracking column, or
   PATH:NAME, optionally followed by " narrower: REASON". PATH is a source
   listed in the _RocqProject of its tree (rocq/open, rocq/quantum or
   rocq/delegation), and the source holds a Theorem, Lemma, Corollary,
   Proposition, Fact or Remark command named by the last component of NAME,
   inside a Module named by each earlier component. The scan lexes the source
   first: nested comments and string literals (a doubled quote stays inside
   the string) hold no command; a Module Type block and a Local theorem
   contribute no name; the theorem counts when its proof ends with Qed or
   Defined, or when it is given by a term with :=, and an Abort or Admitted
   ending does not count.

Calibration. Before the verdict on the repository counts, the script runs the
same checks on known-bad copies of the inputs, one per defect class above
(the mutants function lists them), and requires each to fail; it runs them on
known-good copies that stress the lexers (the controls function) and requires
each to pass; and it runs them on the repository inputs.

Exit status: 0 every check passed; 1 a check failed (each failure printed);
2 the calibration failed or an input is unreadable.
"""

from __future__ import annotations

import re
import subprocess
import sys
from dataclasses import dataclass, field, replace
from functools import cache
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
HEADER = ["prover", "path", "theorem", "partner", "tracking"]
ISSUE_URL = re.compile(r"^https://github\.com/Oichkatzelesfrettschen/gororoba-math/issues/[0-9]+$")
PARTNER = re.compile(r"^(rocq/(?:open|quantum|delegation)/[A-Za-z0-9_/]+\.v):([A-Za-z0-9_.']+)(?: narrower: (.+))?$")
LEAN_DECL = re.compile(
    r"^\s*(?P<attrs>(?:@\[[^\]]*\]\s*)*)"
    r"(?P<mods>(?:(?:private|protected|noncomputable|public|nonrec|unsafe|partial)\s+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\s+(?P<name>[^\s:({\[]+)"
)
LEAN_NAMESPACE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.']+)\s*$")
LEAN_SECTION = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|public|meta)\s+)*section(?:\s+([A-Za-z0-9_.']+))?\s*$"
)
LEAN_MUTUAL = re.compile(r"^\s*mutual\s*$")
LEAN_END = re.compile(r"^\s*end(?:\s+([A-Za-z0-9_.']+))?\s*$")
LEAN_CHAR = re.compile(r"'(?:[^\\'\n]|\\x[0-9A-Fa-f]{2}|\\u\{?[0-9A-Fa-f]+\}?|\\.)'")
LEAN_RAW_STRING = re.compile(r"r(#*)\"")
ROCQ_THEOREMS = ("Theorem", "Lemma", "Corollary", "Proposition", "Fact", "Remark")
ROCQ_THEOREM = re.compile(r"^(?:" + "|".join(ROCQ_THEOREMS) + r")\s+([A-Za-z0-9_']+)")
ROCQ_MODULE = re.compile(r"^Module\s+((?:(?:Import|Export|Type)\s+)*)([A-Za-z0-9_']+)")
ROCQ_PREFIX = re.compile(
    r"^(?:#\[(?P<attrs>[^\]]*)\]\s*|(?P<word>Local|Global|Polymorphic|Monomorphic|Private|Program)\s+)"
)
TOKEN = re.compile(r"\x60([^\x60]+)\x60")
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_.']*$")

# Identifier-shaped tokens of a README Result cell that are mathematics or code text, not declaration names:
# (module path, token) -> reason. Every other identifier token of the table resolves to a declaration of its module.
NON_DECLARATION_TOKENS: dict[tuple[str, str], str] = {
    ("lean/GororobaMath/CayleyDickson/AlignedPairClosedForm.lean", "m'"): "the masked index of the closed form",
    ("lean/GororobaMath/CayleyDickson/AlignedPairSpectrum.lean", "j"): "a bound variable of the statement text",
    ("lean/GororobaMath/CayleyDickson/AlignedPairSpectrum.lean", "n"): "a bound variable of the statement text",
    ("lean/GororobaMath/CayleyDickson/AnnihilatorSymmetry.lean", "k"): "the level, a bound variable",
    ("lean/GororobaMath/CayleyDickson/NonAssociative.lean", "k"): "the level, a bound variable",
    ("lean/GororobaMath/CayleyDickson/Tower.lean", "k"): "the level, a bound variable",
    ("lean/GororobaMath/CayleyDickson/Tower.lean", "A_5"): "the 32-dimensional algebra, mathematical notation",
    ("lean/GororobaMath/CayleyDickson/TowerModule.lean", "R"): "the coefficient ring, a bound variable",
    ("lean/GororobaMath/CayleyDickson/TowerModule.lean", "e_p"): "a basis element, mathematical notation",
    ("lean/GororobaMath/CayleyDickson/TwoTerm.lean", "A_5"): "the 32-dimensional algebra, mathematical notation",
    ("lean/GororobaMath/CayleyDickson/TwoTermNullity.lean", "A_5"): "the 32-dimensional algebra, mathematical notation",
    ("lean/GororobaMath/CayleyDickson/TwoTermRecursion.lean", "alignedPairCount"): "declared in CayleyDickson.TwoTerm",
    ("lean/GororobaMath/CayleyDickson/TwoTermRecursion.lean", "a"): "a bound variable of the statement text",
    ("lean/GororobaMath/CayleyDickson/TwoTermRecursion.lean", "b"): "a bound variable of the statement text",
    ("lean/GororobaMath/CayleyDickson/TwoTermRecursion.lean", "i"): "a bound variable of the statement text",
    ("lean/GororobaMath/CayleyDickson/TwoTermRecursion.lean", "j"): "a bound variable of the statement text",
    ("lean/GororobaMath/CayleyDickson/TwoTermRecursion.lean", "k"): "a bound variable of the statement text",
    ("lean/GororobaMath/CayleyDickson/TwoTermRecursion.lean", "e_0"): "the basis element of index 0",
    ("lean/GororobaMath/KernelMap/Estimator.lean", "V_hat"): "the observed contrast scale, mathematical notation",
}


@dataclass
class Inputs:
    rows: list[list[str]]
    readme: str
    lean: dict[str, str]
    rocq: dict[str, str]
    projects: dict[str, set[str]] = field(default_factory=dict)
    exempt: dict[tuple[str, str], str] = field(default_factory=lambda: dict(NON_DECLARATION_TOKENS))


def blank(chunk: str) -> str:
    """The chunk with every character but a newline replaced by a space, so that positions and lines stay put."""
    return "".join(c if c == "\n" else " " for c in chunk)


def lean_code(text: str) -> str:
    """The Lean text with comments, string literals and character literals blanked, position for position."""
    out: list[str] = []
    i, n, depth = 0, len(text), 0
    while i < n:
        c = text[i]
        after_ident = i > 0 and (text[i - 1].isalnum() or text[i - 1] in "_'")
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append(blank(c))
                i += 1
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = n if end < 0 else end
            out.append(blank(text[i:end]))
            i = end
        elif text.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
        elif c == '"' or (not after_ident and (raw := LEAN_RAW_STRING.match(text, i))):
            if c == '"':
                end, quote = i + 1, '"'
                while end < n and text[end] != '"':
                    end += 2 if text[end] == "\\" else 1
            else:
                quote = '"' + raw.group(1)
                end = text.find(quote, raw.end())
                end = n if end < 0 else end
            stop = min(n, end + len(quote))
            out.append(blank(text[i:stop]))
            i = stop
        elif c == "'" and not after_ident and (lit := LEAN_CHAR.match(text, i)):
            out.append(blank(lit.group(0)))
            i = lit.end()
        else:
            out.append(c)
            i += 1
    return "".join(out)


def lean_scan(text: str) -> list[tuple[str, str, bool, int]]:
    """(full name, kind, private, line index) of each declaration command of a Lean file, in order."""
    scopes: list[tuple[str, list[str]]] = []
    found: list[tuple[str, str, bool, int]] = []
    for number, line in enumerate(lean_code(text).splitlines()):
        match = LEAN_NAMESPACE.match(line)
        if match:
            scopes.append(("namespace", match.group(1).split(".")))
            continue
        if LEAN_SECTION.match(line):
            scopes.append(("section", []))
            continue
        if LEAN_MUTUAL.match(line):
            scopes.append(("mutual", []))
            continue
        if LEAN_END.match(line):
            if scopes:
                scopes.pop()
            continue
        match = LEAN_DECL.match(line)
        if match:
            name = match.group("name").rstrip(".")
            if name.startswith("_root_."):
                full = name[len("_root_.") :]
            else:
                full = ".".join([*[part for _, parts in scopes for part in parts], name])
            found.append((full, match.group("kind"), "private" in match.group("mods").split(), number))
    return found


@cache
def lean_declarations(text: str) -> dict[str, str]:
    """Full name to kind ('theorem' for theorem and lemma) of each public declaration of a Lean file."""
    return {
        full: "theorem" if kind in ("theorem", "lemma") else kind
        for full, kind, private, _ in lean_scan(text)
        if not private
    }


def rocq_sentences(text: str) -> list[str]:
    """The commands of a Rocq file: comments dropped, string literals reduced to two quotes, split at '. '."""
    sentences: list[str] = []
    current: list[str] = []
    i, n, depth = 0, len(text), 0

    def string_end(start: int) -> int:
        j = start + 1
        while j < n:
            if text[j] == '"':
                if j + 1 < n and text[j + 1] == '"':
                    j += 2
                    continue
                return j + 1
            j += 1
        return n

    while i < n:
        c = text[i]
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
            if not depth:
                current.append(" ")
        elif c == '"':
            i = string_end(i)
            if not depth:
                current.append('""')
        elif depth:
            i += 1
        elif c == "." and (i + 1 >= n or text[i + 1].isspace()) and not (i and text[i - 1] == "."):
            sentences.append("".join(current).strip() + ".")
            current = []
            i += 1
        else:
            current.append(c)
            i += 1
    return sentences


def has_term_body(sentence: str) -> bool:
    """True when a theorem command carries its proof term: a := outside brackets that no let precedes."""
    depth = 0
    for index, char in enumerate(sentence):
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif char == ":" and not depth and sentence.startswith(":=", index):
            return re.search(r"\blet\b", sentence[:index]) is None
    return False


@cache
def rocq_theorems(text: str) -> set[str]:
    """Names Module.Sub.name of the proved theorem-like commands of a Rocq file, with every enclosing module prefix."""
    names: set[str] = set()
    stack: list[tuple[str, str]] = []
    pending: str | None = None
    for sentence in rocq_sentences(text):
        local = False
        while True:
            prefix = ROCQ_PREFIX.match(sentence)
            if not prefix:
                break
            attrs = prefix.group("attrs") or ""
            local = local or prefix.group("word") == "Local" or re.search(r"\blocal\b", attrs) is not None
            sentence = sentence[prefix.end() :]
        word = re.match(r"[A-Za-z]+", sentence)
        keyword = word.group(0) if word else ""
        theorem = ROCQ_THEOREM.match(sentence)
        if theorem:
            full = ".".join([*[name for kind, name in stack if kind != "section"], theorem.group(1)])
            hidden = local or any(kind == "type" for kind, _ in stack)
            pending = None if hidden else full
            if pending and has_term_body(sentence):
                names.add(pending)
                pending = None
        elif keyword in ("Qed", "Defined"):
            if pending:
                names.add(pending)
            pending = None
        elif keyword in ("Admitted", "Abort"):
            pending = None
        elif keyword == "Module":
            module = ROCQ_MODULE.match(sentence)
            if module and ":=" not in sentence:
                stack.append(("type" if "Type" in module.group(1).split() else "module", module.group(2)))
        elif keyword == "Section":
            section = re.match(r"Section\s+([A-Za-z0-9_']+)", sentence)
            if section:
                stack.append(("section", section.group(1)))
        elif keyword == "End":
            end = re.match(r"End\s+([A-Za-z0-9_']+)", sentence)
            if end and stack and stack[-1][1] == end.group(1):
                stack.pop()
                pending = None
    return names


def readme_table(readme: str) -> tuple[dict[str, list[str]], list[str]]:
    """Module path to the backquoted tokens of its Result column in the Lean library table, and the layout errors."""
    table: dict[str, list[str]] = {}
    errors: list[str] = []
    inside = False
    for raw in readme.splitlines():
        line = raw.strip()
        if line.startswith("## "):
            inside = line == "## Lean library"
            continue
        if not inside or not line.startswith("| \x60GororobaMath."):
            continue
        cells = [cell.strip() for cell in re.split(r"(?<!\\)\|", line.strip("|"))]
        module = cells[0].strip("\x60")
        path = "lean/" + module.replace(".", "/") + ".lean"
        if path in table:
            errors.append(f"README.md: the Lean library table has two rows for {module}")
            continue
        table[path] = TOKEN.findall(cells[1])
    return table, errors


def check(inputs: Inputs) -> list[str]:
    failures: list[str] = []
    if not inputs.rows or inputs.rows[0] != HEADER:
        return ["ci/headline-results.tsv: the header is not " + "\t".join(HEADER)]
    table, failures = readme_table(inputs.readme)
    declared = {path: lean_declarations(text) for path, text in inputs.lean.items()}
    proved = {path: rocq_theorems(text) for path, text in inputs.rocq.items()}
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
        if (path, theorem) in lean_rows:
            failures.append(f"{where}: {theorem} of {path} has a row already")
        lean_rows.add((path, theorem))
        if path not in declared:
            failures.append(f"{where}: {path} is not a tracked module under lean/GororobaMath/")
        elif declared[path].get(theorem) != "theorem":
            failures.append(f"{where}: {path} declares no public theorem {theorem}")
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
        elif name not in proved.get(source, set()):
            failures.append(f"{where}: {source} holds no theorem {name} that ends in Qed or Defined")
    for path, tokens in sorted(table.items()):
        names = declared.get(path)
        if names is None:
            failures.append(f"README.md: the Lean library table names {path}, which is not a tracked module")
            continue
        for token in tokens:
            if not IDENT.match(token):
                continue
            hits = [full for full in names if full == token or full.endswith("." + token)]
            if not hits and (path, token) not in inputs.exempt:
                failures.append(f"README.md: {token} in the row of {path} names no declaration of that module")
            for full in hits:
                if names[full] == "theorem" and (path, full) not in lean_rows:
                    failures.append(f"README.md: {full} ({path}) is a theorem the table names and has no row")
    for path, token in sorted(inputs.exempt):
        if token not in table.get(path, []):
            failures.append(f"NON_DECLARATION_TOKENS: {token} is not in the README row of {path}")
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


@dataclass
class Sites:
    """Places of the repository inputs that the calibration copies edit."""

    first: list[str]
    lean_lines: list[str]
    lean_index: int
    lean_name: re.Match[str]
    partner_row: list[str]
    partner_index: int
    partner_source: str
    partner_last: str
    partner_start: int
    partner_end: re.Match[str]


def find_sites(good: Inputs) -> Sites:
    first = good.rows[1]
    lines = good.lean[first[1]].splitlines()
    code = lean_code(good.lean[first[1]]).splitlines()
    scan = [entry for entry in lean_scan(good.lean[first[1]]) if entry[0] == first[2] and not entry[2]]
    owed = any(r[3] == "owed" for r in good.rows[1:])
    if not scan or not owed:
        raise SystemExit("check_headline_results: calibration needs a Lean row with a declaration and one owed row")
    index = scan[0][3]
    name = LEAN_DECL.match(code[index])
    for position, row in enumerate(good.rows[1:], start=1):
        partner = PARTNER.match(row[3])
        if not partner:
            continue
        last = partner.group(2).rsplit(".", 1)[-1]
        text = good.rocq[partner.group(1)]
        start = re.search(r"^[ \t]*(?:" + "|".join(ROCQ_THEOREMS) + r")\s+" + re.escape(last) + r"\b", text, re.M)
        end = re.compile(r"\b(?:Qed|Defined)\s*\.").search(text, start.end()) if start else None
        if start and end and partner.group(2) in rocq_theorems(text):
            return Sites(first, lines, index, name, row, position, partner.group(1), last, start.start(), end)
    raise SystemExit("check_headline_results: calibration needs a partner row whose theorem ends in Qed or Defined")


def mutants(good: Inputs) -> dict[str, Inputs]:
    """Known-bad copies of the inputs, each with one defect the checks must report."""
    site = find_sites(good)
    cases: dict[str, Inputs] = {}

    def with_rows(rows: list[list[str]]) -> Inputs:
        return replace(good, rows=[list(r) for r in rows])

    def edit_row(index: int, column: int, value: str) -> list[list[str]]:
        rows = [list(r) for r in good.rows]
        rows[index][column] = value
        return rows

    def with_lean(before: list[str], rename: bool = False, private: bool = False) -> Inputs:
        lines = list(site.lean_lines)
        line, match = lines[site.lean_index], site.lean_name
        if rename:
            line = line[: match.end("name")] + "_renamed" + line[match.end("name") :]
        if private:
            line = line[: match.start("kind")] + "private " + line[match.start("kind") :]
        lines[site.lean_index : site.lean_index + 1] = [*before, line]
        return replace(
            good, rows=[list(r) for r in good.rows], lean={**good.lean, site.first[1]: "\n".join(lines) + "\n"}
        )

    def with_rocq(rewrite: str, row: list[list[str]] | None = None) -> Inputs:
        return replace(
            good,
            rows=[list(r) for r in (row if row is not None else good.rows)],
            rocq={**good.rocq, site.partner_source: rewrite},
        )

    text = good.rocq[site.partner_source]
    block = text[site.partner_start : site.partner_end.end()]
    renamed = block.replace(site.partner_last, site.partner_last + "_renamed", 1)
    head, tail = text[: site.partner_start], text[site.partner_end.end() :]

    rows = [list(r) for r in good.rows]
    rows[1][2] = site.first[2] + "_missing"
    cases["a row whose theorem the file lacks"] = with_rows(rows)
    cases["a README theorem without a row"] = with_rows([good.rows[0], *good.rows[2:]])
    cases["a partner whose theorem the source lacks"] = with_rows(
        edit_row(site.partner_index, 3, site.partner_row[3].split(" ")[0] + "_missing")
    )
    tree = "/".join(site.partner_source.split("/")[:2])
    projects = {k: set(v) for k, v in good.projects.items()}
    projects[tree].discard(site.partner_source[len(tree) + 1 :])
    cases["a partner source the project file omits"] = replace(good, projects=projects)
    owed = next(i for i, r in enumerate(good.rows) if i and r[3] == "owed")
    cases["an owed row without an issue URL"] = with_rows(edit_row(owed, 4, "-"))
    extra = "calibration_unlisted"
    unlisted = with_lean([f"theorem {extra} : True := trivial"])
    unlisted.rows.append(
        [
            "lean",
            site.first[1],
            site.first[2].rsplit(".", 1)[0] + "." + extra if "." in site.first[2] else extra,
            "owed",
            good.rows[owed][4],
        ]
    )
    cases["a registry row that README does not name"] = unlisted

    def with_token(token: str, indent: bool = False) -> Inputs:
        marker = "| \x60GororobaMath.CayleyDickson.Tower\x60 | "
        if marker not in good.readme:
            raise SystemExit("check_headline_results: calibration needs the Tower row of the README table")
        row = marker + "\x60" + token + "\x60, "
        readme = good.readme.replace(marker, ("  " if indent else "") + row, 1)
        return replace(good, readme=readme)

    cases["a README short dotted misspelling"] = with_token("Tower.e_mul_e_typo")
    cases["a README GororobaMath-qualified misspelling"] = with_token("GororobaMath.CayleyDickson.Tower.e_mul_e_typo")
    cases["a README dotless misspelling"] = with_token("e_mul_e_typo")
    cases["an indented README row with a misspelling"] = with_token("e_mul_e_typo", indent=True)
    row_lines = good.readme.splitlines()
    duplicate = next(i for i, line in enumerate(row_lines) if line.startswith("| \x60GororobaMath."))
    row_lines.insert(duplicate + 1, row_lines[duplicate])
    cases["a repeated README module row"] = replace(good, readme="\n".join(row_lines) + "\n")
    cases["a repeated registry row"] = with_rows([*good.rows, [*good.rows[1][:3], "owed", good.rows[owed][4]]])
    cases["a stale NON_DECLARATION_TOKENS entry"] = replace(
        good, exempt={**good.exempt, (site.first[1], "calibration_absent"): "calibration"}
    )

    cases["a Rocq partner theorem that only a block comment holds"] = with_rocq(
        head + "(* " + block + " *)\n" + renamed + tail
    )
    cases["a Rocq partner theorem ending in Abort"] = with_rocq(
        head + block[: -len(site.partner_end.group(0))] + "Abort." + tail
    )
    cases["a Rocq partner theorem ending in Admitted"] = with_rocq(
        head + block[: -len(site.partner_end.group(0))] + "Admitted." + tail
    )
    qualified = site.partner_row[3].split(":")[1].split(" ")[0]
    inner = qualified.rsplit(".", 1)
    moved = ".".join([*inner[:-1], "CalibrationT", site.partner_last])
    cases["a Rocq partner theorem that only a Module Type holds"] = with_rocq(
        head + "Module Type CalibrationT.\n" + block + "\nEnd CalibrationT.\n" + tail,
        edit_row(site.partner_index, 3, site.partner_row[3].replace(qualified, moved, 1)),
    )

    cases["a Lean theorem inside a block comment"] = with_lean(
        ["/-", f"theorem {site.lean_name.group('name')} : True := trivial", "-/"], rename=True
    )
    cases["a Lean theorem inside a block comment after a line comment that holds both delimiters"] = with_lean(
        ["-- /- -/ -/", "/-", f"theorem {site.lean_name.group('name')} : True := trivial", "-/"], rename=True
    )
    cases["a Lean theorem inside nested docstring comments"] = with_lean(
        ["/-- doc /- nested -/ text", f"theorem {site.lean_name.group('name')} : True := trivial", "-/"], rename=True
    )
    cases["a Lean private theorem with the row's name"] = with_lean([], private=True)
    return cases


def controls(good: Inputs) -> dict[str, Inputs]:
    """Known-good copies that stress the lexers; each must pass every check."""
    site = find_sites(good)
    lean_before = {
        "a Lean mutual block before the theorem": ["mutual", "def calibrationDummy : Nat := 0", "end"],
        "Lean string, character and comment text that holds delimiters": [
            'def calibrationString : String := "/- \\" -/ -- \\\\"',
            "def calibrationChar : Char := '\"'",
            "-- /- a line comment that opens a block",
        ],
    }
    cases: dict[str, Inputs] = {}
    for label, before in lean_before.items():
        lines = list(site.lean_lines)
        lines[site.lean_index : site.lean_index] = before
        cases[label] = replace(good, lean={**good.lean, site.first[1]: "\n".join(lines) + "\n"})
    text = good.rocq[site.partner_source]
    insert = (
        "(* Module Bogus. Theorem fake : True. Proof. Qed. *)\n"
        'Definition calibration_string := "say ""(*"" and ""*)"" ".\n'
        "Module Type CalibrationT.\n  Parameter calibration_p : nat.\nEnd CalibrationT.\n"
        "Section CalibrationS.\nEnd CalibrationS.\n"
    )
    cases["Rocq comments, strings and blocks around the partner theorem"] = replace(
        good, rocq={**good.rocq, site.partner_source: text[: site.partner_start] + insert + text[site.partner_start :]}
    )
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
    for label, fine in controls(good).items():
        failures = check(fine)
        if failures:
            print(f"check_headline_results: calibration rejected {label}: {failures[0]}", file=sys.stderr)
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
