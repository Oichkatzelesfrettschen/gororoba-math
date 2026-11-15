"""Census of the theorems of rocq/open/verified whose statement names no project constant.

Usage, with the `rocq` of Rocq 9.3.0 on PATH (for example under
`opam exec --switch=rocq-9.3 --`) and a compiled tree of rocq/open, such as the
`rocq/open` directory that `make rocq-open` builds under `BUILD_DIR`:

    opam exec --switch=rocq-9.3 -- "$PYTHON" -I ci/theorem_census.py \\
        --objects "$BUILD_DIR/rocq/open" [--tsv FILE]

Criterion. A declaration counts as listed when the type that Rocq prints for it
refers to no constant, inductive type or constructor of the logical roots
OpenGororoba and OpenGororobaVerified. The type comes from `Check` on the
compiled object with `Set Printing All` (notations, coercions and implicit
arguments shown) and `Set Printing Fully Qualified`, so every project name
appears with its root and a notation or coercion cannot hide one. The proof is
not read: `Print Assumptions` is not the criterion, since it follows the proof
term. The script reads the source only to find the names of the declarations
(Theorem, Lemma, Corollary, Fact, Proposition, Example, outside comments and
strings) and the statement text shown in the table.

Coherence. The compiled tree holds a copy of every source. Each copy must equal the
file of --tree byte for byte and its object must not be older than the copy; the
declaration names and statement text come from the copy, so they describe the
object that Rocq prints.

Scope. A declaration is listed when it names no project constant, whatever it claims:
a theorem over a definition local to its own file is not listed (the local
definition is a project constant), and a theorem over standard-library names alone is
listed even when it states the file's claim. The list bounds where a statement
carries no project content; it does not decide whether a header overclaims.
Declarations of other kinds (Definition, Remark) are not read.

Calibration. Every run checks four declarations against the criterion before it
reports: C029_three_embeddings and C029_s3_order of C029_FermionGenerations are
listed, chern_sum_zero_under_trs of C1233_ChernSumZero and
C028_lo_subalgebra_closed of C028_SedenionAutGroup are not. A different verdict,
a missing declaration, an object missing for a listed source, a Rocq error or
any stderr output exits 1.

Output. Stdout gets one line per source file with its count of listed and of
all declarations, then the total. `--tsv FILE` writes the listed declarations as
file, theorem and statement columns.
"""

import argparse
import os
import re
import subprocess  # noqa: S404 - the census runs the pinned rocq on a compiled tree
import sys
import tempfile
from pathlib import Path

ROOT_REFERENCE = re.compile(r"\bOpenGororoba(?:Verified)?\.[A-Za-z_]")
DECLARATION = re.compile(
    r"(?m)^[ \t]*(?:(?:#\[[^\]]*\]|Local|Global)[ \t]+)*"
    r"(Theorem|Lemma|Corollary|Fact|Proposition|Example)[ \t]+([A-Za-z_][A-Za-z0-9_']*)"
)
CALIBRATION_LISTED = (
    ("C029_FermionGenerations", "C029_three_embeddings"),
    ("C029_FermionGenerations", "C029_s3_order"),
)
CALIBRATION_UNLISTED = (
    ("C1233_ChernSumZero", "chern_sum_zero_under_trs"),
    ("C028_SedenionAutGroup", "C028_lo_subalgebra_closed"),
)


class CensusError(Exception):
    """A condition under which no verdict is given."""


def strip_comments_and_strings(text: str) -> str:
    """Return the text with comments (nested) and string literals blanked, newlines kept."""
    out: list[str] = []
    depth = 0
    in_string = False
    i = 0
    while i < len(text):
        two = text[i : i + 2]
        ch = text[i]
        if in_string:
            if ch == '"':
                in_string = False
            out.append("\n" if ch == "\n" else " ")
        elif depth > 0:
            if ch == '"':
                in_string = True
                out.append(" ")
            elif two == "(*":
                depth += 1
                out.append("  ")
                i += 1
            elif two == "*)":
                depth -= 1
                out.append("  ")
                i += 1
            else:
                out.append("\n" if ch == "\n" else " ")
        elif two == "(*":
            depth = 1
            out.append("  ")
            i += 1
        elif ch == '"':
            in_string = True
            out.append(" ")
        else:
            out.append(ch)
        i += 1
    return "".join(out)


def statement_text(stripped: str, start: int) -> str:
    """Source statement from `start` to the first sentence-ending period, whitespace collapsed."""
    match = re.compile(r"\.(?=\s|$)").search(stripped, start)
    end = match.start() if match else len(stripped)
    return " ".join(stripped[start:end].split())


def verified_sources(project: Path) -> list[str]:
    """Stems of the verified/ sources that the _RocqProject lists, in file order."""
    stems = []
    for line in project.read_text(encoding="utf-8").splitlines():
        entry = line.strip()
        if entry.startswith("verified/") and entry.endswith(".v"):
            stems.append(entry[len("verified/") : -len(".v")])
    if not stems:
        raise CensusError(f"{project} lists no verified/ source")
    return stems


def check_coherence(tree: Path, objects: Path, stems: list[str]) -> None:
    """Require that each compiled object comes from the checkout's source bytes.

    The compiled tree carries its own copy of every source. The copy must equal the
    checkout's file, and its object must not be older than the copy, so the printed
    type and the statement text describe one source.
    """
    for stem in stems:
        checkout = tree / "verified" / f"{stem}.v"
        copy = objects / "verified" / f"{stem}.v"
        obj = objects / "verified" / f"{stem}.vo"
        if not copy.is_file() or not obj.is_file():
            raise CensusError(f"no compiled source and object for verified/{stem} under {objects}")
        if copy.read_bytes() != checkout.read_bytes():
            raise CensusError(f"verified/{stem}.v differs between {tree} and {objects}: rebuild the compiled tree")
        if obj.stat().st_mtime < copy.stat().st_mtime:
            raise CensusError(f"verified/{stem}.vo is older than its source under {objects}: rebuild the compiled tree")


def declarations(tree: Path, stems: list[str]) -> dict[str, list[tuple[str, str]]]:
    """Map each source stem to its (name, statement text) declarations."""
    found: dict[str, list[tuple[str, str]]] = {}
    for stem in stems:
        stripped = strip_comments_and_strings((tree / "verified" / f"{stem}.v").read_text(encoding="utf-8"))
        found[stem] = [(m.group(2), statement_text(stripped, m.end())) for m in DECLARATION.finditer(stripped)]
    return found


def flocq_root() -> Path:
    """Flocq library directory: FLOCQ_ROOT, else the prefix of the active opam switch."""
    named = os.environ.get("FLOCQ_ROOT")
    candidates = []
    if named:
        candidates.append(Path(named))
    prefix = os.environ.get("OPAM_SWITCH_PREFIX")
    if prefix:
        candidates.append(Path(prefix) / "lib" / "coq" / "user-contrib" / "Flocq")
    for candidate in candidates:
        if (candidate / "Core" / "Core.vo").is_file():
            return candidate
    raise CensusError("Flocq Core.vo not found: set FLOCQ_ROOT or run under opam exec --switch=rocq-9.3")


def run_checks(objects: Path, decls: dict[str, list[tuple[str, str]]]) -> dict[tuple[str, str], str]:
    """Run one Rocq driver over every declaration; return the printed type of each."""
    for stem in decls:
        if not (objects / "verified" / f"{stem}.vo").is_file():
            raise CensusError(f"no compiled object for verified/{stem}.v under {objects}")
    lines = [f"From OpenGororobaVerified Require {stem}." for stem in decls]
    lines += ["Set Printing All.", "Set Printing Fully Qualified.", "Set Printing Width 1000000."]
    order = []
    for stem, items in decls.items():
        for name, _ in items:
            lines.append(f"Check OpenGororobaVerified.{stem}.{name}.")
            order.append((stem, name))
    with tempfile.TemporaryDirectory(prefix="theorem-census-") as scratch:
        driver = Path(scratch) / "CensusDriver.v"
        driver.write_text("\n".join(lines) + "\n", encoding="utf-8")
        command = [
            "rocq",
            "compile",
            "-q",
            "-w",
            "none",
            "-R",
            str(objects / "theories"),
            "OpenGororoba",
            "-R",
            str(objects / "verified"),
            "OpenGororobaVerified",
            "-R",
            str(flocq_root()),
            "Flocq",
            str(driver),
        ]
        env = {k: v for k, v in os.environ.items() if k not in ("COQPATH", "ROCQPATH")}
        done = subprocess.run(command, capture_output=True, text=True, check=False, cwd=scratch, env=env)  # noqa: S603
    if done.returncode != 0 or done.stderr.strip():
        raise CensusError(f"rocq exit {done.returncode}\n{done.stdout[-2000:]}\n{done.stderr[-2000:]}")
    blocks: list[list[str]] = []
    for line in done.stdout.splitlines():
        if line and not line[0].isspace():
            blocks.append([line])
        elif blocks and line.strip():
            blocks[-1].append(line.strip())
        elif not blocks and line.strip():
            raise CensusError(f"unexpected Rocq output before the first block: {line}")
    if len(blocks) != len(order):
        raise CensusError(f"{len(order)} checks produced {len(blocks)} output blocks")
    types = {}
    for (stem, name), block in zip(order, blocks, strict=True):
        if block[0] != f"OpenGororobaVerified.{stem}.{name}":
            raise CensusError(f"output block {block[0]!r} does not match {stem}.{name}")
        types[(stem, name)] = " ".join(block[1:])
    return types


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--objects", required=True, type=Path, help="compiled rocq/open tree (theories/ and verified/)")
    parser.add_argument("--tree", type=Path, default=Path(__file__).resolve().parent.parent / "rocq" / "open")
    parser.add_argument("--tsv", type=Path, help="write the listed declarations (file, theorem, statement) here")
    args = parser.parse_args()
    try:
        stems = verified_sources(args.tree / "_RocqProject")
        check_coherence(args.tree, args.objects, stems)
        decls = declarations(args.objects, stems)
        types = run_checks(args.objects, decls)
        listed = {key: not ROOT_REFERENCE.search(text) for key, text in types.items()}
        for stem, name in CALIBRATION_LISTED:
            if listed.get((stem, name)) is not True:
                raise CensusError(f"calibration: {stem}.{name} must be listed, verdict {listed.get((stem, name))}")
        for stem, name in CALIBRATION_UNLISTED:
            if listed.get((stem, name)) is not False:
                raise CensusError(f"calibration: {stem}.{name} must be unlisted, verdict {listed.get((stem, name))}")
    except (CensusError, OSError) as error:
        print(f"theorem_census: {error}", file=sys.stderr)
        return 1
    rows = []
    total = 0
    for stem, items in decls.items():
        hits = [(name, text) for name, text in items if listed[(stem, name)]]
        rows += [(f"{stem}.v", name, text) for name, text in hits]
        total += len(items)
        print(f"{stem}.v\t{len(hits)}\t{len(items)}")
    print(f"total\t{len(rows)}\t{total}\t(listed, declarations; calibration passed)")
    if args.tsv:
        args.tsv.write_text("".join(f"{a}\t{b}\t{c}\n" for a, b, c in rows), encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
