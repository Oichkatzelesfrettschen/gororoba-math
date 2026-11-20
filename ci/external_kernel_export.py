"""Check that a lean4export NDJSON file is the export the caller asked for.

Usage: python3 ci/external_kernel_export.py EXPORT.ndjson THEOREM...

Rebuilds the declaration names of the export from its name records and
requires each THEOREM to be declared as a theorem in it, the export to declare
no axiom other than propext, Classical.choice and Quot.sound (an external
checker accepts a declared axiom as part of the environment it checks), and the
export to declare at least one declaration. Prints the declaration count and
the axioms on success.

Exit status: 0 the export matches, 1 it does not, 2 it cannot be read.
"""

import json
import sys

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
DECLARATION_KINDS = ("thm", "def", "axiom", "opaque", "inductive", "quot")


def main(argv: list[str]) -> int:
    if len(argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    path, wanted = argv[1], argv[2:]
    names: dict[int, str] = {0: ""}
    declared: dict[str, str] = {}
    try:
        with open(path, encoding="utf-8") as handle:
            for line in handle:
                record = json.loads(line)
                if "in" in record:
                    part = record.get("str") or record.get("num")
                    if part is None:
                        raise ValueError(f"name record without str or num: {line.strip()}")
                    prefix = names[part["pre"]]
                    text = str(part["str"] if "str" in part else part["i"])
                    names[record["in"]] = f"{prefix}.{text}" if prefix else text
                    continue
                for kind in DECLARATION_KINDS:
                    if kind in record and isinstance(record[kind], dict) and "name" in record[kind]:
                        declared[names[record[kind]["name"]]] = kind
    except (OSError, ValueError, KeyError) as error:
        print(f"external_kernel_export: cannot read {path}: {error}", file=sys.stderr)
        return 2
    problems = []
    for theorem in wanted:
        if declared.get(theorem) != "thm":
            problems.append(f"{theorem} is not declared as a theorem")
    axioms = sorted(name for name, kind in declared.items() if kind == "axiom")
    extra = [name for name in axioms if name not in ALLOWED_AXIOMS]
    if extra:
        problems.append("axioms outside the allow list: " + ", ".join(extra))
    if not declared:
        problems.append("no declaration")
    if problems:
        for problem in problems:
            print(f"external_kernel_export: {path}: {problem}", file=sys.stderr)
        return 1
    print(f"{len(declared)} declarations; axioms: {', '.join(axioms) or 'none'}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
