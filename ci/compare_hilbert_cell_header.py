"""Helper of ci/compare_hilbert_cell_header.sh.

reference HEADER TABLES            parse the pinned canonical header and write its J and G tables as JSON
reference-unpinned HEADER TABLES   the same without the digest check, for the mutated copies
mutate HEADER OUT TABLE            copy the header with one coefficient of TABLE (J or G) changed
rocq TEXT TABLES                   read the Eval output of the J and G tables of a cell and write them as JSON
compare REFERENCE ROCQ             exit 0 when every polynomial agrees term by term, 1 on a difference

A table is a list of polynomials; a polynomial is a list of [exponents, coefficient] pairs, and the
comparison merges equal exponent vectors and drops terms whose coefficient is 0 modulo p.
"""

from __future__ import annotations

import hashlib
import json
import re
import sys
from pathlib import Path

HEADER_SHA256 = "6b3cea4923b4e0e2650349e64a83f902fcbbbe288ba364c685a552b03f9e82e0"
PRIME = 32029


def fail(message: str, status: int = 2) -> None:
    print(f"compare_hilbert_cell_header: {message}", file=sys.stderr)
    sys.exit(status)


def read_header(path: str, pinned: bool) -> tuple[list[str], list[str], list[str]]:
    data = Path(path).read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if pinned and digest != HEADER_SHA256:
        fail(f"header sha256 {digest} is not the pinned {HEADER_SHA256}")
    text = data.decode("ascii")
    ring = re.search(r"ring\s+r\s*=\s*(\d+)\s*,\s*\(([^)]*)\)\s*,\s*dp\s*;", text)
    ideals = {m.group(1): m.group(2) for m in re.finditer(r"ideal\s+([JG])\s*=\s*([^;]*);", text)}
    if ring is None or set(ideals) != {"J", "G"} or int(ring.group(1)) != PRIME:
        fail("the header is not a ring over F_32029 with ideals J and G")
    names = [v.strip() for v in ring.group(2).split(",")]

    def split(s: str) -> list[str]:
        return [x for x in "".join(s.split()).split(",") if x]

    return names, split(ideals["J"]), split(ideals["G"])


def parse_poly(text: str, names: list[str]) -> list[list]:
    index = {v: i for i, v in enumerate(names)}
    terms: list[list] = []
    consumed = 0
    for sign, body in re.findall(r"([+-]?)([^+-]+)", text):
        consumed += len(sign) + len(body)
        coefficient, exponents = 1, [0] * len(names)
        for factor in body.split("*"):
            if factor.isdigit():
                coefficient *= int(factor)
                continue
            name, _, power = factor.partition("^")
            if name not in index or (power and not power.isdigit()):
                fail(f"unreadable factor {factor!r}")
            exponents[index[name]] += int(power) if power else 1
        terms.append([exponents, -coefficient if sign == "-" else coefficient])
    if consumed != len(text):
        fail(f"unreadable polynomial {text[:80]!r}")
    return terms


def normalize(tables: dict[str, list]) -> dict[str, list]:
    result = {}
    for table, polys in tables.items():
        result[table] = []
        for poly in polys:
            merged: dict[tuple[int, ...], int] = {}
            for exponents, coefficient in poly:
                key = tuple(exponents)
                merged[key] = (merged.get(key, 0) + coefficient) % PRIME
            result[table].append([[list(k), c] for k, c in sorted(merged.items()) if c])
    return result


def command_reference(header: str, out: str, pinned: bool = True) -> None:
    names, j_text, g_text = read_header(header, pinned)
    tables = {
        "J": [parse_poly(p, names) for p in j_text],
        "G": [parse_poly(p, names) for p in g_text],
    }
    Path(out).write_text(json.dumps(tables), encoding="ascii")


def command_reference_unpinned(header: str, out: str) -> None:
    command_reference(header, out, pinned=False)


def command_mutate(header: str, out: str, table: str) -> None:
    data = Path(header).read_bytes().decode("ascii")
    ideal = re.search(r"ideal\s+" + re.escape(table) + r"\s*=\s*([^;]*);", data)
    if ideal is None:
        fail("no such ideal")
    coefficient = re.search(r"(\d+)\*", ideal.group(1))
    if coefficient is None:
        fail("the ideal holds no integer coefficient")
    at = ideal.start(1) + coefficient.start(1)
    value = (int(coefficient.group(1)) + 1) % PRIME
    mutated = data[:at] + str(value) + data[at + len(coefficient.group(1)) :]
    Path(out).write_text(mutated, encoding="ascii")


def command_rocq(text_path: str, out: str) -> None:
    text = Path(text_path).read_text(encoding="ascii")
    values = re.findall(r"^\s*=\s*(.*?)\n\s*:\s", text, re.S | re.M)
    if len(values) != 2:
        fail("expected the Eval output of two tables")
    tables = {}
    for table, value in zip(("J", "G"), values, strict=True):
        converted = value.replace(";", ",").replace("(", "[").replace(")", "]")
        if re.search(r"[^\[\]\s,0-9]", converted):
            fail("the Eval output holds a token outside lists of naturals")
        tables[table] = json.loads(converted)
    Path(out).write_text(json.dumps(tables), encoding="ascii")


def command_compare(reference: str, rocq: str) -> None:
    left = normalize(json.loads(Path(reference).read_text(encoding="ascii")))
    right = normalize(json.loads(Path(rocq).read_text(encoding="ascii")))
    status = 0
    for table in ("J", "G"):
        if len(left[table]) != len(right[table]):
            print(f"{table}: {len(left[table])} polynomials against {len(right[table])}")
            status = 1
            continue
        for i, (a, b) in enumerate(zip(left[table], right[table], strict=True)):
            if a != b:
                print(f"{table}[{i}] differs: {len(a)} against {len(b)} terms")
                status = 1
    if status == 0:
        terms = sum(len(p) for t in left.values() for p in t)
        print(f"compare_hilbert_cell_header: J and G agree term by term ({terms} terms)")
    sys.exit(status)


COMMANDS = {
    "reference": (command_reference, 2),
    "reference-unpinned": (command_reference_unpinned, 2),
    "mutate": (command_mutate, 3),
    "rocq": (command_rocq, 2),
    "compare": (command_compare, 2),
}


def main() -> None:
    if len(sys.argv) < 2 or sys.argv[1] not in COMMANDS:
        fail("usage: reference|reference-unpinned|mutate|rocq|compare ARGS")
    function, count = COMMANDS[sys.argv[1]]
    if len(sys.argv) != count + 2:
        fail(f"{sys.argv[1]} takes {count} arguments")
    function(*sys.argv[2:])


if __name__ == "__main__":
    main()
