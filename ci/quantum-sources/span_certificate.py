"""Splitting certificate of the Leibniz system of the sedenions against the 14 G_2 derivation tables.

Unknown y[16 m + k] is coordinate k of D(e_m). The equation of (a, b, c) is coordinate c of
D(e_a e_b) - D(e_a) e_b - e_a D(e_b) for e_a e_b = cd_sign(16, a, b) e_(a xor b). With M the equations of a chosen
set of 242 independent triples, V the 256 x 14 matrix of the tables and C a left inverse of V (C V = I), the
certificate is a matrix P and a positive integer d with d I = P M + d V C over the Gaussian integers, so that
M y = 0 gives d y = V (d C y).

The inputs are the record of the 14 derivation tables (`docs/evidence/a5-kernel-attachments/
g2-derivation-tables.json`) and the left-inverse record that names C (`left-inverses.json` of this directory,
passed with `--left-inverses`); both are read with the exact key sets and integer types of
`gaussian_certificates.py`, and C V = I is checked before P is computed. Product signs come from
`gororoba_quantum/cd_core.py`. The computation of P needs python-flint (0.9.0, the pin of requirements.txt);
`--verify` needs none: it checks d I = P M + d V C on the record in Python integers, a Gaussian integer being a
pair (real part, imaginary part).

Run:
    "$PYTHON" span_certificate.py --left-inverses LEFT_JSON [--g2 G2_JSON] [--out SPAN_JSON]
    "$PYTHON" span_certificate.py --left-inverses LEFT_JSON --check    # recompute and compare with SPAN_JSON
    "$PYTHON" span_certificate.py --left-inverses LEFT_JSON --verify   # identity of SPAN_JSON, no python-flint
The command line computes row order 0, the lexicographic order of the triples, which the tracked record holds
(`"seed": 0` there names that order; no random draw enters). `span_record` also accepts the orders n > 0 of its
`seeds` argument, each a shuffle of the triples by `random.Random(n)` before the greedy choice of independent ones,
and keeps the order whose scalar d is smallest, then the fewest nonzero entries. No command-line flag offers them:
a new seed enters through `qrng_seeds.add_seed_argument` (AGENTS.md, "Seeds").
"""

from __future__ import annotations

import argparse
import json
import math
import os
import random
import sys
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import quantum_checkout  # noqa: E402

sys.path.insert(1, str(quantum_checkout.ROOT / "gororoba_quantum"))

import cd_core  # noqa: E402
import gaussian_certificates as gc  # noqa: E402
import render_span  # noqa: E402

N = 16
UNKNOWNS = N * N
DERIVATIONS = gc.DERIVATIONS
PRIME = 1_000_003
SPAN_RECORD = HERE / "span.json"

Triple = tuple[int, int, int]
Entry = gc.Entry
Rows = dict[Triple, dict[int, int]]
Tables = list[list[list[Entry]]]
LeftSparse = list[list[tuple[int, Entry]]]


def sign_table() -> list[list[int]]:
    return [[cd_core.cd_sign(N, a, b) for b in range(N)] for a in range(N)]


def equations(sign: list[list[int]]) -> Rows:
    rows: Rows = {}
    for a in range(N):
        for b in range(N):
            for c in range(N):
                row: dict[int, int] = {}
                for index, value in (
                    (N * (a ^ b) + c, sign[a][b]),
                    (N * a + (c ^ b), -sign[c ^ b][b]),
                    (N * b + (a ^ c), -sign[a][a ^ c]),
                ):
                    row[index] = row.get(index, 0) + value
                row = {index: value for index, value in row.items() if value}
                if row:
                    rows[(a, b, c)] = row
    return rows


def independent(rows: Rows, order: list[Triple]) -> list[Triple]:
    """Greedy row basis modulo PRIME in the given order (verified exactly afterwards by the solve)."""
    pivots: dict[int, dict[int, int]] = {}
    chosen = []
    for key in order:
        work = {index: value % PRIME for index, value in rows[key].items()}
        while work:
            lead = min(work)
            if lead not in pivots:
                break
            factor = work[lead]
            for index, value in pivots[lead].items():
                reduced = (work.get(index, 0) - factor * value) % PRIME
                if reduced:
                    work[index] = reduced
                else:
                    work.pop(index, None)
        if work:
            lead = min(work)
            scale = pow(work[lead], -1, PRIME)
            pivots[lead] = {index: value * scale % PRIME for index, value in work.items()}
            chosen.append(key)
    return chosen


def solve(rows: Rows, chosen: list[Triple], target: list[list[int]]) -> Any:
    """P (rational) with P M = target, M the chosen equations; raises unless the identity holds exactly."""
    import flint  # python-flint 0.9.0; the identity check of --verify needs no import of it

    count = len(chosen)
    dense = [[rows[key].get(index, 0) for index in range(UNKNOWNS)] for key in chosen]
    matrix = flint.fmpz_mat(dense)
    if matrix.rank() != count:
        raise RuntimeError("the chosen equations are dependent")
    # a column basis of M: pivot columns of the reduced row echelon form
    echelon, _ = flint.fmpq_mat(matrix).rref()
    columns = []
    for line in range(count):
        columns.append(next(index for index in range(UNKNOWNS) if echelon[line, index] != 0))
    square = flint.fmpq_mat([[dense[line][index] for index in columns] for line in range(count)])
    restricted = flint.fmpq_mat([[row[index] for index in columns] for row in target])
    solution = restricted * square.inv()
    if solution * flint.fmpq_mat(matrix) != flint.fmpq_mat(target):
        raise RuntimeError("the target rows leave the row space of the chosen equations")
    return solution


# The invariant factors of the 4096 x 256 integer Leibniz system (value -> multiplicity); the rest of the diagonal of
# its Smith form is zero. Computed with python-flint 0.9.0 and compared by --smith; no Rocq theorem states them.
SMITH_INVARIANTS = {1: 192, 2: 49, 6: 1}


def smith_invariants(rows: Rows) -> dict[int, int]:
    """The nonzero diagonal of the Smith normal form of the whole Leibniz system over Z, as value -> multiplicity."""
    import flint

    matrix = flint.fmpz_mat([[row.get(index, 0) for index in range(UNKNOWNS)] for row in rows.values()])
    form = matrix.snf()
    counts: dict[int, int] = {}
    for position in range(min(form.nrows(), form.ncols())):
        value = abs(int(form[position, position]))
        if value:
            counts[value] = counts.get(value, 0) + 1
    return counts


def nullity_modulo(invariants: dict[int, int], prime: int) -> int:
    """The dimension of the solution space modulo `prime`: the unknowns less the invariants prime does not divide."""
    return UNKNOWNS - sum(count for value, count in invariants.items() if value % prime)


def coordinate_matrix(tables: Tables) -> list[list[Entry]]:
    """V[16 m + k][n] is coordinate k of D_(n+1)(e_m)."""
    return [[tables[n][j // N][j % N] for n in range(DERIVATIONS)] for j in range(UNKNOWNS)]


def left_inverse_defects(tables: Tables, left_sparse: LeftSparse) -> list[tuple[int, int]]:
    """The positions where C V differs from the 14 x 14 identity."""
    left: list[list[Entry]] = [[(0, 0)] * UNKNOWNS for _ in range(DERIVATIONS)]
    for line, items in enumerate(left_sparse):
        for column, entry in items:
            left[line][column] = entry
    return gc.left_inverse_defects(coordinate_matrix(tables), left, (1, 0))


def span_record(tables: Tables, left_sparse: LeftSparse, seeds: list[int]) -> dict[str, Any]:
    """The splitting certificate of the best seed: the record that render_span.py reads."""
    defects = left_inverse_defects(tables, left_sparse)
    if defects:
        raise RuntimeError(f"the left inverse does not satisfy C V = I at {defects[:3]}")
    v = coordinate_matrix(tables)
    rows = equations(sign_table())
    # target = I - V C, split into real and imaginary parts
    real_target = [[0] * UNKNOWNS for _ in range(UNKNOWNS)]
    imag_target = [[0] * UNKNOWNS for _ in range(UNKNOWNS)]
    for i in range(UNKNOWNS):
        real_target[i][i] = 1
        for n in range(DERIVATIONS):
            a, b = v[i][n]
            if (a, b) == (0, 0):
                continue
            for j, (e, f) in left_sparse[n]:
                real_target[i][j] -= a * e - b * f
                imag_target[i][j] -= a * f + b * e
    best: dict[str, Any] | None = None
    for seed in seeds:
        order = sorted(rows)
        if seed:
            random.Random(seed).shuffle(order)  # noqa: S311 - a seeded, reproducible row order, no secret
        chosen = independent(rows, order)
        real_p = solve(rows, chosen, real_target)
        imag_p = solve(rows, chosen, imag_target)
        scalar = 1
        for matrix in (real_p, imag_p):
            for i in range(matrix.nrows()):
                for j in range(matrix.ncols()):
                    scalar = math.lcm(scalar, int(matrix[i, j].q))
        entries = [
            [(int(real_p[i, j] * scalar), int(imag_p[i, j] * scalar)) for j in range(len(chosen))]
            for i in range(UNKNOWNS)
        ]
        nonzero = sum(entry != (0, 0) for row in entries for entry in row)
        largest = max(abs(part) for row in entries for entry in row for part in entry)
        print(f"seed {seed}: equations {len(chosen)}, d = {scalar}, nonzero {nonzero}, largest |entry| {largest}")
        if best is None or (scalar, nonzero) < (best["d"], best["nonzero"]):
            best = {"seed": seed, "d": scalar, "nonzero": nonzero, "equations": chosen, "p": entries}
    if best is None:
        raise RuntimeError("no seed")
    print(f"kept seed {best['seed']}: d = {best['d']}, nonzero {best['nonzero']}")
    return {
        "schema": render_span.SCHEMA,
        "d": best["d"],
        "seed": best["seed"],
        "equations": [list(key) for key in best["equations"]],
        "p_sparse": [[[j, list(entry)] for j, entry in enumerate(row) if entry != (0, 0)] for row in best["p"]],
    }


def record_text(record: dict[str, Any]) -> str:
    return json.dumps(record) + "\n"


def splitting_defects(
    record: dict[str, Any], tables: Tables, left_sparse: LeftSparse, rows: Rows
) -> list[tuple[int, int]]:
    """The positions (i, j) where (P M + d V C)[i][j] differs from d for i = j and from 0 otherwise.

    P is `p_sparse` of the record, M the equations of the triples the record lists (taken from `rows`, the equations
    of cd_core.cd_sign), V the coordinates of the tables and C the left inverse. Gaussian integers are pairs."""
    scalar = record["d"]
    total: list[dict[int, Entry]] = [{} for _ in range(UNKNOWNS)]

    def accumulate(i: int, j: int, value: Entry) -> None:
        old = total[i].get(j, (0, 0))
        total[i][j] = (old[0] + value[0], old[1] + value[1])

    for i, line in enumerate(record["p_sparse"]):
        for equation, (real, imaginary) in line:
            for column, coefficient in rows[tuple(record["equations"][equation])].items():
                accumulate(i, column, (real * coefficient, imaginary * coefficient))
    v = coordinate_matrix(tables)
    for i in range(UNKNOWNS):
        for n in range(DERIVATIONS):
            a, b = v[i][n]
            for column, (e, f) in left_sparse[n]:
                accumulate(i, column, (scalar * (a * e - b * f), scalar * (a * f + b * e)))
    return [
        (i, j)
        for i in range(UNKNOWNS)
        for j in range(UNKNOWNS)
        if total[i].get(j, (0, 0)) != ((scalar, 0) if i == j else (0, 0))
    ]


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0] if __doc__ else None)
    parser.add_argument("--left-inverses", type=Path, help="the left-inverse record (JSON); every mode but --smith")
    parser.add_argument("--g2", type=Path, default=gc.G2_RECORD, help="g2-derivation-tables.json")
    parser.add_argument("--out", type=Path, default=SPAN_RECORD, help="the span record (JSON)")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--check", action="store_true", help="recompute and compare with --out, write nothing")
    mode.add_argument("--verify", action="store_true", help="check the identity of --out in integers, no flint")
    mode.add_argument("--smith", action="store_true", help="recompute the Smith invariants of the Leibniz system")
    arguments = parser.parse_args(argv)
    if arguments.smith:
        found_invariants = smith_invariants(equations(sign_table()))
        same = found_invariants == SMITH_INVARIANTS
        listed = ", ".join(f"{value} ({count})" for value, count in sorted(found_invariants.items()))
        print(
            f"{'ok' if same else 'DIFFERS'} Smith invariants {listed}; nullity {nullity_modulo(found_invariants, 2)}"
            f" modulo 2, {nullity_modulo(found_invariants, 3)} modulo 3"
        )
        return 0 if same else 1
    if arguments.left_inverses is None:
        parser.error("--left-inverses is required unless --smith is given")
    if not (arguments.check or arguments.verify):
        # The default mode writes the tracked record, so it reads only the tracked inputs and takes no override.
        if os.environ.get("QUANTUM_SOURCES_ROCQ"):
            raise quantum_checkout.refuse("a write of the span record takes no QUANTUM_SOURCES_ROCQ")
        quantum_checkout.confine_record(arguments.out, SPAN_RECORD)
        quantum_checkout.confine_record(arguments.left_inverses, gc.LEFT_INVERSES)
        quantum_checkout.confine_record(arguments.g2, gc.G2_RECORD)
    tables = gc.derivation_tables(json.loads(arguments.g2.read_text(encoding="utf-8")))
    left_sparse = gc.derivation_left_inverse(json.loads(arguments.left_inverses.read_text(encoding="utf-8")))
    if arguments.verify:
        record = render_span.read_span(json.loads(arguments.out.read_text(encoding="utf-8")))
        found = left_inverse_defects(tables, left_sparse) + splitting_defects(
            record, tables, left_sparse, equations(sign_table())
        )
        print(f"C V = I and P M + d V C = d I: {len(found)} defects, d = {record['d']}")
        return 1 if found else 0
    text = record_text(span_record(tables, left_sparse, [0]))
    if arguments.check:
        same = arguments.out.is_file() and arguments.out.read_text(encoding="utf-8") == text
        print(f"{'ok' if same else 'DIFFERS'} {arguments.out.name}")
        return 0 if same else 1
    arguments.out.write_text(text, encoding="utf-8")
    print(f"wrote {arguments.out.name} ({len(text)} bytes)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
