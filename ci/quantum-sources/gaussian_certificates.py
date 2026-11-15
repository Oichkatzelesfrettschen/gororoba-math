"""Rocq renderings of two Gaussian-integer records of the A_5 program.

- The 14 G_2 derivation tables (`g2-derivation-tables.json`, schema gororoba.a5.g2-derivation-tables/1) become
  `CdTowerG2Derivations.v`: one image table per derivation, the Leibniz rule on the 256 pairs of basis units
  decided by `vm_compute`, the rule on the whole level-4 algebra over every commutative ring that receives a
  homomorphism from the Gaussian integers by `derivation_transport` of CdTowerRingBaseChange.v, and the linear
  independence of the 14 maps from a left inverse of the 256 x 14 matrix of their coordinates.
- The eight W8 arc matrices (`w8-component-arc-matrices-qi.json`, schema
  gororoba.a5.w8-component-arc-matrices-qi/1) become `A5W8ArcMatrixRanks.v`: for each 24 x 6 matrix M a 6 x 24
  matrix L and a Gaussian integer d with L M = d I, which MatrixLeftInverseCertificate.v turns into the
  independence of the six columns over every ring where the image of d is a nonzero divisor.

A left inverse is built from the first linearly independent rows of M in row order: L holds the adjugate of that
square block in the columns of those rows and zero elsewhere, d is the determinant of the block, and both are
divided by the largest positive integer that divides every real and imaginary part. A scalar that is a unit is
normalized to 1.

The reader of each record accepts exactly the shape the rendered statements name: 14 derivations in order with
16 x 16 integer pairs, and the eight matrices of `ARC_IDS` in order with 24 x 6 entries written as decimal
integers. A float, a boolean, a fraction, a missing or an extra case raises.

The two Rocq files are sources of this repository (`rocq/quantum`). The module constants `G2_ROCQ_FILE` and
`ARC_ROCQ_FILE` name them; `main` compares the rendering with them (`--check`) or replaces them (`--write`):

    GOROROBA_QUANTUM=PATH "$PYTHON" ci/quantum-sources/gaussian_certificates.py --check

`--rocq DIRECTORY` names another directory that holds the two files, and `--g2`, `--arcs` and
`--record` replace the inputs of the gororoba-quantum checkout and the left-inverse record. `--write` writes
the two files and the record, `--check` compares them and writes nothing.
"""

from __future__ import annotations

import argparse
import json
import math
import os
import re
import sys
import tempfile
from fractions import Fraction
from itertools import pairwise
from pathlib import Path
from typing import Any

import quantum_checkout

HERE = Path(__file__).resolve().parent
ROOT = quantum_checkout.ROOT
sys.path.insert(0, str(ROOT / "gororoba_quantum"))

import parallel  # noqa: E402

G2_SCHEMA = "gororoba.a5.g2-derivation-tables/1"
ARC_SCHEMA = "gororoba.a5.w8-component-arc-matrices-qi/1"
RECORD_SCHEMA = "gororoba.a5.gaussian-left-inverses/1"
G2_FILE = "CdTowerG2Derivations.v"
ARC_FILE = "A5W8ArcMatrixRanks.v"
G2_RECORD = ROOT / "docs/evidence/a5-kernel-attachments/g2-derivation-tables.json"
ARC_RECORD = ROOT / "docs/evidence/a5-char0-transfer/w8-component-arc-matrices-qi.json"
LEFT_INVERSES = HERE / "left-inverses.json"
# The locations of the two Rocq sources; --rocq replaces them.
G2_ROCQ_FILE: Path = quantum_checkout.ROCQ / G2_FILE
ARC_ROCQ_FILE: Path = quantum_checkout.ROCQ / ARC_FILE
LINE_WIDTH = 116
DERIVATIONS = 14
DIMENSION = 16
ARC_ROWS = 24
ARC_COLUMNS = 6
ARC_IDS = (
    "w8-nm-linear-point1",
    "w8-nm-linear-point2",
    "w8-np-linear-point1",
    "w8-np-linear-point2",
    "w8-nm-series-point1",
    "w8-nm-series-point2",
    "w8-np-series-point1",
    "w8-np-series-point2",
)
DECIMAL_INTEGER = re.compile(r"-?(0|[1-9][0-9]*)")
G2_RECORD_KEYS = {"schema", "ring", "dimension", "convention", "inputs", "derivations", "span_rank", "pass"}
G2_DERIVATION_KEYS = {"id", "nonzero_entries", "real", "images"}
ARC_RECORD_KEYS = {"schema", "field", "inputs", "arc_record_sha256", "matrices", "pass"}
ARC_MATRIX_KEYS = {
    "id",
    "ledger_row",
    "slug",
    "family",
    "point",
    "order_of_G",
    "rows",
    "columns",
    "claimed_rank",
    "columns_meaning",
    "entries",
}
ARC_ENTRY_KEYS = {"re", "im"}
LEFT_RECORD_KEYS = {"schema", "ring", "convention", "g2_derivations", "arc_matrices"}
LEFT_SECTION_KEYS = {"row_meaning", "rows", "columns", "selected_rows", "d", "norm_of_d", "left_sparse"}

Entry = tuple[int, int]
Gaussian = tuple[Fraction, Fraction]
ZERO: Gaussian = (Fraction(0), Fraction(0))
ONE: Gaussian = (Fraction(1), Fraction(0))


def add(left: Gaussian, right: Gaussian) -> Gaussian:
    return (left[0] + right[0], left[1] + right[1])


def sub(left: Gaussian, right: Gaussian) -> Gaussian:
    return (left[0] - right[0], left[1] - right[1])


def mul(left: Gaussian, right: Gaussian) -> Gaussian:
    return (left[0] * right[0] - left[1] * right[1], left[0] * right[1] + left[1] * right[0])


def inverse(value: Gaussian) -> Gaussian:
    norm = value[0] * value[0] + value[1] * value[1]
    if norm == 0:
        raise ZeroDivisionError("inverse of the Gaussian zero")
    return (value[0] / norm, -value[1] / norm)


def independent_rows(matrix: list[list[Gaussian]], count: int) -> list[int]:
    """The first `count` rows, in row order, that are linearly independent over Q(i)."""
    reduced: list[tuple[int, list[Gaussian]]] = []
    chosen: list[int] = []
    for index, row in enumerate(matrix):
        work = list(row)
        for pivot, basis in reduced:
            factor = work[pivot]
            if factor != ZERO:
                work = [sub(entry, mul(factor, other)) for entry, other in zip(work, basis, strict=True)]
        lead = next((column for column, entry in enumerate(work) if entry != ZERO), None)
        if lead is None:
            continue
        scale = inverse(work[lead])
        work = [mul(scale, entry) for entry in work]
        reduced = [
            (other, [sub(entry, mul(basis[lead], mine)) for entry, mine in zip(basis, work, strict=True)])
            for other, basis in reduced
        ]
        reduced.append((lead, work))
        chosen.append(index)
        if len(chosen) == count:
            return chosen
    raise RuntimeError(f"the matrix has rank {len(chosen)}, below {count}")


def determinant_and_inverse(block: list[list[Gaussian]]) -> tuple[Gaussian, list[list[Gaussian]]]:
    """Gauss-Jordan elimination over Q(i) on a square block of full rank."""
    size = len(block)
    work = [list(row) + [ONE if column == index else ZERO for column in range(size)] for index, row in enumerate(block)]
    determinant = ONE
    for column in range(size):
        pivot_row = next(row for row in range(column, size) if work[row][column] != ZERO)
        if pivot_row != column:
            work[column], work[pivot_row] = work[pivot_row], work[column]
            determinant = sub(ZERO, determinant)
        pivot = work[column][column]
        determinant = mul(determinant, pivot)
        scale = inverse(pivot)
        work[column] = [mul(scale, entry) for entry in work[column]]
        for row in range(size):
            factor = work[row][column]
            if row != column and factor != ZERO:
                pivot_line = work[column]
                work[row] = [sub(entry, mul(factor, other)) for entry, other in zip(work[row], pivot_line, strict=True)]
    return determinant, [row[size:] for row in work]


def integer_pair(value: Gaussian) -> Entry:
    if value[0].denominator != 1 or value[1].denominator != 1:
        raise RuntimeError(f"{value} is not a Gaussian integer")
    return (int(value[0]), int(value[1]))


def left_inverse_defects(entries: list[list[Entry]], left: list[list[Entry]], scalar: Entry) -> list[Entry]:
    """The positions (l, j) where (left . entries)[l][j] differs from d for l = j and from 0 otherwise."""
    columns = len(left)
    defects = []
    for line in range(columns):
        for column in range(columns):
            real = imaginary = 0
            for row, matrix_row in enumerate(entries):
                a, b = left[line][row]
                c, e = matrix_row[column]
                real += a * c - b * e
                imaginary += a * e + b * c
            expected = scalar if line == column else (0, 0)
            if (real, imaginary) != expected:
                defects.append((line, column))
    return defects


def left_inverse(entries: list[list[Entry]]) -> dict[str, Any]:
    """Selected rows, scalar d and the nonzero entries of a left inverse: left . entries = d . identity."""
    columns = len(entries[0])
    matrix = [[(Fraction(real), Fraction(imaginary)) for real, imaginary in row] for row in entries]
    rows = independent_rows(matrix, columns)
    determinant, block_inverse = determinant_and_inverse([matrix[row] for row in rows])
    adjugate = [[integer_pair(mul(determinant, entry)) for entry in row] for row in block_inverse]
    scalar = integer_pair(determinant)
    content = math.gcd(*scalar, *(part for row in adjugate for entry in row for part in entry))
    scalar = (scalar[0] // content, scalar[1] // content)
    adjugate = [[(real // content, imaginary // content) for real, imaginary in row] for row in adjugate]
    if scalar[0] * scalar[0] + scalar[1] * scalar[1] == 1:
        # d is a unit: multiplying the left inverse by its conjugate gives d = 1.
        real, imaginary = scalar
        adjugate = [[(real * a + imaginary * b, real * b - imaginary * a) for a, b in row] for row in adjugate]
        scalar = (1, 0)
    left = [[(0, 0)] * len(entries) for _ in range(columns)]
    for line, adjugate_row in enumerate(adjugate):
        for position, row in enumerate(rows):
            left[line][row] = adjugate_row[position]
    defects = left_inverse_defects(entries, left, scalar)
    if defects:
        raise RuntimeError(f"left inverse fails at {defects[:3]}")
    return {
        "rows": len(entries),
        "columns": columns,
        "selected_rows": rows,
        "d": list(scalar),
        "norm_of_d": scalar[0] ** 2 + scalar[1] ** 2,
        "left_sparse": [[[row, list(line[row])] for row in rows if line[row] != (0, 0)] for line in left],
    }


def exact_integer(value: object, where: str) -> int:
    """A JSON integer; a float, a boolean or a string raises."""
    if type(value) is not int:
        raise RuntimeError(f"{where}: {value!r} is not an integer")
    return value


def decimal_integer(value: object, where: str) -> int:
    """A decimal integer written as a string, the form of the arc-matrix record."""
    if not isinstance(value, str) or DECIMAL_INTEGER.fullmatch(value) is None:
        raise RuntimeError(f"{where}: {value!r} is not a decimal integer string")
    return int(value)


def exact_keys(item: object, keys: set[str], where: str) -> dict[str, Any]:
    """A JSON object with exactly the named keys, so that a field this reader ignores cannot change a meaning."""
    if not isinstance(item, dict) or set(item) != keys:
        found = sorted(item) if isinstance(item, dict) else type(item).__name__
        raise RuntimeError(f"{where}: keys {found}, expected {sorted(keys)}")
    return item


def derivation_tables(record: dict[str, Any]) -> list[list[list[Entry]]]:
    """tables[n][m][c] is coordinate c of D_(n+1)(e_m) as (real part, imaginary part)."""
    exact_keys(record, G2_RECORD_KEYS, "derivation record")
    if record["schema"] != G2_SCHEMA or record["ring"] != "Z[i]":
        raise RuntimeError("unexpected derivation record")
    if exact_integer(record["dimension"], "dimension") != DIMENSION:
        raise RuntimeError("unexpected derivation record")
    if record.get("pass") is not True:
        raise RuntimeError("the derivation record does not pass its own checks")
    derivations = record["derivations"]
    if not isinstance(derivations, list) or len(derivations) != DERIVATIONS:
        raise RuntimeError(f"the derivation record does not hold {DERIVATIONS} tables")
    tables = []
    for number, derivation in enumerate(derivations, start=1):
        exact_keys(derivation, G2_DERIVATION_KEYS, f"derivation {number}")
        if derivation["id"] != f"g2_derivation_{number}":
            raise RuntimeError(f"derivation {number} has id {derivation['id']}")
        images = derivation["images"]
        if (
            not isinstance(images, list)
            or len(images) != DIMENSION
            or any(not isinstance(image, list) or len(image) != DIMENSION for image in images)
        ):
            raise RuntimeError(f"derivation {number}: the table is not {DIMENSION} x {DIMENSION}")
        table = []
        for unit, image in enumerate(images):
            row = []
            for coordinate, parts in enumerate(image):
                where = f"derivation {number}, image of e_{unit}, coordinate {coordinate}"
                if not isinstance(parts, list) or len(parts) != 2:
                    raise RuntimeError(f"{where}: {parts!r} is not a [real, imaginary] pair")
                row.append((exact_integer(parts[0], where), exact_integer(parts[1], where)))
            table.append(row)
        tables.append(table)
    return tables


def derivation_certificate(tables: list[list[list[Entry]]]) -> dict[str, Any]:
    """A left inverse of the 256 x 14 matrix whose row 16 m + c holds coordinate c of each D_n(e_m)."""
    entries = [
        [table[unit][coordinate] for table in tables] for unit in range(DIMENSION) for coordinate in range(DIMENSION)
    ]
    certificate = left_inverse(entries)
    if certificate["d"] != [1, 0]:
        raise RuntimeError(f"the scalar {certificate['d']} is not a unit; the rendered theorem needs d = 1")
    return {"row_meaning": "row 16 m + c is coordinate c of D(e_m)", **certificate}


def arc_certificate(matrix: dict[str, Any]) -> dict[str, Any]:
    """One matrix of the arc record with its integer entries and its exact left inverse; the matrices are
    independent, so arc_matrices maps this function over them in order."""
    name = matrix["id"]
    shape = tuple(exact_integer(matrix[key], f"{name}, {key}") for key in ("rows", "columns", "claimed_rank"))
    if shape != (ARC_ROWS, ARC_COLUMNS, ARC_COLUMNS):
        raise RuntimeError(f"{name}: rows, columns and claimed rank are {shape}")
    rows = matrix["entries"]
    if (
        not isinstance(rows, list)
        or len(rows) != ARC_ROWS
        or any(not isinstance(row, list) or len(row) != ARC_COLUMNS for row in rows)
    ):
        raise RuntimeError(f"{name}: the entries are not {ARC_ROWS} x {ARC_COLUMNS}")
    for index, row in enumerate(rows):
        for column, entry in enumerate(row):
            exact_keys(entry, ARC_ENTRY_KEYS, f"{name}, row {index}, column {column}")
    entries = [
        [
            (
                decimal_integer(entry["re"], f"{name}, row {index}, column {column}, re"),
                decimal_integer(entry["im"], f"{name}, row {index}, column {column}, im"),
            )
            for column, entry in enumerate(row)
        ]
        for index, row in enumerate(rows)
    ]
    return {"id": name, "ledger_row": matrix["ledger_row"], "entries": entries, **left_inverse(entries)}


def arc_matrices(record: dict[str, Any]) -> list[dict[str, Any]]:
    """The eight matrices of ARC_IDS, each with its integer entries and its left inverse."""
    exact_keys(record, ARC_RECORD_KEYS, "arc-matrix record")
    if record["schema"] != ARC_SCHEMA or record["field"] != "Q(i)":
        raise RuntimeError("unexpected arc-matrix record")
    matrices = record["matrices"]
    if not isinstance(matrices, list):
        raise RuntimeError("the arc-matrix record holds no list of matrices")
    for position, matrix in enumerate(matrices):
        exact_keys(matrix, ARC_MATRIX_KEYS, f"arc matrix {position}")
    if record.get("pass") is not True:
        raise RuntimeError("the arc-matrix record does not pass its own checks")
    identifiers = tuple(matrix["id"] for matrix in matrices)
    if identifiers != ARC_IDS:
        raise RuntimeError(f"the arc-matrix record holds {identifiers}, expected {ARC_IDS}")
    return parallel.ordered_map(arc_certificate, matrices, min_items=2)


def derivation_left_inverse(record: object) -> list[list[tuple[int, Entry]]]:
    """The 14 lines of the left inverse of the 256 x 14 coordinate matrix, each as (column, (real, imaginary)) pairs.

    The reader accepts exactly the shape this module writes: the key sets of the record and of its derivation
    section, integer types, scalar d = 1 with its norm, 14 distinct increasing selected rows within 0 to 255, 14 lines
    whose columns are distinct, increase and lie among the selected rows, the two sentences as nonempty strings and
    arc_matrices as a list of sections; their content is covered by the --check comparison of the whole record with
    its regeneration, and no Rocq rendering reads it from the record."""
    record = exact_keys(record, LEFT_RECORD_KEYS, "left-inverse record")
    if record["schema"] != RECORD_SCHEMA or record["ring"] != "Z[i]":
        raise RuntimeError("unexpected left-inverse record")
    section = exact_keys(record["g2_derivations"], LEFT_SECTION_KEYS, "left-inverse record, derivations")
    if (
        exact_integer(section["rows"], "derivations, rows") != DIMENSION * DIMENSION
        or exact_integer(section["columns"], "derivations, columns") != DERIVATIONS
    ):
        raise RuntimeError("the derivation left inverse is not 14 x 256")
    scalar = section["d"]
    if not isinstance(scalar, list) or len(scalar) != 2:
        raise RuntimeError(f"derivations, d: {scalar!r} is not a [real, imaginary] pair")
    if (exact_integer(scalar[0], "derivations, d"), exact_integer(scalar[1], "derivations, d")) != (1, 0):
        raise RuntimeError(f"the scalar {scalar} is not 1")
    if exact_integer(section["norm_of_d"], "derivations, norm_of_d") != 1:
        raise RuntimeError(f"derivations, norm_of_d: {section['norm_of_d']} is not the norm of d = 1")
    for holder, key in ((record, "convention"), (section, "row_meaning")):
        if not isinstance(holder[key], str) or not holder[key]:
            raise RuntimeError(f"left-inverse record, {key}: {holder[key]!r} is not a sentence")
    if not isinstance(record["arc_matrices"], list) or not all(
        isinstance(item, dict) for item in record["arc_matrices"]
    ):
        raise RuntimeError("left-inverse record, arc_matrices: not a list of sections")
    selected = section["selected_rows"]
    if not isinstance(selected, list) or len(selected) != DERIVATIONS:
        raise RuntimeError(f"derivations, selected_rows: not a list of {DERIVATIONS} rows")
    chosen = [exact_integer(row, "derivations, selected_rows") for row in selected]
    if any(not 0 <= row < DIMENSION * DIMENSION for row in chosen) or any(a >= b for a, b in pairwise(chosen)):
        raise RuntimeError(f"derivations, selected_rows: {chosen} leaves 0 to 255, repeats or is out of order")
    lines = section["left_sparse"]
    if not isinstance(lines, list) or len(lines) != DERIVATIONS:
        raise RuntimeError(f"the left inverse does not hold {DERIVATIONS} lines")
    result = []
    for number, line in enumerate(lines):
        if not isinstance(line, list):
            raise RuntimeError(f"left inverse line {number} is not a list")
        items: list[tuple[int, Entry]] = []
        for position, item in enumerate(line):
            where = f"left inverse line {number}, item {position}"
            if not isinstance(item, list) or len(item) != 2 or not isinstance(item[1], list) or len(item[1]) != 2:
                raise RuntimeError(f"{where}: {item!r} is not [column, [real, imaginary]]")
            column = exact_integer(item[0], where)
            if not 0 <= column < DIMENSION * DIMENSION or (items and column <= items[-1][0]):
                raise RuntimeError(f"{where}: column {column} is out of range, repeated or out of order")
            if column not in chosen:
                raise RuntimeError(f"{where}: column {column} is outside selected_rows")
            items.append((column, (exact_integer(item[1][0], where), exact_integer(item[1][1], where))))
        result.append(items)
    return result


def wrapped(items: list[str], indent: str, opening: str, closing: str) -> str:
    """`opening item; item; ... closing`, broken at LINE_WIDTH with continuation lines at `indent`."""
    lines = [indent + opening]
    for position, item in enumerate(items):
        piece = item + ("; " if position + 1 < len(items) else "")
        if len(lines[-1]) + len(piece.rstrip()) > LINE_WIDTH:
            lines[-1] = lines[-1].rstrip()
            lines.append(indent + " " * len(opening))
        lines[-1] += piece
    return "\n".join(lines) + closing


def pair(entry: Entry) -> str:
    return f"({entry[0]}, {entry[1]})"


def dense_table(name: str, rows: list[list[Entry]]) -> str:
    body = ";\n".join(wrapped([pair(entry) for entry in row], "    ", "[", "]") for row in rows)
    return f"Definition {name} : list (list (Z * Z)) :=\n  [\n{body}\n  ].\n"


def sparse_table(name: str, lines: list[list[list[Any]]]) -> str:
    body = ";\n".join(
        wrapped([f"({row}%nat, {pair((value[0], value[1]))})" for row, value in line], "    ", "[", "]")
        for line in lines
    )
    return f"Definition {name} : list (list (nat * (Z * Z))) :=\n  [\n{body}\n  ].\n"


def identifier(name: str) -> str:
    return name.replace("-", "_")


def render_g2(tables: list[list[list[Entry]]], certificate: dict[str, Any]) -> str:
    count = len(tables)
    out = [
        "(** 14 derivations of the sedenions over a commutative ring that receives the Gaussian integers: the tables",
        "    that the source record names the G_2 derivations. No theorem of this file states that they span the",
        "    derivation algebra or that it is g_2.",
        "",
        "    Generated by docs/evidence/a5-gaussian-certificates/gaussian_certificates.py of gororoba-quantum from",
        "    docs/evidence/a5-kernel-attachments/g2-derivation-tables.json there; edit the generator, not this file.",
        "",
        "    [images_N m] is D_N(e_m) for the N-th table of the record, a Gaussian-integer combination of the basis",
        "    units of level 4 of the ring tower. [leibniz_basis_N] decides D(e_i e_j) = D(e_i) e_j + e_i D(e_j) on",
        "    the 256 pairs of basis units over the Gaussian integers, and [derivation_N] is the same rule for all",
        "    x and y over a target ring D with a homomorphism h from the Gaussian integers, through",
        "    [derivation_transport] of CdTowerRingBaseChange.v.",
        "",
        "    Independence: [coefficient r n] is coordinate (r mod 16) of D_(n+1)(e_(r / 16)), a 256 x 14 matrix M.",
        "    [independence_left] holds a 14 x 256 matrix L by its nonzero entries (column, value) and",
        "    [independence_d] the scalar d = 1 with L M = d I ([independence_left_inverse]). A combination",
        "    sum_n a_n D_(n+1) that vanishes on the 16 basis units of the target algebra then has h(d) a_n = 0",
        "    ([derivations_relation_coefficients], through MatrixLeftInverseCertificate.v), and since d = 1 the",
        "    14 derivations are linearly independent over every target ring",
        "    ([derivations_independent_on_basis_units], [derivations_independent]). *)",
        "",
        "From Stdlib Require Import Ring Lia PeanoNat ZArith List.",
        "Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange GaussianIntegerHom.",
        "Require Import MatrixLeftInverseCertificate.",
        "Import ListNotations.",
        "",
        "Module G2DerivationTables.",
        "Local Open Scope Z_scope.",
        "",
        sparse_table("independence_left", certificate["left_sparse"]),
        f"Definition independence_d : Z * Z := {pair((certificate['d'][0], certificate['d'][1]))}.",
        "",
        "End G2DerivationTables.",
        "",
        "Module G2Derivations (D : CommutativeRing) (H : RingHom GaussianIntegers D).",
        "Module BC := BaseChange GaussianIntegers D H.",
        "Module LC := LeftInverseCertificate GaussianIntegers D H.",
        "Import BC.",
        "",
        "Add Ring g2_derivation_target : D.ring_th.",
        "",
        "Definition vec (entries : list (nat * (Z * Z))) : TA.cd 4 :=",
        "  fold_right (fun entry rest => TA.add 4 (TA.scale 4 (snd entry) (SA.basis 4 (fst entry))) rest)"
        " (TA.zero 4) entries.",
        "",
        "Ltac basis_pairs :=",
        "  intros i j Hi Hj; change (Nat.pow 2 4) with 16%nat in Hi, Hj;",
        "  do 16 (destruct i as [|i];",
        "    [ do 16 (destruct j as [|j]; [vm_compute; reflexivity |]); exfalso; lia |]);",
        "  exfalso; lia.",
        "",
    ]
    for number, images in enumerate(tables, start=1):
        out.append(f"Definition images_{number} (m : nat) : TA.cd 4 :=")
        out.append("  match m with")
        for unit, image in enumerate(images):
            terms = [
                f"({index}%nat, ({real}, {imaginary})%Z)"
                for index, (real, imaginary) in enumerate(image)
                if (real, imaginary) != (0, 0)
            ]
            if terms:
                out.append(f"  | {unit} => vec [{'; '.join(terms)}]")
        out += [
            "  | _ => TA.zero 4",
            "  end.",
            "",
            f"Lemma leibniz_basis_{number} : forall i j, (i < Nat.pow 2 4)%nat -> (j < Nat.pow 2 4)%nat ->",
            f"  source_map 4 images_{number} (TA.mul 4 (SA.basis 4 i) (SA.basis 4 j)) =",
            f"  TA.add 4 (TA.mul 4 (source_map 4 images_{number} (SA.basis 4 i)) (SA.basis 4 j))",
            f"           (TA.mul 4 (SA.basis 4 i) (source_map 4 images_{number} (SA.basis 4 j))).",
            "Proof. basis_pairs. Qed.",
            "",
            f"Theorem derivation_{number} : forall x y, target_map 4 images_{number} (TB.mul 4 x y) =",
            f"  TB.add 4 (TB.mul 4 (target_map 4 images_{number} x) y) (TB.mul 4 x (target_map 4 images_{number} y)).",
            f"Proof. exact (derivation_transport 4 images_{number} leibniz_basis_{number}). Qed.",
            "",
        ]
    combination = f"SB.tsum 4 {count} (fun n => TB.scale 4 (a n) (target_map 4 (images n)"
    out += [
        f"(** [images n] is the table of D_(n+1) for n < {count}; a larger n reads the last table. *)",
        "Definition images (n : nat) : nat -> TA.cd 4 :=",
        "  match n with",
        *(f"  | {index} => images_{index + 1}" for index in range(count - 1)),
        f"  | _ => images_{count}",
        "  end.",
        "",
        "Definition coefficient (r n : nat) : GaussianIntegers.t := TA.coord 4 (images n (r / 16)) (r mod 16).",
        "",
        "Lemma independence_left_well_formed :",
        f"  LC.sparse_shape G2DerivationTables.independence_left {count} 256 = true.",
        "Proof. vm_compute. reflexivity. Qed.",
        "",
        f"Lemma independence_left_inverse : forall l j, (l < {count})%nat -> (j < {count})%nat ->",
        "  LC.SA.dsum 256",
        "    (fun r => GaussianIntegers.mul (LC.sparse_entry G2DerivationTables.independence_left l r)",
        "                (coefficient r j)) =",
        "  if Nat.eqb j l then G2DerivationTables.independence_d else GaussianIntegers.zero.",
        "Proof.",
        "  intros l j Hl Hj;",
        f"  do {count} (destruct l as [|l];",
        f"    [ do {count} (destruct j as [|j]; [vm_compute; reflexivity |]); exfalso; lia |]);",
        "  exfalso; lia.",
        "Qed.",
        "",
        "Lemma dsum_agree n (g : nat -> D.t) : SB.dsum n g = LC.SB.dsum n g.",
        "Proof. induction n as [|m IH]; cbn [SB.dsum LC.SB.dsum]; [reflexivity | rewrite IH; reflexivity]. Qed.",
        "",
        "(** Coordinate c of the image of the basis unit e_m under the map with prescribed images, at every",
        "    level k. *)",
        "Lemma target_map_basis_coord k (table : nat -> TA.cd k) m c : (m < Nat.pow 2 k)%nat ->",
        "  TB.coord k (target_map k table (SB.basis k m)) c = H.h (TA.coord k (table m) c).",
        "Proof.",
        "  intro Hm. unfold target_map. rewrite SB.coord_tsum.",
        "  rewrite (SB.dsum_ext _ _",
        "             (fun i => D.mul (TB.coord k (tmap k (table i)) c) (if Nat.eqb i m then D.one else D.zero))).",
        "  - rewrite SB.dsum_delta, (proj2 (Nat.ltb_lt _ _) Hm), <- tmap_coord. reflexivity.",
        "  - intros i Hi. rewrite TB.coord_scale, SB.coord_basis by assumption.",
        "    rewrite (Nat.eqb_sym m i). ring.",
        "Qed.",
        "",
        f"(** A combination of the {count} derivations that vanishes on the 16 basis units of the target algebra has",
        "    every coefficient annihilated by h(d). *)",
        "Theorem derivations_relation_coefficients (a : nat -> D.t) :",
        f"  (forall m, (m < 16)%nat -> {combination} (SB.basis 4 m))) =",
        "     TB.zero 4) ->",
        f"  forall n, (n < {count})%nat -> D.mul (H.h G2DerivationTables.independence_d) (a n) = D.zero.",
        "Proof.",
        "  intro R.",
        f"  apply (LC.relation_coefficients 256 {count} G2DerivationTables.independence_d coefficient",
        "           (LC.sparse_entry G2DerivationTables.independence_left) independence_left_inverse a).",
        "  unfold LC.relation. intros r Hr.",
        "  assert (Hm : (r / 16 < 16)%nat) by (apply Nat.Div0.div_lt_upper_bound; lia).",
        "  pose proof (f_equal (fun w => TB.coord 4 w (r mod 16)) (R (r / 16) Hm)) as E.",
        "  cbn beta in E. rewrite SB.coord_tsum, TB.coord_zero in E.",
        "  rewrite <- dsum_agree, <- E. apply SB.dsum_ext. intros n _.",
        "  rewrite TB.coord_scale, (target_map_basis_coord 4) by exact Hm. unfold coefficient. ring.",
        "Qed.",
        "",
        f"(** The scalar is 1, so the {count} derivations are linearly independent over the target ring. *)",
        "Theorem derivations_independent_on_basis_units (a : nat -> D.t) :",
        f"  (forall m, (m < 16)%nat -> {combination} (SB.basis 4 m))) =",
        "     TB.zero 4) ->",
        f"  forall n, (n < {count})%nat -> a n = D.zero.",
        "Proof.",
        "  intros R n Hn. pose proof (derivations_relation_coefficients a R n Hn) as E.",
        "  change G2DerivationTables.independence_d with GaussianIntegers.one in E.",
        "  rewrite H.h_one in E. rewrite <- E. ring.",
        "Qed.",
        "",
        "Theorem derivations_independent (a : nat -> D.t) :",
        f"  (forall x, {combination} x)) = TB.zero 4) ->",
        f"  forall n, (n < {count})%nat -> a n = D.zero.",
        "Proof. intro R. apply derivations_independent_on_basis_units. intros m _. apply R. Qed.",
        "",
        "End G2Derivations.",
        "",
        "(** Over the Gaussian integers, with the identity homomorphism. *)",
        "Module GaussianG2 := G2Derivations GaussianIntegers GaussianIdentity.",
        "",
        "(** Over a commutative ring with a square root of -1, with the homomorphism (a, b) -> a + b i. *)",
        "Module G2DerivationsWithI (D : CommutativeRingWithI).",
        "Module H := GaussianHom D.",
        "Module Derivations := G2Derivations D H.",
        "End G2DerivationsWithI.",
        "",
    ]
    return "\n".join(out)


def render_arcs(certificates: list[dict[str, Any]]) -> str:
    out = [
        "(** Independent columns of the eight W8 arc matrices [dF | F] of the A_5 program, by left inverses.",
        "",
        "    Generated by docs/evidence/a5-gaussian-certificates/gaussian_certificates.py of gororoba-quantum from",
        "    docs/evidence/a5-char0-transfer/w8-component-arc-matrices-qi.json there; edit the generator, not this",
        "    file.",
        "",
        "    For each 24 x 6 matrix M of the record, [NAME_matrix] holds its Gaussian-integer entries as pairs",
        "    (real part, imaginary part), [NAME_left] a 6 x 24 matrix L by its nonzero entries (column, value)",
        "    and [NAME_d] a scalar d with L M = d I, checked on the 36 entries by [vm_compute]",
        "    ([NAME_left_inverse]); [NAME_tables_well_formed] checks the shape of both tables.",
        "    MatrixLeftInverseCertificate.v then gives, over every commutative ring D that receives a",
        "    homomorphism h from the Gaussian integers: a column relation M a = 0 has h(d) a_l = 0",
        "    ([NAME_relation_coefficients]), and the six columns are linearly independent where h(d) is a nonzero",
        "    divisor ([NAME_columns_independent]). Over the Gaussian integers themselves d is nonzero",
        "    ([NAME_columns_independent_gaussian]); independence over Q(i), which is rank 6, follows by clearing",
        "    denominators, a step in prose: no theorem of this file models Q(i). *)",
        "",
        "From Stdlib Require Import Lia PeanoNat ZArith List.",
        "Require Import CdTowerRing CdTowerRingBaseChange GaussianIntegerHom MatrixLeftInverseCertificate.",
        "Import ListNotations.",
        "",
        "Module W8ArcTables.",
        "Local Open Scope Z_scope.",
        "",
    ]
    for certificate in certificates:
        name = identifier(certificate["id"])
        out.append(dense_table(f"{name}_matrix", certificate["entries"]))
        out.append(sparse_table(f"{name}_left", certificate["left_sparse"]))
        out.append(f"Definition {name}_d : Z * Z := {pair((certificate['d'][0], certificate['d'][1]))}.\n")
    out += [
        "End W8ArcTables.",
        "",
        "Module W8ArcMatrixRanks (D : CommutativeRing) (H : RingHom GaussianIntegers D).",
        "Module LC := LeftInverseCertificate GaussianIntegers D H.",
        "Import W8ArcTables.",
        "",
        "Ltac left_inverse_entries :=",
        "  intros l j Hl Hj;",
        "  do 6 (destruct l as [|l];",
        "    [ do 6 (destruct j as [|j]; [vm_compute; reflexivity |]); exfalso; lia |]);",
        "  exfalso; lia.",
        "",
    ]
    for certificate in certificates:
        name = identifier(certificate["id"])
        out += [
            f"Lemma {name}_tables_well_formed :",
            f"  LC.dense_shape {name}_matrix 24 6 = true /\\ LC.sparse_shape {name}_left 6 24 = true.",
            "Proof. split; vm_compute; reflexivity. Qed.",
            "",
            f"Lemma {name}_left_inverse : forall l j, (l < 6)%nat -> (j < 6)%nat ->",
            "  LC.SA.dsum 24",
            f"    (fun r => GaussianIntegers.mul (LC.sparse_entry {name}_left l r)",
            f"                (LC.entry {name}_matrix r j)) =",
            f"  if Nat.eqb j l then {name}_d else GaussianIntegers.zero.",
            "Proof. left_inverse_entries. Qed.",
            "",
            f"Theorem {name}_relation_coefficients (a : nat -> D.t) :",
            f"  LC.relation 24 6 (LC.entry {name}_matrix) a ->",
            f"  forall l, (l < 6)%nat -> D.mul (H.h {name}_d) (a l) = D.zero.",
            "Proof.",
            f"  exact (LC.relation_coefficients 24 6 {name}_d (LC.entry {name}_matrix)",
            f"           (LC.sparse_entry {name}_left) {name}_left_inverse a).",
            "Qed.",
            "",
            f"Theorem {name}_columns_independent (a : nat -> D.t) :",
            f"  (forall x, D.mul (H.h {name}_d) x = D.zero -> x = D.zero) ->",
            f"  LC.relation 24 6 (LC.entry {name}_matrix) a -> forall l, (l < 6)%nat -> a l = D.zero.",
            "Proof.",
            f"  exact (LC.columns_independent 24 6 {name}_d (LC.entry {name}_matrix)",
            f"           (LC.sparse_entry {name}_left) {name}_left_inverse a).",
            "Qed.",
            "",
        ]
    out += [
        "End W8ArcMatrixRanks.",
        "",
        "(** Over the Gaussian integers, with the identity homomorphism. *)",
        "Module GaussianW8ArcMatrixRanks := W8ArcMatrixRanks GaussianIntegers GaussianIdentity.",
        "Module GaussianLC := GaussianW8ArcMatrixRanks.LC.",
        "",
        "(** Over a commutative ring with a square root of -1, with the homomorphism (a, b) -> a + b i. *)",
        "Module W8ArcMatrixRanksWithI (D : CommutativeRingWithI).",
        "Module H := GaussianHom D.",
        "Module Ranks := W8ArcMatrixRanks D H.",
        "End W8ArcMatrixRanksWithI.",
        "",
    ]
    for certificate in certificates:
        name = identifier(certificate["id"])
        out += [
            f"Theorem {name}_columns_independent_gaussian (a : nat -> GaussianIntegers.t) :",
            f"  GaussianLC.relation 24 6 (GaussianLC.entry W8ArcTables.{name}_matrix) a ->",
            "  forall l, (l < 6)%nat -> a l = GaussianIntegers.zero.",
            "Proof.",
            f"  apply GaussianW8ArcMatrixRanks.{name}_columns_independent.",
            f"  intros x E. apply (gaussian_regular W8ArcTables.{name}_d); [| exact E].",
            "  intro Z. vm_compute in Z. discriminate Z.",
            "Qed.",
            "",
        ]
    return "\n".join(out)


def replace_text(path: Path, text: str) -> None:
    """Replace `path` with `text` through a scratch file created exclusively beside it, so that a reader sees the
    old bytes or the new ones, with the mode of an existing `path` (0644 otherwise)."""
    mode = path.stat().st_mode & 0o777 if path.is_file() else 0o644
    descriptor, scratch = tempfile.mkstemp(prefix=path.name + ".", dir=path.parent)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as stream:
            stream.write(text)
        os.chmod(scratch, mode)
        os.replace(scratch, path)
    except BaseException:
        Path(scratch).unlink(missing_ok=True)
        raise


def left_inverse_record(independence: dict[str, Any], certificates: list[dict[str, Any]]) -> dict[str, Any]:
    return {
        "schema": RECORD_SCHEMA,
        "ring": "Z[i]",
        "convention": (
            "every entry is [real part, imaginary part]; left_sparse[l] lists [column, entry] of line l of the"
            " left inverse, a column of the left inverse being a row of the matrix; left . matrix = d . identity"
        ),
        "g2_derivations": independence,
        "arc_matrices": [
            {key: value for key, value in certificate.items() if key != "entries"} for certificate in certificates
        ],
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0] if __doc__ else None)
    parser.add_argument("--g2", type=Path, default=G2_RECORD, help="g2-derivation-tables.json")
    parser.add_argument("--arcs", type=Path, default=ARC_RECORD, help="w8-component-arc-matrices-qi.json")
    parser.add_argument("--record", type=Path, default=LEFT_INVERSES, help="path of the left-inverse record (JSON)")
    parser.add_argument("--rocq", type=Path, help="directory of the two rendered Rocq files, instead of rocq/quantum")
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--check", action="store_true", help="compare with the files on disk, write nothing")
    mode.add_argument("--write", action="store_true", help="write the two Rocq files and the record")
    arguments = parser.parse_args(argv)
    g2_target, arc_target = G2_ROCQ_FILE, ARC_ROCQ_FILE
    if arguments.rocq is not None:
        g2_target, arc_target = arguments.rocq / G2_FILE, arguments.rocq / ARC_FILE

    certificates = arc_matrices(json.loads(arguments.arcs.read_text(encoding="utf-8")))
    tables = derivation_tables(json.loads(arguments.g2.read_text(encoding="utf-8")))
    independence = derivation_certificate(tables)
    rendered = {
        g2_target: render_g2(tables, independence),
        arc_target: render_arcs(certificates),
        arguments.record: json.dumps(left_inverse_record(independence, certificates), indent=1) + "\n",
    }
    status = 0
    for target, text in rendered.items():
        if arguments.check:
            same = target.is_file() and target.read_text(encoding="utf-8") == text
            print(f"{'ok' if same else 'DIFFERS'} {target.name}")
            status = status if same else 1
        else:
            replace_text(target, text)
            print(f"wrote {target.name} ({len(text)} bytes)")
    print(f"g2 derivations: rows {independence['selected_rows']}, d = {tuple(independence['d'])}")
    for certificate in certificates:
        print(
            f"{certificate['id']}: rows {certificate['selected_rows']}, d = {tuple(certificate['d'])},"
            f" norm {certificate['norm_of_d']}"
        )
    return status


if __name__ == "__main__":
    sys.exit(main())
