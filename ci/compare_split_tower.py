#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Helpers of ci/compare_split_tower.sh.

cases OUT_V MUTANT_V   write the Rocq evaluation sources of the split tower and of a mutated one that
                       negates every gamma
compare RUST ROCQ      compare the basis products of cd_multiply_split with those of the Rocq tower

A case is a level n in {2, 3} and a signature (gamma_0, ..., gamma_(n-1)) in {-1, 1}^n, 12 cases.
The rows of the Rust program read: n, the signature as a comma-separated list, then the integer
coordinates of e_p e_q for p, q below 2^n in row-major order. The Rocq source prints one list of the
same coordinates per case, in the order of CASES.
"""

import itertools
import re
import sys

CASES = [
    (n, gammas)
    for n in (2, 3)
    for gammas in itertools.product((-1, 1), repeat=n)
]


def z_literal(value):
    return "(%d)%%Z" % value


def rocq_source(mutated):
    sign = "Z.opp (nth k gs 1)" if mutated else "nth k gs 1"
    lines = [
        "From Stdlib Require Import ZArith List.",
        "Import ListNotations.",
        "Require Import SplitDoublingTower.",
        "Open Scope Z_scope.",
        "",
        "Definition table (n : nat) (gs : list Z) : list Z :=",
        "  let g := fun k => %s in" % sign,
        "  flat_map (fun p => flat_map (fun q =>",
        "    flat n (ZT.mul n g (basis n p) (basis n q))) (seq 0 (Nat.pow 2 n)))",
        "    (seq 0 (Nat.pow 2 n)).",
        "",
    ]
    for n, gammas in CASES:
        lines.append(
            "Compute (table %d [%s])." % (n, "; ".join(z_literal(g) for g in gammas))
        )
    return "\n".join(lines) + "\n"


def parse_rust(path):
    rows = {}
    with open(path, encoding="utf-8") as handle:
        for line in handle:
            fields = line.split()
            if not fields:
                continue
            n = int(fields[0])
            gammas = tuple(int(x) for x in fields[1].split(","))
            rows[(n, gammas)] = [int(x) for x in fields[2:]]
    return rows


def parse_rocq(path):
    with open(path, encoding="utf-8") as handle:
        text = handle.read()
    blocks = re.findall(r"=\s*(.*?)\s*:\s*list Z", text, flags=re.S)
    if len(blocks) != len(CASES):
        raise SystemExit("compare_split_tower: %d Rocq results, %d expected" % (len(blocks), len(CASES)))
    return {
        case: [int(x) for x in re.findall(r"-?\d+", block)]
        for case, block in zip(CASES, blocks)
    }


def compare(rust_path, rocq_path):
    rust = parse_rust(rust_path)
    rocq = parse_rocq(rocq_path)
    status = 0
    for case in CASES:
        n, gammas = case
        want = rust.get(case)
        have = rocq[case]
        if want is None or len(want) != 4 ** n * 2 ** n:
            raise SystemExit("compare_split_tower: the Rust output lacks case %r" % (case,))
        if want != have:
            first = next(i for i, (a, b) in enumerate(zip(want, have)) if a != b)
            pair, coord = divmod(first, 2 ** n)
            print(
                "compare_split_tower: level %d gammas %s differ at e_%d e_%d coordinate %d: %d against %d"
                % (n, list(gammas), pair // 2 ** n, pair % 2 ** n, coord, want[first], have[first])
            )
            status = 1
    if status == 0:
        print(
            "compare_split_tower: %d cases, %d coordinates agree"
            % (len(CASES), sum(len(v) for v in rust.values()))
        )
    return status


def main(argv):
    if len(argv) == 4 and argv[1] == "cases":
        with open(argv[2], "w", encoding="utf-8") as handle:
            handle.write(rocq_source(False))
        with open(argv[3], "w", encoding="utf-8") as handle:
            handle.write(rocq_source(True))
        return 0
    if len(argv) == 4 and argv[1] == "compare":
        return compare(argv[2], argv[3])
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv))
