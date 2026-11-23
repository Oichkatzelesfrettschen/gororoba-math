"""Exact census of the sedenion index planes, written before the Rocq source.

The sign function is the recursion of gororoba-quantum cd_core.cd_sign and of
gororoba-open cd_basis_mul_sign (the two agree line for line). The script
prints one JSON object; it reads no file and takes no argument.

Predictions recorded before the first run, each confirmed by it:
ordered nonassociating basis triples 1848 of 4096; noncommuting ordered
imaginary pairs 210; 35 lines; 15 planes; every pair of planes shares 4
indices and one line; 252 sorted triples fail to associate; 8 planes hold 28
of them and 7 planes hold 4; left alternativity on two-term elements fails in
exactly those 7 planes; 336 ordered signed zero products of 2-blades on 84
unordered assessor pairs; every such pair spans one of the 7 planes, 12 per
plane.
"""

import itertools
import json

DIM = 16
Vector = list[int]
Blade = tuple[int, int, int]


def sign(dim: int, p: int, q: int) -> int:
    """Sign of e_p * e_q in the Cayley-Dickson algebra of dimension dim."""
    result = 1
    half = dim >> 1
    while half > 0:
        p_high = p >= half
        q_high = q >= half
        if not p_high and q_high:
            p, q = q - half, p
        elif p_high and not q_high:
            p -= half
            if q != 0:
                result = -result
        elif p_high and q_high:
            if q == half:
                return -result
            p, q = q - half, p - half
        half >>= 1
    return result


SIGN = [[sign(DIM, p, q) for q in range(DIM)] for p in range(DIM)]


def mul(x: Vector, y: Vector) -> Vector:
    z = [0] * DIM
    for i, a in enumerate(x):
        if a:
            for j, b in enumerate(y):
                if b:
                    z[i ^ j] += a * b * SIGN[i][j]
    return z


def unit(i: int, coefficient: int = 1) -> Vector:
    v = [0] * DIM
    v[i] = coefficient
    return v


def add(x: Vector, y: Vector) -> Vector:
    return [a + b for a, b in zip(x, y, strict=True)]


def fails(a: int, b: int, c: int) -> bool:
    """Whether (e_a e_b) e_c differs from e_a (e_b e_c)."""
    return SIGN[a][b] * SIGN[a ^ b][c] != SIGN[b][c] * SIGN[a][b ^ c]


def span(generators: list[int]) -> tuple[int, ...]:
    group = {0}
    for x in generators:
        group |= {h ^ x for h in group}
    return tuple(sorted(group))


def plane_record(plane: tuple[int, ...]) -> dict[str, object]:
    imaginary = [x for x in plane if x]
    triples = [t for t in itertools.combinations(imaginary, 3) if t[0] ^ t[1] ^ t[2] != 0]
    left = right = flexible = 0
    for a, b in itertools.combinations(imaginary, 2):
        x = add(unit(a), unit(b))
        for c in imaginary:
            y = unit(c)
            left += mul(x, mul(x, y)) != mul(mul(x, x), y)
            right += mul(mul(y, x), x) != mul(y, mul(x, x))
            flexible += mul(mul(x, y), x) != mul(x, mul(y, x))
    return {
        "plane": plane,
        "sorted_nonassoc": sum(1 for t in triples if fails(*t)),
        "ordered_nonassoc": sum(1 for p in itertools.permutations(imaginary, 3) if fails(*p)),
        "left_alt_fail": left,
        "right_alt_fail": right,
        "flex_fail": flexible,
    }


def components(adjacency: dict[tuple[int, int], set[tuple[int, int]]]) -> list[list[tuple[int, int]]]:
    seen: set[tuple[int, int]] = set()
    result = []
    for start in sorted(adjacency):
        if start in seen:
            continue
        component: set[tuple[int, int]] = set()
        stack = [start]
        while stack:
            node = stack.pop()
            if node not in component:
                component.add(node)
                stack.extend(adjacency[node] - component)
        seen |= component
        result.append(sorted(component))
    return result


def census() -> dict[str, object]:
    out: dict[str, object] = {}
    indices = range(DIM)
    imaginary = range(1, DIM)
    out["dim8_check"] = sum(1 for t in itertools.product(range(8), repeat=3) if fails(*t))
    out["ordered_nonassoc_4096"] = sum(1 for t in itertools.product(indices, repeat=3) if fails(*t))
    out["noncommuting_ordered_imag_pairs"] = sum(
        1 for a in imaginary for b in imaginary if a != b and SIGN[a][b] != SIGN[b][a]
    )
    triples = list(itertools.combinations(imaginary, 3))
    lines = [t for t in triples if t[0] ^ t[1] ^ t[2] == 0]
    out["lines"] = len(lines)
    out["sorted_triples"] = len(triples)
    out["sorted_nonassoc"] = sum(1 for t in triples if fails(*t))
    out["sorted_noncollinear_assoc"] = sum(1 for t in triples if t not in lines and not fails(*t))
    histogram: dict[int, int] = {}
    for t in triples:
        orders = sum(1 for p in itertools.permutations(t) if fails(*p))
        histogram[orders] = histogram.get(orders, 0) + 1
    out["orders_nonassoc_hist"] = histogram

    planes = sorted({s for s in (span(list(g)) for g in itertools.combinations(imaginary, 3)) if len(s) == 8})
    pairs = list(itertools.combinations(planes, 2))
    out["planes"] = len(planes)
    out["plane_pairs"] = len(pairs)
    out["plane_pair_intersections"] = sorted({len(set(a) & set(b)) for a, b in pairs})
    out["lines_per_plane"] = sorted({sum(1 for line in lines if set(line) <= set(p)) for p in planes})
    out["planes_per_line"] = sorted({sum(1 for p in planes if set(line) <= set(p)) for line in lines})
    out["shared_lines_per_plane_pair"] = sorted(
        {sum(1 for line in lines if set(line) <= set(a) & set(b)) for a, b in pairs}
    )
    records = [plane_record(p) for p in planes]
    out["plane_info"] = records

    blades: list[Blade] = [(i, j, s) for i in indices for j in range(i + 1, DIM) for s in (1, -1)]
    edges: dict[frozenset[tuple[int, int]], tuple[int, ...]] = {}
    zero_products = 0
    for (i, j, s), (k, m, t) in itertools.product(blades, blades):
        if not any(mul(add(unit(i), unit(j, s)), add(unit(k), unit(m, t)))):
            zero_products += 1
            edges[frozenset([(i, j), (k, m)])] = span([i, j, k, m])
    out["ordered_signed_zero_products"] = zero_products
    out["unordered_assessor_edges"] = len(edges)
    out["edge_span_sizes"] = sorted({len(carrier) for carrier in edges.values()})
    per_plane: dict[tuple[int, ...], int] = {}
    for carrier in edges.values():
        per_plane[carrier] = per_plane.get(carrier, 0) + 1
    nonassoc = {r["plane"]: r["sorted_nonassoc"] for r in records}
    out["edges_per_plane"] = [
        {"plane": p, "edges": n, "sorted_nonassoc": nonassoc.get(p)} for p, n in sorted(per_plane.items())
    ]

    assessors = sorted({a for edge in edges for a in edge})
    out["assessors"] = len(assessors)
    out["assessor_xor_keys"] = sorted({i ^ j for i, j in assessors})
    adjacency: dict[tuple[int, int], set[tuple[int, int]]] = {a: set() for a in assessors}
    for edge in edges:
        a, b = tuple(edge)
        adjacency[a].add(b)
        adjacency[b].add(a)
    out["kites"] = [
        {
            "assessors": kite,
            "xor_keys": sorted({i ^ j for i, j in kite}),
            "planes": sorted({edges[edge] for edge in edges if edge <= set(kite)}),
        }
        for kite in components(adjacency)
    ]
    return out


if __name__ == "__main__":
    print(json.dumps(census(), sort_keys=True))
