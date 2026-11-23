"""Exact census of the sedenion index planes, written before the Rocq source.

The sign function is the recursion of gororoba-quantum cd_core.cd_sign and of
gororoba-open cd_basis_mul_sign (the two agree line for line). The script
prints one JSON object; it reads no file and takes no argument.

The first block of the output recomputes each conjunct of the theorems of
rocq/open/verified/C582_IndexPlaneIncidence.v; the level counts, the octet
enumeration, the point-pair count, the basis alternativity check and the
plane and key cells were added after the first run, to cover every conjunct.

Predictions recorded before the first run, each confirmed by it:
ordered nonassociating basis triples 1848 of 4096; noncommuting ordered
imaginary pairs 210; 35 lines; 15 planes; every pair of planes shares 4
indices and one line; 252 sorted triples fail to associate; 8 planes hold 28
of them and 7 planes hold 4; left alternativity on two-term elements fails in
exactly those 7 planes; 336 ordered signed zero products of 2-blades on 84
unordered assessor pairs; every such pair spans one of the 7 planes, 12
unordered pairs (48 ordered signed products) per plane.
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


def level_counts(level: int) -> tuple[int, int]:
    """Ordered nonassociating basis triples and noncommuting imaginary pairs of one level."""
    dim = 1 << level
    table = [[sign(dim, p, q) for q in range(dim)] for p in range(dim)]
    triples = sum(
        1
        for a, b, c in itertools.product(range(dim), repeat=3)
        if table[a][b] * table[a ^ b][c] != table[b][c] * table[a][b ^ c]
    )
    pairs = sum(1 for a in range(1, dim) for b in range(1, dim) if a != b and table[a][b] != table[b][a])
    return triples, pairs


def closed_octets() -> tuple[int, list[tuple[int, ...]]]:
    """The number of 8-element index sets containing 0, and those closed under xor."""
    octets = [(0, *rest) for rest in itertools.combinations(range(1, DIM), 7)]
    closed = [o for o in octets if all((x ^ y) in o for x in o for y in o)]
    return len(octets), closed


def parity_plane(u: int) -> tuple[int, ...]:
    """The index set {i | parity(u land i) = 0}, the plane of the Rocq source."""
    return tuple(i for i in range(DIM) if (u & i).bit_count() % 2 == 0)


def fano_form(u: int) -> bool:
    """Whether the plane of u is 0, a line of 1..7, and 8 xor i for the i of 1..7 off that line."""
    plane = parity_plane(u)
    low = [i for i in plane if 1 <= i <= 7]
    high = [8 ^ i for i in range(1, 8) if i not in low]
    return len(low) == 3 and low[0] ^ low[1] == low[2] and plane == (0, *low, *high)


def census() -> dict[str, object]:
    out: dict[str, object] = {}
    indices = range(DIM)
    imaginary = range(1, DIM)
    for level in (2, 3, 4):
        triples_failing, pairs_failing = level_counts(level)
        out[f"level{level}_ordered_nonassoc"] = triples_failing
        out[f"level{level}_noncommuting"] = pairs_failing
    out["basis_units_alternate"] = all(not fails(a, a, b) and not fails(a, b, b) for a in indices for b in indices)
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
    out["lines_are_the_triples_failing_in_no_order"] = all(
        (t in lines) == (not any(fails(*p) for p in itertools.permutations(t))) for t in triples
    )
    out["sorted_failure_iff_all_orders"] = all(
        fails(*t) == all(fails(*p) for p in itertools.permutations(t)) for t in triples
    )

    planes = sorted({s for s in (span(list(g)) for g in itertools.combinations(imaginary, 3)) if len(s) == 8})
    by_u = {u: parity_plane(u) for u in imaginary}
    out["parity_planes_distinct"] = len(set(by_u.values()))
    out["parity_planes_are_the_spans"] = sorted(by_u.values()) == planes
    out["planes_per_nonline_triple"] = sorted(
        {sum(1 for p in planes if set(t) <= set(p)) for t in triples if t not in lines}
    )
    out["failing_triples_by_u"] = {
        u: sum(1 for t in triples if set(t) <= set(p) and fails(*t)) for u, p in sorted(by_u.items())
    }
    out["late_planes_have_fano_form"] = all(fano_form(u) for u in range(9, 16))
    out["late_low_parts_are_the_octonion_lines"] = sorted(
        tuple(i for i in by_u[u] if 1 <= i <= 7) for u in range(9, 16)
    ) == sorted(t for t in itertools.combinations(range(1, 8), 3) if t[0] ^ t[1] == t[2])
    octet_count, closed = closed_octets()
    out["octets"] = octet_count
    out["closed_octets"] = len(closed)
    out["closed_octets_are_planes"] = sorted(closed) == planes
    out["lines_per_point_pair"] = sorted(
        {sum(1 for line in lines if a in line and b in line) for a, b in itertools.combinations(imaginary, 2)}
    )
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
    cells: dict[tuple[tuple[int, ...], int], int] = {}
    keys_agree = True
    for (i, j, s), (k, m, t) in itertools.product(blades, blades):
        if not any(mul(add(unit(i), unit(j, s)), add(unit(k), unit(m, t)))):
            zero_products += 1
            carrier = span([i, j, k, m])
            edges[frozenset([(i, j), (k, m)])] = carrier
            keys_agree = keys_agree and (i ^ j) == (k ^ m)
            cells[(carrier, i ^ j)] = cells.get((carrier, i ^ j), 0) + 1
    out["carriers_are_the_late_planes"] = {p for p, _ in cells} == {by_u[u] for u in range(9, 16)}
    out["zero_product_keys_agree"] = keys_agree
    out["plane_key_cells"] = len(cells)
    out["signed_products_per_cell"] = sorted(set(cells.values()))
    out["signed_products_per_plane"] = sorted(
        {sum(n for (p, _), n in cells.items() if p == plane) for plane in {p for p, _ in cells}}
    )
    out["cells_only_where_key_in_plane"] = all(key in plane for plane, key in cells)
    out["keys_per_plane"] = sorted({sum(1 for p, _ in cells if p == plane) for plane in {p for p, _ in cells}})
    out["planes_per_key"] = sorted({sum(1 for _, k in cells if k == key) for key in {k for _, k in cells}})
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
