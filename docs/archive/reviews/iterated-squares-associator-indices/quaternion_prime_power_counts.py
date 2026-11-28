"""Square-zero and idempotent counts of the quaternions over F_4, F_8, F_9, F_25 and F_27.

The record extends the prime-field counts of gororoba-quantum's findings row A5-662 to fields of
prime-power order, the falsifier named by pool row PROOF-75. The quaternions A_2 over F_q are
built by the Cayley-Dickson doubling (a, b)(c, d) = (ac - d* b, da + b c*) with the identity as
the star of F_q, so e_i e_j = s(i, j) e_(i ^ j) with s read from the doubled product of basis
vectors over the integers, and the table is checked to be associative. Every element of F_q^4 is
enumerated, and the record checks, for odd q:

- x * x = 0 exactly when re x = 0 and N(x) = 0, with N(x) the sum of the squared coordinates;
- the elements with x * x = 0 number q^2 (prediction q^(2^n - 2) at n = 2);
- the elements with (x * x) * (x * x) = 0 are the same set;
- the idempotents other than 0 and 1 number q^2 + q (prediction q^(2^n - 2) + q^(2^(n-1) - 1)).

For even q (a reviewer conjecture of the record) it checks q^3 square-zero elements, the same
set for the fourth power, no idempotent other than 0 and 1, and q^3 - q^2 elements with x * x = 0
outside re x = 0 and N(x) = 0.

Controls: the product with s(1, 2) negated changes both counts at q = 9, so the enumeration reads
the sign table; negating s(1, 2) and s(2, 1) together leaves every square unchanged, and the
associativity check rejects that table. Arithmetic is exact over integer tables of F_q; no random
draw enters.
"""

from __future__ import annotations

import itertools
import sys

# Each field: characteristic p and the monic irreducible polynomial m(t) of degree e, listed by
# its coefficients of t^0 .. t^(e - 1) in t^e = -(c_0 + c_1 t + ...).
FIELDS = {4: (2, (1, 1)), 8: (2, (1, 1, 0)), 9: (3, (1, 0)), 25: (5, (3, 0)), 27: (3, (2, 2, 0))}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise RuntimeError(message)


def field_tables(q: int) -> tuple[list[list[int]], list[list[int]]]:
    """Addition and multiplication tables of F_q on the integers 0 .. q - 1, whose base-p digits,
    lowest first, are the coefficients of 1, t, t^2, ..., so index 0 is zero and index 1 is one."""
    p, low = FIELDS[q]
    e = len(low)
    elems = [v[::-1] for v in itertools.product(range(p), repeat=e)]
    index = {v: i for i, v in enumerate(elems)}

    def mul(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
        prod = [0] * (2 * e - 1)
        for i, ai in enumerate(a):
            for j, bj in enumerate(b):
                prod[i + j] += ai * bj
        for d in range(2 * e - 2, e - 1, -1):
            c = prod[d]
            prod[d] = 0
            for j, lj in enumerate(low):
                prod[d - e + j] -= c * lj
        return tuple(x % p for x in prod[:e])

    add_t = [[index[tuple((x + y) % p for x, y in zip(a, b, strict=True))] for b in elems] for a in elems]
    mul_t = [[index[mul(a, b)] for b in elems] for a in elems]
    nonzero = range(1, q)
    require(all(mul_t[1][a] == a for a in range(q)), f"F_{q}: index 1 is not the unit")
    require(all(any(mul_t[a][b] == 1 for b in nonzero) for a in nonzero), f"F_{q}: not a field")
    return add_t, mul_t


def sign_table(n: int) -> list[list[int]]:
    """s(i, j) with e_i e_j = s(i, j) e_(i ^ j) in A_n over the integers."""

    def conj(x: list[int]) -> list[int]:
        return [x[0]] + [-c for c in x[1:]]

    def mult(x: list[int], y: list[int]) -> list[int]:
        if len(x) == 1:
            return [x[0] * y[0]]
        h = len(x) // 2
        a, b, c, d = x[:h], x[h:], y[:h], y[h:]
        left = [u - v for u, v in zip(mult(a, c), mult(conj(d), b), strict=True)]
        right = [u + v for u, v in zip(mult(d, a), mult(b, conj(c)), strict=True)]
        return left + right

    dim = 1 << n
    basis = [[int(i == j) for j in range(dim)] for i in range(dim)]
    table = []
    for i in range(dim):
        row = []
        for j in range(dim):
            prod = mult(basis[i], basis[j])
            require(sum(abs(c) for c in prod) == 1 and prod[i ^ j] in (1, -1), "sign table")
            row.append(prod[i ^ j])
        table.append(row)
    return table


def is_associative(signs: list[list[int]]) -> bool:
    """Whether e_i (e_j e_k) = (e_i e_j) e_k for every basis triple of the signed table."""
    dim = len(signs)
    return all(
        signs[j][k] * signs[i][j ^ k] == signs[i][j] * signs[i ^ j][k]
        for i in range(dim)
        for j in range(dim)
        for k in range(dim)
    )


def mutated_signs(flips: tuple[tuple[int, int], ...]) -> list[list[int]]:
    signs = sign_table(2)
    for i, j in flips:
        signs[i][j] = -signs[i][j]
    return signs


def counts(q: int, signs: list[list[int]]) -> dict[str, int]:
    add_t, mul_t = field_tables(q)
    neg = [next(b for b in range(q) if add_t[a][b] == 0) for a in range(q)]

    def product(x: tuple[int, ...], y: tuple[int, ...]) -> tuple[int, ...]:
        out = [0] * 4
        for i in range(4):
            for j in range(4):
                term = mul_t[x[i]][y[j]]
                out[i ^ j] = add_t[out[i ^ j]][term if signs[i][j] == 1 else neg[term]]
        return tuple(out)

    zero, one = (0, 0, 0, 0), (1, 0, 0, 0)
    nil2 = nil4 = idem = mismatch = 0
    for x in itertools.product(range(q), repeat=4):
        sq = product(x, x)
        norm = 0
        for c in x:
            norm = add_t[norm][mul_t[c][c]]
        predicate = x[0] == 0 and norm == 0
        nil2 += sq == zero
        nil4 += product(sq, sq) == zero
        mismatch += (sq == zero) != predicate
        idem += sq == x and x not in (zero, one)
    return {"nil2": nil2, "nil4": nil4, "idempotents": idem, "predicate_mismatches": mismatch}


def predicted(q: int) -> dict[str, int]:
    """Odd q: A5-662 at n = 2. Even q: x * x = N(x) 1 with N(x) = (sum of the coordinates)^2, so
    x * x = 0 on a hyperplane, re x = 0 and N(x) = 0 on a plane inside it, and no idempotent other
    than 0 and 1 (Tower.mul_self_eq_self_iff_of_two_eq_zero)."""
    if q % 2:
        return {"nil2": q**2, "nil4": q**2, "idempotents": q**2 + q, "predicate_mismatches": 0}
    return {"nil2": q**3, "nil4": q**3, "idempotents": 0, "predicate_mismatches": q**3 - q**2}


def main() -> int:
    table = sign_table(2)
    require(is_associative(table), "the quaternion sign table is not associative")
    for q in FIELDS:
        got = counts(q, table)
        want = predicted(q)
        require(got == want, f"F_{q}: {got} against {want}")
        print(f"F_{q}: {got}")
    single = counts(9, mutated_signs(((1, 2),)))
    require(
        single["nil2"] != 81 and single["idempotents"] != 90,
        f"control: the table with s(1, 2) negated kept the counts {single}",
    )
    print(f"F_9 control, s(1, 2) negated: {single}")
    # Squares read only s(i, j) + s(j, i), so a paired flip keeps every count; the associativity
    # check of the table rejects it.
    paired = mutated_signs(((1, 2), (2, 1)))
    require(not is_associative(paired), "control: the paired flip kept an associative table")
    require(counts(9, paired) == predicted(9), "control: the paired flip changed a square")
    print("F_9 control, s(1, 2) and s(2, 1) negated: counts unchanged, table not associative")
    return 0


if __name__ == "__main__":
    sys.exit(main())
