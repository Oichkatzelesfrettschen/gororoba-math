"""Generate and check the Rocq certificate of the conjugation map Phi between the two E8-bar Rees scripts.

The input is conjugation_map.sing of docs/evidence/a5-exceptional-fibers/working/runs/e8-rees-fibers-v3-open-cells/
conjugation of the gororoba-quantum checkout that GOROROBA_QUANTUM names, pinned by its sha256 (a file with another
digest is refused). The script holds the 15 x 15 skew matrices C of the N- and N+ Rees data with entries linear in i
and s1..s9, the matrices F, the substitution Phi (i -> -i, s4 -> -s5, s5 -> s4, s7 <-> s8, the other variables fixed)
and the sign vectors D and E; T = F^t C F has the pivot block B (rows and columns 1..6).

E8ConjugationMap.v (rocq/quantum) carries C and F of both signs as sparse polynomials over Z in the variables
v1 = i, v2..v10 = s1..s9, the block B of T = F^t C F reduced modulo i^2 + 1 with the cofactors E of its entries
(T - B = (v1^2 + 1) E), and R of each sign, the cofactor with detB - closed form = (v1^2 + 1) R. This generator
recomputes every identity in exact integer arithmetic before it renders: D Phi(C-) D = -C+ and D Phi(F-) E = F+
entrywise with i free (no reduction by i^2 + 1), and detB = -1024 (s2^2 - 1)^2 (s2 -+ i)^2 modulo i^2 + 1, with R
the exact quotient. A failing identity ends the run with status 1 and names the entry.

--write regenerates the source in rocq/quantum of this checkout; --check compares that file with a fresh render.
"""

from __future__ import annotations

import argparse
import hashlib
import re
import sys

from quantum_checkout import ROCQ, ROOT

SING = (
    ROOT
    / "docs/evidence/a5-exceptional-fibers/working/runs/e8-rees-fibers-v3-open-cells/conjugation/conjugation_map.sing"
)
SING_SHA256 = "a1d7278b251e39c907641276ddee0d94919ffefa8613ad9863a2ff4e262d01ed"
PROOF_NAME = "E8ConjugationMap.v"
N = 15
PIVOT = 6
VARIABLES = ["i", *[f"s{k}" for k in range(1, 10)]]
NVAR = len(VARIABLES)
# Phi on variable positions 0..9 (i, s1..s9): the target position and the sign.
EXPECTED_PHI = {0: (0, -1), 4: (5, -1), 5: (4, 1), 7: (8, 1), 8: (7, 1)}

Poly = dict[tuple[int, ...], int]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def clean(p: Poly) -> Poly:
    return {m: c for m, c in p.items() if c != 0}


def const(c: int) -> Poly:
    return {(0,) * NVAR: c} if c else {}


def var(k: int) -> Poly:
    e = [0] * NVAR
    e[k] = 1
    return {tuple(e): 1}


def add(p: Poly, q: Poly) -> Poly:
    r = dict(p)
    for m, c in q.items():
        r[m] = r.get(m, 0) + c
    return clean(r)


def neg(p: Poly) -> Poly:
    return {m: -c for m, c in p.items()}


def scale(k: int, p: Poly) -> Poly:
    return clean({m: k * c for m, c in p.items()})


def mul(p: Poly, q: Poly) -> Poly:
    r: Poly = {}
    for m, c in p.items():
        for n, d in q.items():
            key = tuple(a + b for a, b in zip(m, n, strict=True))
            r[key] = r.get(key, 0) + c * d
    return clean(r)


def power(p: Poly, n: int) -> Poly:
    r = const(1)
    for _ in range(n):
        r = mul(r, p)
    return r


TOKEN = re.compile(r"\s*(\d+|[A-Za-z_]\w*|[-+*^()])")


def parse_poly(text: str) -> Poly:
    """Parse a Singular polynomial over Q[i, s1..s9] with integer coefficients."""
    tokens: list[str] = []
    position = 0
    text = text.strip()
    while position < len(text):
        match = TOKEN.match(text, position)
        require(match is not None, f"unreadable polynomial near {text[position : position + 20]!r}")
        if match is None:
            raise AssertionError
        tokens.append(match.group(1))
        position = match.end()
    index = 0

    def peek() -> str | None:
        return tokens[index] if index < len(tokens) else None

    def take() -> str:
        nonlocal index
        require(index < len(tokens), "polynomial ends early")
        index += 1
        return tokens[index - 1]

    def atom() -> Poly:
        symbol = take()
        if symbol == "(":
            inner = expression()
            require(take() == ")", "unbalanced parenthesis")
            value = inner
        elif symbol.isdigit():
            value = const(int(symbol))
        else:
            require(symbol in VARIABLES, f"unknown variable {symbol}")
            value = var(VARIABLES.index(symbol))
        if peek() == "^":
            take()
            exponent = take()
            require(exponent.isdigit(), "exponent is no integer")
            value = power(value, int(exponent))
        return value

    def factor() -> Poly:
        if peek() == "-":
            take()
            return neg(factor())
        if peek() == "+":
            take()
        return atom()

    def term() -> Poly:
        value = factor()
        while peek() == "*":
            take()
            value = mul(value, factor())
        return value

    def expression() -> Poly:
        value = term()
        while peek() in ("+", "-"):
            sign = take()
            rhs = term()
            value = add(value, rhs if sign == "+" else neg(rhs))
        return value

    result = expression()
    require(index == len(tokens), "trailing tokens after polynomial")
    return result


def read_sing() -> str:
    data = SING.read_bytes()
    require(hashlib.sha256(data).hexdigest() == SING_SHA256, "conjugation_map.sing has another sha256 than the pin")
    return data.decode("utf-8")


def parse_matrices(text: str) -> tuple[dict[str, list[list[Poly]]], dict[str, list[list[Poly]]]]:
    """C and F of the N- block and of the N+ block, as 0-based tables."""
    blocks = text.split("matrix C[15][15];")
    require(len(blocks) == 3, "the script holds two C blocks")
    cs: dict[str, list[list[Poly]]] = {}
    fs: dict[str, list[list[Poly]]] = {}
    for sign, block in zip(("m", "p"), blocks[1:], strict=True):
        c_text, rest = block.split("matrix F[15][15];")
        f_text = rest.split("matrix T=")[0]
        c: list[list[Poly]] = [[{} for _ in range(N)] for _ in range(N)]
        seen = 0
        for a, b, expression in re.findall(r"C\[(\d+),(\d+)\]=([^;]*);\s*C\[\d+,\d+\]=-C\[\d+,\d+\];", c_text):
            value = parse_poly(expression)
            c[int(a) - 1][int(b) - 1] = value
            c[int(b) - 1][int(a) - 1] = neg(value)
            seen += 1
        require(seen == N * (N - 1) // 2, f"C of sign {sign} has {seen} upper entries")
        f: list[list[Poly]] = [[{} for _ in range(N)] for _ in range(N)]
        for a, b, expression in re.findall(r"F\[(\d+),(\d+)\]=([^;]*);", f_text):
            f[int(a) - 1][int(b) - 1] = parse_poly(expression)
        cs[sign], fs[sign] = c, f
    return cs, fs


def parse_conjugation(text: str) -> tuple[dict[int, tuple[int, int]], list[int], list[int]]:
    """Phi as position -> (target position, sign), and the diagonals of D and E."""
    images = re.search(r"map Phi=r,([^;]*);", text)
    require(images is not None, "the script holds no map Phi")
    if images is None:
        raise AssertionError
    phi: dict[int, tuple[int, int]] = {}
    for position, image in enumerate(images.group(1).split(",")):
        image = image.strip()
        sign = -1 if image.startswith("-") else 1
        name = image.lstrip("-")
        require(name in VARIABLES, f"Phi sends variable {position} to {image}")
        if (VARIABLES.index(name), sign) != (position, 1):
            phi[position] = (VARIABLES.index(name), sign)
    require(phi == EXPECTED_PHI, f"Phi differs from the stated substitution: {phi}")
    diagonals = []
    for name in ("dv", "ev"):
        found = re.search(rf"intvec {name}=([^;]*);", text)
        require(found is not None, f"the script holds no intvec {name}")
        if found is None:
            raise AssertionError
        values = [int(x) for x in found.group(1).split(",")]
        require(len(values) == N and all(v in (-1, 1) for v in values), f"{name} is no sign vector of length {N}")
        diagonals.append(values)
    return phi, diagonals[0], diagonals[1]


def substitute(p: Poly, phi: dict[int, tuple[int, int]]) -> Poly:
    """Phi applied to p: each variable goes to its signed target."""
    r: Poly = {}
    for m, c in p.items():
        key = [0] * NVAR
        sign = 1
        for position, exponent in enumerate(m):
            target, s = phi.get(position, (position, 1))
            key[target] += exponent
            sign *= s**exponent
        r[tuple(key)] = r.get(tuple(key), 0) + sign * c
    return clean(r)


def matmul(a: list[list[Poly]], b: list[list[Poly]]) -> list[list[Poly]]:
    size = len(a)
    out: list[list[Poly]] = [[{} for _ in range(len(b[0]))] for _ in range(size)]
    for i in range(size):
        for k in range(len(b)):
            if not a[i][k]:
                continue
            for j in range(len(b[0])):
                if b[k][j]:
                    out[i][j] = add(out[i][j], mul(a[i][k], b[k][j]))
    return out


def transpose(a: list[list[Poly]]) -> list[list[Poly]]:
    return [[a[j][i] for j in range(len(a))] for i in range(len(a[0]))]


def determinant(m: list[list[Poly]]) -> Poly:
    """Laplace expansion along the first row, over the column subsets of the remaining rows."""
    size = len(m)
    memo: dict[tuple[int, tuple[int, ...]], Poly] = {}

    def minor(row: int, cols: tuple[int, ...]) -> Poly:
        if row == size:
            return const(1)
        key = (row, cols)
        if key not in memo:
            total: Poly = {}
            for position, column in enumerate(cols):
                rest = cols[:position] + cols[position + 1 :]
                term = mul(m[row][column], minor(row + 1, rest))
                total = add(total, term if position % 2 == 0 else neg(term))
            memo[key] = total
        return memo[key]

    return minor(0, tuple(range(size)))


def reduce_by_i_squared(p: Poly) -> tuple[Poly, Poly]:
    """Return (remainder, quotient) of p modulo i^2 + 1, with p = remainder + (i^2 + 1) quotient."""
    work = dict(p)
    quotient: Poly = {}
    while True:
        high = [m for m in work if m[0] >= 2]
        if not high:
            return clean(work), clean(quotient)
        for m in high:
            c = work.pop(m, 0)
            if c == 0:
                continue
            lowered = (m[0] - 2, *m[1:])
            quotient[lowered] = quotient.get(lowered, 0) + c
            work[lowered] = work.get(lowered, 0) - c
        work = clean(work)


def closed_form(sign: int) -> Poly:
    """-1024 (s2^2 - 1)^2 (s2 - sign i)^2 with sign = +1 for N- and -1 for N+."""
    s2 = var(2)
    q = add(mul(s2, s2), const(-1))
    t = add(s2, scale(-sign, var(0)))
    return scale(-1024, mul(mul(q, q), mul(t, t)))


def pivot_data(
    c: list[list[Poly]], f: list[list[Poly]], sign: int, label: str
) -> tuple[list[list[Poly]], list[list[Poly]], Poly]:
    """The block B of T = F^t C F reduced modulo i^2 + 1, the entry cofactors, and the cofactor of detB."""
    t = matmul(matmul(transpose(f), c), f)
    reduced: list[list[Poly]] = [[{} for _ in range(PIVOT)] for _ in range(PIVOT)]
    cofactors: list[list[Poly]] = [[{} for _ in range(PIVOT)] for _ in range(PIVOT)]
    for a in range(PIVOT):
        for b in range(PIVOT):
            reduced[a][b], cofactors[a][b] = reduce_by_i_squared(t[a][b])
    det = determinant(reduced)
    remainder, quotient = reduce_by_i_squared(add(det, neg(closed_form(sign))))
    require(not remainder, f"detB of {label} differs from its closed form modulo i^2 + 1")
    return reduced, cofactors, quotient


def monomial(m: tuple[int, ...]) -> str:
    variables = [str(k + 1) for k, e in enumerate(m) for _ in range(e)]
    return "[" + "; ".join(variables) + "]"


def render_poly(p: Poly) -> str:
    if not p:
        return "[]"
    parts = []
    for m in sorted(p, reverse=True):
        c = p[m]
        coefficient = f"({c})%Z" if c < 0 else f"{c}%Z"
        parts.append(f"({coefficient}, {monomial(m)})")
    return "[" + "; ".join(parts) + "]"


def render_table(name: str, table: list[list[Poly]]) -> str:
    rows = ["  [" + "; ".join(render_poly(entry) for entry in row) + "]" for row in table]
    return f"Definition {name} : list (list SPoly) := [\n" + ";\n".join(rows) + "\n].\n"


def render_z_list(name: str, values: list[int]) -> str:
    return f"Definition {name} : list Z := [" + "; ".join(f"({v})%Z" if v < 0 else f"{v}%Z" for v in values) + "].\n"


def verify(
    cs: dict[str, list[list[Poly]]],
    fs: dict[str, list[list[Poly]]],
    phi: dict[int, tuple[int, int]],
    dv: list[int],
    ev: list[int],
) -> None:
    for a in range(N):
        for b in range(N):
            expected = scale(-dv[a] * dv[b], substitute(cs["m"][a][b], phi))
            require(cs["p"][a][b] == expected, f"D Phi(C-) D + C+ is nonzero at ({a + 1}, {b + 1})")
            expected = scale(dv[a] * ev[b], substitute(fs["m"][a][b], phi))
            require(fs["p"][a][b] == expected, f"D Phi(F-) E - F+ is nonzero at ({a + 1}, {b + 1})")


def certificate_text() -> str:
    text = read_sing()
    cs, fs = parse_matrices(text)
    phi, dv, ev = parse_conjugation(text)
    verify(cs, fs, phi, dv, ev)
    block_m, entries_m, quotient_m = pivot_data(cs["m"], fs["m"], 1, "N-")
    block_p, entries_p, quotient_p = pivot_data(cs["p"], fs["p"], -1, "N+")
    data = "\n".join(
        [
            render_table("CmRows", cs["m"]),
            render_table("CpRows", cs["p"]),
            render_table("FmRows", fs["m"]),
            render_table("FpRows", fs["p"]),
            render_table("BmRows", block_m),
            render_table("BpRows", block_p),
            render_table("EmRows", entries_m),
            render_table("EpRows", entries_p),
            render_z_list("dsgList", dv),
            render_z_list("esgList", ev),
            f"Definition Rm : SPoly := {render_poly(quotient_m)}.\n",
            f"Definition Rp : SPoly := {render_poly(quotient_p)}.\n",
        ]
    )
    return TEMPLATE.replace("(*DATA*)", data)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--write", action="store_true")
    mode.add_argument("--check", action="store_true")
    arguments = parser.parse_args()
    try:
        text = certificate_text()
        path = ROCQ / PROOF_NAME
        if arguments.write:
            path.write_text(text, encoding="utf-8")
            return 0
        require(path.read_text(encoding="utf-8") == text, f"{PROOF_NAME} differs from a fresh render; run --write")
    except (ValueError, OSError) as error:
        print(f"conjugation map certificate: {error}", file=sys.stderr)
        return 1
    print("conjugation map certificate: C, F, detB identities and the Rocq source agree with conjugation_map.sing")
    return 0


TEMPLATE = r"""(** * The conjugation map Phi between the two E8-bar Rees scripts, as a certificate.

    Generated by ci/quantum-sources/conjugation_map_certificate.py from conjugation_map.sing; the generator
    recomputes every identity below in exact integer arithmetic before it renders.

    Convention. Polynomials over Z are sparse lists SPoly of monomials (c, [v1; ...; vn]), the variable index
    1 being i and the indices 2 .. 10 being s1 .. s9; a monomial is the product of its listed variables with
    repetition. A ring D with a square root of -1 (CdTowerRing.CommutativeRingWithI) receives a polynomial at a
    point xv : nat -> D.t, the value xv j standing for variable j, through the canonical map Z -> D.
    Cm, Cp are the 15 x 15 skew matrices C of the N- and N+ scripts and Fm, Fp their matrices F, indexed from 0;
    T = F^t C F and B is the block of T on the indices 0 .. 5. detD is the Laplace expansion along the first row.

    Phi is the substitution i -> -i, s4 -> -s5, s5 -> s4, s7 <-> s8 (variable indices 1, 5, 6, 8, 9), the
    other variables fixed. PhiSP applies it to a polynomial; its evaluation lemma evSP_Phi states that PhiSP p at
    xv equals p at phix xv, so PhiSP is the endomorphism of the polynomial ring dual to the point map phix of
    every D. The point map has order 4 (phix_order4) and its square negates the s4 and s5 coordinates only
    (phix_square), so PhiSP is an automorphism of order 4 whose inverse is PhiSP applied three times.
    D = diag(dsg) and E = diag(esg) are the sign matrices of the identities
    D Phi(C-) D = -C+ (conj_C) and D Phi(F-) E = F+ (conj_F), which hold entrywise for the free variable i.
    detB of each sign equals -1024 (s2^2 - 1)^2 (s2 -+ i)^2 in every ring with i^2 = -1 (detB_Nm, detB_Np), the
    reduction by i^2 + 1 being the explicit cofactor Rm, Rp that the checks detm_ok and detp_ok verify, and
    Phi(detB-) = detB+ follows (detB_conj).

    The reflection pattern is that of StiefelA5Certificate.v and StiefelA5Pfaffian.v: the polynomials are
    Ring_polynom.Pol over Z, peq decides an identity by vm_compute, and ev_peq turns it into an identity of D. *)

From Stdlib Require Import ZArith List Ring Ring_polynom Ring_theory InitialRing PeanoNat Lia Bool.
Require Import CdTowerRing Pfaffian StiefelA5Certificate StiefelA5Pfaffian.
Import ListNotations.

Definition SPoly := list (Z * list nat).

(*DATA*)

Definition Cm (a b : nat) : SPoly := nth b (nth a CmRows []) [].
Definition Cp (a b : nat) : SPoly := nth b (nth a CpRows []) [].
Definition Fm (a b : nat) : SPoly := nth b (nth a FmRows []) [].
Definition Fp (a b : nat) : SPoly := nth b (nth a FpRows []) [].
Definition Bm (a b : nat) : SPoly := nth b (nth a BmRows []) [].
Definition Bp (a b : nat) : SPoly := nth b (nth a BpRows []) [].
Definition Em (a b : nat) : SPoly := nth b (nth a EmRows []) [].
Definition Ep (a b : nat) : SPoly := nth b (nth a EpRows []) [].
Definition dsg (a : nat) : Z := nth a dsgList 1%Z.
Definition esg (a : nat) : Z := nth a esgList 1%Z.

Definition varP (j : nat) : ZP := pX (Pos.of_nat j).
Fixpoint monoP (vs : list nat) : ZP :=
  match vs with [] => pc 1%Z | v :: r => pmul (varP v) (monoP r) end.
Fixpoint toP (s : SPoly) : ZP :=
  match s with [] => pc 0%Z | (c, vs) :: r => padd (pmul (pc c) (monoP vs)) (toP r) end.

Definition wfv (v : nat) : bool := Nat.leb 1 v && Nat.leb v 10.
Definition wfb (s : SPoly) : bool := forallb (fun m => forallb wfv (snd m)) s.
Definition checkEq (p q : SPoly) : bool := wfb p && wfb q && peq (toP p) (toP q).

Definition phiv (j : nat) : nat * Z :=
  match j with
  | 1 => (1, (-1)%Z)
  | 5 => (6, (-1)%Z)
  | 6 => (5, 1%Z)
  | 8 => (9, 1%Z)
  | 9 => (8, 1%Z)
  | _ => (j, 1%Z)
  end.

Fixpoint signP (vs : list nat) : Z :=
  match vs with [] => 1%Z | v :: r => Z.mul (snd (phiv v)) (signP r) end.

Fixpoint PhiSP (s : SPoly) : SPoly :=
  match s with
  | [] => []
  | (c, vs) :: r => (Z.mul c (signP vs), map (fun v => fst (phiv v)) vs) :: PhiSP r
  end.

Fixpoint scaleSP (k : Z) (s : SPoly) : SPoly :=
  match s with [] => [] | (c, vs) :: r => (Z.mul k c, vs) :: scaleSP k r end.

Definition allpairsN (n : nat) (f : nat -> nat -> bool) : bool :=
  forallb (fun a => forallb (fun b => f a b) (seq 0 n)) (seq 0 n).
Definition allpairs : (nat -> nat -> bool) -> bool := allpairsN 15.

Definition Cfun (a b : nat) : bool :=
  checkEq (Cp a b) (scaleSP (Z.opp (Z.mul (dsg a) (dsg b))) (PhiSP (Cm a b))).
Definition Ffun (a b : nat) : bool :=
  checkEq (Fp a b) (scaleSP (Z.mul (dsg a) (esg b)) (PhiSP (Fm a b))).
Definition Wfun (a b : nat) : bool := wfb (Cm a b) && wfb (Cp a b) && wfb (Fm a b) && wfb (Fp a b).

Lemma CCheck_ok : allpairs Cfun = true.
Proof. vm_compute. reflexivity. Qed.

Lemma FCheck_ok : allpairs Ffun = true.
Proof. vm_compute. reflexivity. Qed.

Lemma WfData_ok : allpairs Wfun = true.
Proof. vm_compute. reflexivity. Qed.

(** The pivot block B of T = F^t C F over ZP, and its Laplace determinant. *)

Definition TP (C F : nat -> nat -> SPoly) (a b : nat) : ZP :=
  sumP 15 (fun k => sumP 15 (fun l => pmul (pmul (toP (F k a)) (toP (C k l))) (toP (F l b)))).

Fixpoint detP (M : nat -> nat -> ZP) (rows cols : list nat) : ZP :=
  match rows with
  | [] => pc 1%Z
  | r :: rs =>
      sumP (length cols) (fun k => pmul (pmul (sgnP k) (M r (nth k cols O))) (detP M rs (rem_at k cols)))
  end.

Definition sqP (p : ZP) : ZP := pmul p p.
Definition iP : ZP := varP 1.
Definition s2P : ZP := varP 3.
Definition qP : ZP := padd (sqP s2P) (popp (pc 1%Z)).
Definition clP (t : ZP) : ZP := pmul (pc (-1024)%Z) (pmul (sqP qP) (sqP t)).
Definition clm : ZP := clP (padd s2P (popp iP)).
Definition clp : ZP := clP (padd s2P iP).
Definition iiP : ZP := padd (sqP iP) (pc 1%Z).

Definition detBred (B : nat -> nat -> SPoly) : ZP := detP (fun a b => toP (B a b)) (seq 0 6) (seq 0 6).

Definition Tfun (C F B E : nat -> nat -> SPoly) (a b : nat) : bool :=
  wfb (B a b) && peq (padd (TP C F a b) (popp (toP (B a b)))) (pmul iiP (toP (E a b))).
Definition Tcheck (C F B E : nat -> nat -> SPoly) : bool := allpairsN 6 (Tfun C F B E).

Lemma Tm_ok : Tcheck Cm Fm Bm Em = true.
Proof. vm_compute. reflexivity. Qed.

Lemma Tp_ok : Tcheck Cp Fp Bp Ep = true.
Proof. vm_compute. reflexivity. Qed.

Lemma detm_ok : peq (padd (detBred Bm) (popp clm)) (pmul iiP (toP Rm)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma detp_ok : peq (padd (detBred Bp) (popp clp)) (pmul iiP (toP Rp)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma allpairsN_sound n f : allpairsN n f = true -> forall a b, (a < n)%nat -> (b < n)%nat -> f a b = true.
Proof.
  unfold allpairsN. intros H a b Ha Hb. rewrite forallb_forall in H.
  specialize (H a ltac:(apply in_seq; lia)). rewrite forallb_forall in H.
  apply H. apply in_seq. lia.
Qed.

Lemma allpairs_sound f : allpairs f = true -> forall a b, (a < 15)%nat -> (b < 15)%nat -> f a b = true.
Proof. exact (allpairsN_sound 15 f). Qed.

Lemma Forall_rem_at (P : nat -> Prop) (k : nat) (l : list nat) : Forall P l -> Forall P (rem_at k l).
Proof.
  revert k. induction l as [|x r IH]; intros k H; [exact H|].
  inversion H as [|y s Hx Hr]; subst. destruct k as [|k]; simpl; [exact Hr|].
  constructor; [exact Hx | apply IH; exact Hr].
Qed.

Lemma wfv_range v : wfv v = true -> 1 <= v /\ v <= 10.
Proof.
  unfold wfv. intros H. apply andb_prop in H as [H1 H2].
  apply Nat.leb_le in H1. apply Nat.leb_le in H2. split; assumption.
Qed.

Module ConjugationMap (D : CommutativeRingWithI).
Module SPf := StiefelPfaffian D.
Add Ring cj_ring : D.ring_th.

Definition envf (xv : nat -> D.t) : list D.t := map xv (seq 1 10).

Lemma phiZ_mul a b : SPf.phiZ (Z.mul a b) = D.mul (SPf.phiZ a) (SPf.phiZ b).
Proof. exact (morph_mul SPf.morph a b). Qed.

Lemma ev_pX_gen env j : SPf.ev env (pX j) = BinList.nth D.zero j env.
Proof. unfold pX, SPf.ev. symmetry. exact (mkX_ok SPf.Rsth SPf.Reqe SPf.ARth SPf.morph j env). Qed.

Lemma ev_varP xv j : 1 <= j /\ j <= 10 -> SPf.ev (envf xv) (varP j) = xv j.
Proof.
  intros H. unfold varP. rewrite ev_pX_gen. unfold envf.
  do 11 (destruct j as [|j]; [try lia; reflexivity|]). lia.
Qed.

Ltac evs :=
  repeat (first [rewrite SPf.ev_add | rewrite SPf.ev_mul | rewrite SPf.ev_opp | rewrite SPf.ev_pc]).
Ltac evs_in H :=
  repeat (first [rewrite SPf.ev_add in H | rewrite SPf.ev_mul in H | rewrite SPf.ev_opp in H
                | rewrite SPf.ev_pc in H]).

Lemma detB_close xv (det cl : ZP) (R : SPoly) :
  D.mul (xv 1) (xv 1) = D.opp D.one ->
  peq (padd det (popp cl)) (pmul iiP (toP R)) = true ->
  SPf.ev (envf xv) det = SPf.ev (envf xv) cl.
Proof.
  intros Hi Hp. pose proof (SPf.ev_peq (envf xv) _ _ Hp) as E.
  unfold iiP, sqP, iP in E. evs_in E.
  rewrite (ev_varP xv 1) in E by lia.
  rewrite SPf.phiZ_one, Hi in E.
  transitivity (D.add (D.add (SPf.ev (envf xv) det) (D.opp (SPf.ev (envf xv) cl))) (SPf.ev (envf xv) cl));
    [ring|].
  rewrite E. ring.
Qed.

Fixpoint evMono (xv : nat -> D.t) (vs : list nat) : D.t :=
  match vs with [] => D.one | v :: r => D.mul (xv v) (evMono xv r) end.

Fixpoint evSP (xv : nat -> D.t) (s : SPoly) : D.t :=
  match s with
  | [] => D.zero
  | (c, vs) :: r => D.add (D.mul (SPf.phiZ c) (evMono xv vs)) (evSP xv r)
  end.

Lemma ev_monoP xv vs : forallb wfv vs = true -> SPf.ev (envf xv) (monoP vs) = evMono xv vs.
Proof.
  induction vs as [|v r IH]; intros H.
  - cbn [monoP evMono]. rewrite SPf.ev_pc. exact SPf.phiZ_one.
  - cbn [forallb] in H. apply andb_prop in H as [H1 H2].
    cbn [monoP evMono]. rewrite SPf.ev_mul, (ev_varP xv v (wfv_range v H1)), (IH H2). reflexivity.
Qed.

Lemma ev_toP xv s : wfb s = true -> SPf.ev (envf xv) (toP s) = evSP xv s.
Proof.
  induction s as [|[c vs] r IH]; intros H.
  - cbn [toP evSP]. rewrite SPf.ev_pc. reflexivity.
  - unfold wfb in H. cbn [forallb snd] in H. apply andb_prop in H as [H1 H2].
    cbn [toP evSP]. rewrite SPf.ev_add, SPf.ev_mul, SPf.ev_pc, (ev_monoP xv vs H1).
    rewrite (IH H2). reflexivity.
Qed.

Lemma checkEq_sound p q : checkEq p q = true -> forall xv, evSP xv p = evSP xv q.
Proof.
  unfold checkEq. intros H xv. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  rewrite <- (ev_toP xv p H1), <- (ev_toP xv q H2). apply SPf.ev_peq. exact H3.
Qed.

Lemma evSP_scale xv k s : evSP xv (scaleSP k s) = D.mul (SPf.phiZ k) (evSP xv s).
Proof.
  induction s as [|[c vs] r IH]; cbn [scaleSP evSP].
  - ring.
  - rewrite IH, phiZ_mul. ring.
Qed.

(** The point map dual to Phi: variable j takes the signed value of the variable it is sent to. *)

Definition phix (xv : nat -> D.t) (j : nat) : D.t :=
  D.mul (SPf.phiZ (snd (phiv j))) (xv (fst (phiv j))).

Lemma evMono_phi xv vs :
  evMono (phix xv) vs = D.mul (SPf.phiZ (signP vs)) (evMono xv (map (fun v => fst (phiv v)) vs)).
Proof.
  induction vs as [|v r IH]; cbn [evMono signP map].
  - rewrite SPf.phiZ_one. ring.
  - rewrite IH, phiZ_mul. unfold phix. ring.
Qed.

Theorem evSP_Phi xv s : evSP xv (PhiSP s) = evSP (phix xv) s.
Proof.
  induction s as [|[c vs] r IH]; cbn [PhiSP evSP].
  - reflexivity.
  - rewrite IH, evMono_phi, phiZ_mul. ring.
Qed.

Lemma evMono_ext xv yv vs : (forall k, xv k = yv k) -> evMono xv vs = evMono yv vs.
Proof.
  intros H. induction vs as [|v r IH]; cbn [evMono]; [reflexivity|]. rewrite H, IH. reflexivity.
Qed.

Lemma evSP_ext xv yv s : (forall k, xv k = yv k) -> evSP xv s = evSP yv s.
Proof.
  intros H. induction s as [|[c vs] r IH]; cbn [evSP]; [reflexivity|].
  rewrite IH, (evMono_ext xv yv vs H). reflexivity.
Qed.

Theorem phix_square xv j :
  phix (phix xv) j = if Nat.eqb j 5 || Nat.eqb j 6 then D.opp (xv j) else xv j.
Proof.
  do 11 (destruct j as [|j]; [cbv [phix phiv fst snd Nat.eqb orb];
    rewrite ?SPf.phiZ_one, ?SPf.phiZ_mone; ring|]).
  cbv [phix phiv fst snd Nat.eqb orb]. rewrite ?SPf.phiZ_one, ?SPf.phiZ_mone. ring.
Qed.

Theorem phix_order4 xv j : phix (phix (phix (phix xv))) j = xv j.
Proof.
  do 11 (destruct j as [|j]; [cbv [phix phiv fst snd];
    rewrite ?SPf.phiZ_one, ?SPf.phiZ_mone; ring|]).
  cbv [phix phiv fst snd]. rewrite ?SPf.phiZ_one, ?SPf.phiZ_mone. ring.
Qed.

Theorem Phi_order4 xv s : evSP xv (PhiSP (PhiSP (PhiSP (PhiSP s)))) = evSP xv s.
Proof.
  rewrite !evSP_Phi. apply evSP_ext. intros k. apply phix_order4.
Qed.

Theorem Phi_square_s4 xv : evSP xv (PhiSP (PhiSP [(1%Z, [5])])) = D.opp (xv 5).
Proof.
  rewrite !evSP_Phi. cbn [evSP evMono]. rewrite (phix_square xv 5). cbn -[SPf.phiZ].
  rewrite SPf.phiZ_one. ring.
Qed.

(** The matrix identities, entrywise. *)

Theorem conj_C xv a b : (a < 15)%nat -> (b < 15)%nat ->
  evSP xv (Cp a b) = D.mul (SPf.phiZ (Z.opp (Z.mul (dsg a) (dsg b)))) (evSP (phix xv) (Cm a b)).
Proof.
  intros Ha Hb.
  pose proof (checkEq_sound _ _ (allpairs_sound Cfun CCheck_ok a b Ha Hb) xv) as H.
  rewrite H, evSP_scale, evSP_Phi. reflexivity.
Qed.

Theorem conj_F xv a b : (a < 15)%nat -> (b < 15)%nat ->
  evSP xv (Fp a b) = D.mul (SPf.phiZ (Z.mul (dsg a) (esg b))) (evSP (phix xv) (Fm a b)).
Proof.
  intros Ha Hb.
  pose proof (checkEq_sound _ _ (allpairs_sound Ffun FCheck_ok a b Ha Hb) xv) as H.
  rewrite H, evSP_scale, evSP_Phi. reflexivity.
Qed.

(** The determinant of the pivot block, over D. *)

Definition TD (C F : nat -> nat -> SPoly) (xv : nat -> D.t) (a b : nat) : D.t :=
  SPf.P.sumk 15 (fun k => SPf.P.sumk 15 (fun l =>
    D.mul (D.mul (evSP xv (F k a)) (evSP xv (C k l))) (evSP xv (F l b)))).

Fixpoint detD (M : nat -> nat -> D.t) (rows cols : list nat) : D.t :=
  match rows with
  | [] => D.one
  | r :: rs =>
      SPf.P.sumk (length cols) (fun k =>
        D.mul (D.mul (SPf.P.sgn k) (M r (nth k cols O))) (detD M rs (rem_at k cols)))
  end.

Definition detBD (C F : nat -> nat -> SPoly) (xv : nat -> D.t) : D.t :=
  detD (TD C F xv) (seq 0 6) (seq 0 6).

Lemma ev_detP env n (M : nat -> nat -> ZP) (N : nat -> nat -> D.t) :
  (forall a b, (a < n)%nat -> (b < n)%nat -> SPf.ev env (M a b) = N a b) ->
  forall rows cols, Forall (fun x => (x < n)%nat) rows -> Forall (fun x => (x < n)%nat) cols ->
  SPf.ev env (detP M rows cols) = detD N rows cols.
Proof.
  intros HM rows. induction rows as [|r rs IH]; intros cols Hr Hc; cbn [detP detD].
  - rewrite SPf.ev_pc. exact SPf.phiZ_one.
  - rewrite SPf.ev_sumP. apply SPf.P.sumk_ext. intros k Hk. try cbv beta.
    inversion Hr as [|y s Hr1 Hrs]; subst.
    rewrite SPf.ev_mul, SPf.ev_mul, SPf.ev_sgnP.
    rewrite (IH (rem_at k cols) Hrs (Forall_rem_at _ k cols Hc)).
    assert (Hin : In (nth k cols O) cols) by (apply nth_In; exact Hk).
    rewrite (HM r (nth k cols O) Hr1 (proj1 (Forall_forall _ _) Hc _ Hin)).
    reflexivity.
Qed.

Lemma ev_TP xv C F a b :
  (forall a b, (a < 15)%nat -> (b < 15)%nat -> wfb (C a b) = true /\ wfb (F a b) = true) ->
  (a < 15)%nat -> (b < 15)%nat -> SPf.ev (envf xv) (TP C F a b) = TD C F xv a b.
Proof.
  intros Hw Ha Hb. unfold TP, TD. rewrite SPf.ev_sumP. apply SPf.P.sumk_ext. intros k Hk. try cbv beta.
  rewrite SPf.ev_sumP. apply SPf.P.sumk_ext. intros l Hl. try cbv beta.
  rewrite SPf.ev_mul, SPf.ev_mul.
  rewrite (ev_toP xv (F k a) (proj2 (Hw k a Hk Ha))), (ev_toP xv (C k l) (proj1 (Hw k l Hk Hl))),
    (ev_toP xv (F l b) (proj2 (Hw l b Hl Hb))).
  reflexivity.
Qed.

Lemma ev_TP_red xv C F B E :
  (forall a b, (a < 15)%nat -> (b < 15)%nat -> wfb (C a b) = true /\ wfb (F a b) = true) ->
  Tcheck C F B E = true -> D.mul (xv 1) (xv 1) = D.opp D.one ->
  forall a b, (a < 6)%nat -> (b < 6)%nat -> SPf.ev (envf xv) (toP (B a b)) = TD C F xv a b.
Proof.
  intros Hw Hc Hi a b Ha Hb.
  pose proof (allpairsN_sound 6 _ Hc a b Ha Hb) as H. unfold Tfun in H.
  apply andb_prop in H as [Hwf Hp].
  rewrite <- (ev_TP xv C F a b Hw ltac:(lia) ltac:(lia)).
  symmetry. exact (detB_close xv _ _ _ Hi Hp).
Qed.

Lemma detBD_ev xv C F B E :
  (forall a b, (a < 15)%nat -> (b < 15)%nat -> wfb (C a b) = true /\ wfb (F a b) = true) ->
  Tcheck C F B E = true -> D.mul (xv 1) (xv 1) = D.opp D.one ->
  detBD C F xv = SPf.ev (envf xv) (detBred B).
Proof.
  intros Hw Hc Hi. unfold detBD, detBred. symmetry. apply (ev_detP (envf xv) 6).
  - intros a b Ha Hb. exact (ev_TP_red xv C F B E Hw Hc Hi a b Ha Hb).
  - apply (proj2 (Forall_forall _ _)). intros x Hx. apply in_seq in Hx. lia.
  - apply (proj2 (Forall_forall _ _)). intros x Hx. apply in_seq in Hx. lia.
Qed.

Lemma wf_m : forall a b, (a < 15)%nat -> (b < 15)%nat -> wfb (Cm a b) = true /\ wfb (Fm a b) = true.
Proof.
  intros a b Ha Hb. pose proof (allpairs_sound Wfun WfData_ok a b Ha Hb) as H. unfold Wfun in H.
  repeat rewrite andb_true_iff in H. tauto.
Qed.

Lemma wf_p : forall a b, (a < 15)%nat -> (b < 15)%nat -> wfb (Cp a b) = true /\ wfb (Fp a b) = true.
Proof.
  intros a b Ha Hb. pose proof (allpairs_sound Wfun WfData_ok a b Ha Hb) as H. unfold Wfun in H.
  repeat rewrite andb_true_iff in H. tauto.
Qed.

Definition sqm1 (s : D.t) : D.t := D.sub (D.mul s s) D.one.

Definition closedForm (xv : nat -> D.t) (t : D.t) : D.t :=
  D.mul (SPf.phiZ (-1024)%Z) (D.mul (D.mul (sqm1 (xv 3)) (sqm1 (xv 3))) (D.mul t t)).

Lemma ev_clm xv : SPf.ev (envf xv) clm = closedForm xv (D.sub (xv 3) (xv 1)).
Proof.
  unfold clm, clP, qP, sqP, s2P, iP, closedForm, sqm1. evs.
  rewrite (ev_varP xv 3) by lia. rewrite (ev_varP xv 1) by lia. rewrite SPf.phiZ_one. ring.
Qed.

Lemma ev_clp xv : SPf.ev (envf xv) clp = closedForm xv (D.add (xv 3) (xv 1)).
Proof.
  unfold clp, clP, qP, sqP, s2P, iP, closedForm, sqm1. evs.
  rewrite (ev_varP xv 3) by lia. rewrite (ev_varP xv 1) by lia. rewrite SPf.phiZ_one. ring.
Qed.

(** detB of the N- script is -1024 (s2^2 - 1)^2 (s2 - i)^2 in every ring with i^2 = -1. *)
Theorem detB_Nm xv : D.mul (xv 1) (xv 1) = D.opp D.one ->
  detBD Cm Fm xv = closedForm xv (D.sub (xv 3) (xv 1)).
Proof.
  intros Hi. rewrite (detBD_ev xv Cm Fm Bm Em wf_m Tm_ok Hi).
  rewrite (detB_close xv (detBred Bm) clm Rm Hi detm_ok). apply ev_clm.
Qed.

(** detB of the N+ script is -1024 (s2^2 - 1)^2 (s2 + i)^2 in every ring with i^2 = -1. *)
Theorem detB_Np xv : D.mul (xv 1) (xv 1) = D.opp D.one ->
  detBD Cp Fp xv = closedForm xv (D.add (xv 3) (xv 1)).
Proof.
  intros Hi. rewrite (detBD_ev xv Cp Fp Bp Ep wf_p Tp_ok Hi).
  rewrite (detB_close xv (detBred Bp) clp Rp Hi detp_ok). apply ev_clp.
Qed.

(** Phi(detB-) = detB+: detB- at the point phix xv equals detB+ at xv. *)
Theorem detB_conj xv : D.mul (xv 1) (xv 1) = D.opp D.one ->
  detBD Cp Fp xv = detBD Cm Fm (phix xv).
Proof.
  intros Hi.
  assert (Hi' : D.mul (phix xv 1) (phix xv 1) = D.opp D.one).
  { cbv [phix phiv fst snd]. rewrite SPf.phiZ_mone.
    transitivity (D.mul (xv 1) (xv 1)); [ring|exact Hi]. }
  rewrite (detB_Np xv Hi), (detB_Nm (phix xv) Hi').
  unfold closedForm, sqm1. cbv [phix phiv fst snd]. rewrite ?SPf.phiZ_one, ?SPf.phiZ_mone. ring.
Qed.

End ConjugationMap.

Module GaussianConjugation := ConjugationMap GaussianIntegers.

Theorem detB_conj_gaussian (xv : nat -> GaussianIntegers.t) :
  GaussianIntegers.mul (xv 1) (xv 1) = GaussianIntegers.opp GaussianIntegers.one ->
  GaussianConjugation.detBD Cp Fp xv = GaussianConjugation.detBD Cm Fm (GaussianConjugation.phix xv).
Proof. exact (GaussianConjugation.detB_conj xv). Qed.
"""

if __name__ == "__main__":
    raise SystemExit(main())
