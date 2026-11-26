/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Nat.Factors
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# Sparse integer polynomials with prime-coded monomials, for kernel certificates

Convention: a polynomial is a list of terms `(code, coeff)`; a monomial is coded by a natural
number `n` standing for the positive number `n + 1`, whose prime factors with multiplicity are
the variables of the monomial. A variable is a prime `p`, with code `p - 1`, and the product of
two monomials is the product of their numbers, `mulCode a b = (a + 1) * (b + 1) - 1`, which the
kernel computes on big naturals. The evaluation at `env : ℕ → R` of a term `(n, c)` is
`c` times the product of `env p` over the prime factors `p` of `n + 1`; `evP env p` sums the
terms. No operation relies on a sorted list: the evaluation lemmas hold for every list, and
sortedness only makes the zero test of a difference complete.

## Main results

* `SparsePoly.evP_padd`, `SparsePoly.evP_pneg`, `SparsePoly.evP_pmul`: evaluation is additive,
  odd and multiplicative, for every list and every commutative ring.
* `SparsePoly.evP_varP`: the polynomial of a prime variable evaluates to the value of `env` there.
-/

@[expose] public section

namespace SparsePoly

/-- A term is a monomial code and an integer coefficient. -/
abbrev Poly : Type := List (ℕ × ℤ)

/-- The code of the product of two monomials. -/
def mulCode (a b : ℕ) : ℕ := (a + 1) * (b + 1) - 1

/-- The value of a monomial code at `env`: the product of `env p` over the prime factors of
`n + 1`. -/
def monEv {R : Type*} [CommRing R] (env : ℕ → R) (n : ℕ) : R :=
  (((n + 1).primeFactorsList).map env).prod

/-- Evaluation of a polynomial at `env`. -/
def evP {R : Type*} [CommRing R] (env : ℕ → R) (p : Poly) : R :=
  (p.map fun t => (t.2 : R) * monEv env t.1).sum

variable {R : Type*} [CommRing R] (env : ℕ → R)

theorem mulCode_succ (a b : ℕ) : mulCode a b + 1 = (a + 1) * (b + 1) := by
  unfold mulCode
  have : 0 < (a + 1) * (b + 1) := Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos b)
  omega

/-- The value of a product code is the product of the values. -/
theorem monEv_mulCode (a b : ℕ) : monEv env (mulCode a b) = monEv env a * monEv env b := by
  unfold monEv
  rw [mulCode_succ]
  have h := (Nat.perm_primeFactorsList_mul (Nat.succ_ne_zero a) (Nat.succ_ne_zero b)).map env
  rw [h.prod_eq, List.map_append, List.prod_append]

/-- The code of the variable `p`. -/
def varCode (p : ℕ) : ℕ := p - 1

/-- A prime variable evaluates to the value of `env` at it. -/
theorem monEv_varCode {p : ℕ} (hp : p.Prime) : monEv env (varCode p) = env p := by
  unfold monEv varCode
  rw [Nat.sub_add_cancel hp.one_le, Nat.primeFactorsList_prime hp]
  simp

/-- The polynomial of the variable `p`. -/
def varP (p : ℕ) : Poly := [(varCode p, 1)]

theorem evP_varP {p : ℕ} (hp : p.Prime) : evP env (varP p) = env p := by
  simp [evP, varP, monEv_varCode env hp]

/-- The constant polynomial `c`. -/
def constP (c : ℤ) : Poly := if c = 0 then [] else [(0, c)]

theorem evP_constP (c : ℤ) : evP env (constP c) = c := by
  unfold constP
  split_ifs with h
  · simp [evP, h]
  · simp [evP, monEv]

@[simp] theorem evP_nil : evP env [] = 0 := by simp [evP]

@[simp] theorem evP_cons (t : ℕ × ℤ) (p : Poly) :
    evP env (t :: p) = (t.2 : R) * monEv env t.1 + evP env p := by simp [evP]

theorem evP_append (p q : Poly) : evP env (p ++ q) = evP env p + evP env q := by
  simp [evP, List.sum_append]

/-- The merge of two term lists by code, with a fuel that bounds the recursion; at fuel zero the
lists are appended, so the evaluation lemma holds at every fuel. -/
def mergeF : ℕ → Poly → Poly → Poly
  | 0, p, q => p ++ q
  | _ + 1, [], q => q
  | _ + 1, a :: p, [] => a :: p
  | n + 1, (a, x) :: p, (b, y) :: q =>
      if a < b then (a, x) :: mergeF n p ((b, y) :: q)
      else if b < a then (b, y) :: mergeF n ((a, x) :: p) q
      else if x + y = 0 then mergeF n p q else (a, x + y) :: mergeF n p q

theorem evP_mergeF : ∀ (n : ℕ) (p q : Poly), evP env (mergeF n p q) = evP env p + evP env q := by
  intro n
  induction n with
  | zero => intro p q; simp [mergeF, evP_append]
  | succ n ih =>
    intro p q
    cases p with
    | nil => simp [mergeF]
    | cons t p =>
      cases q with
      | nil => simp [mergeF]
      | cons u q =>
        obtain ⟨a, x⟩ := t
        obtain ⟨b, y⟩ := u
        simp only [mergeF]
        split_ifs with h1 h2 h3
        · rw [evP_cons, ih, evP_cons, evP_cons]; ring
        · rw [evP_cons, ih, evP_cons, evP_cons]; ring
        · have hab : a = b := by omega
          subst hab
          rw [ih, evP_cons, evP_cons]
          have : ((x + y : ℤ) : R) = 0 := by rw [h3]; simp
          push_cast at this
          linear_combination (-monEv env a) * this
        · have hab : a = b := by omega
          subst hab
          rw [evP_cons, ih, evP_cons, evP_cons]
          push_cast
          ring

/-- The sum of two polynomials. -/
def padd (p q : Poly) : Poly := mergeF (p.length + q.length) p q

theorem evP_padd (p q : Poly) : evP env (padd p q) = evP env p + evP env q := evP_mergeF env _ p q

/-- The negation of a polynomial. -/
def pneg (p : Poly) : Poly := p.map fun t => (t.1, -t.2)

theorem evP_pneg (p : Poly) : evP env (pneg p) = -evP env p := by
  induction p with
  | nil => simp [pneg]
  | cons t p ih =>
    simp only [pneg, List.map_cons, evP_cons] at ih ⊢
    rw [ih]; push_cast; ring

/-- The product of a term and a polynomial. -/
def pmulTerm (t : ℕ × ℤ) (q : Poly) : Poly := q.map fun s => (mulCode t.1 s.1, t.2 * s.2)

theorem evP_pmulTerm (t : ℕ × ℤ) (q : Poly) :
    evP env (pmulTerm t q) = (t.2 : R) * monEv env t.1 * evP env q := by
  induction q with
  | nil => simp [pmulTerm]
  | cons s q ih =>
    simp only [pmulTerm, List.map_cons, evP_cons] at ih ⊢
    rw [ih, monEv_mulCode]; push_cast; ring

/-- The product of two polynomials. -/
def pmul (p q : Poly) : Poly := p.foldr (fun t acc => padd (pmulTerm t q) acc) []

theorem evP_pmul (p q : Poly) : evP env (pmul p q) = evP env p * evP env q := by
  induction p with
  | nil => simp [pmul]
  | cons t p ih =>
    simp only [pmul, List.foldr_cons] at ih ⊢
    rw [evP_padd, evP_pmulTerm, ih, evP_cons]; ring

/-- The sum of a list of polynomials. -/
def psum (l : List Poly) : Poly := l.foldr padd []

theorem evP_psum (l : List Poly) : evP env (psum l) = (l.map (evP env)).sum := by
  induction l with
  | nil => simp [psum]
  | cons p l ih =>
    simp only [psum, List.foldr_cons] at ih ⊢
    rw [evP_padd, ih, List.map_cons, List.sum_cons]

end SparsePoly
