/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Associator
public import GororobaMath.CayleyDickson.AnnihilatorSymmetry
public import GororobaMath.CayleyDickson.Kaplansky

/-!
# Square-zero elements and idempotents over a domain

Convention: `Tower F k` is the `k`-fold Cayley-Dickson double of a commutative ring `F`
without zero divisors and with the identity as star, `Tower.re` is the coordinate of `1` and
`Tower.dot` the trace form, so `dot k x x` is the norm `N(x)`. The results read at every level;
`mul_self_eq_zero_iff` also assumes `2 ≠ 0`, so it covers the finite fields `F_p` with `p` odd
and every field of characteristic other than `2`.

The quadratic relation `x * x = (2 re x) • x - N(x) • 1` (`Tower.mul_self_eq_smul_sub`) decides
both questions. Applying `dot · 1` to it gives the scalar equation `re (x * x) = 2 re(x)² - N(x)`.
When the coefficient of `x` left in the relation is nonzero, it cancels, since `F` has no zero
divisors, and `x` is a multiple of `1`; a multiple `a • 1` squares to `a² • 1`. Otherwise the
relation is a scalar equation. Zero divisors break the first result: over `ℚ[ε]/(ε²)`, where `2` is
a unit, the element `ε • 1` squares to zero with `re = ε ≠ 0`.

## Main results

* `Tower.mul_self_eq_zero_iff`: `x * x = 0` exactly when `re x = 0` and `N(x) = 0`.
* `Tower.mul_self_eq_zero_of_mul_self_mul_mul_self_eq_zero`: `(x * x) * (x * x) = 0` only when
  `x * x = 0`.
* `Tower.iterate_mul_self_eq_zero_iff`: for `m ≥ 1` the `m`-fold iterated square of `x` is
  zero exactly when `x * x = 0`, with no hypothesis on `2`.
* `Tower.mul_self_eq_self_iff`: `x * x = x` exactly when `x = 0`, `x = 1`, or `2 re x = 1` and
  `N(x) = 0`.
* `Tower.mul_self_eq_self_iff_of_two_eq_zero`: when `2 = 0` the only idempotents are `0` and
  `1`.

These are the statements of gororoba-quantum's findings row A5-661 over every such ring;
its enumerated counts over `F_p` are not stated here.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {F : Type u} [CommRing F] [NoZeroDivisors F] [StarRing F] [TrivialStar F] {k : ℕ}

omit [NoZeroDivisors F] in
/-- The coordinate of `1` in `x * x`: `re (x * x) = 2 re(x)² - N(x)`. -/
theorem re_mul_self (x : Tower F k) : re k (x * x) = 2 * re k x * re k x - dot k x x := by
  rw [← dot_one_right k (x * x), mul_self_eq_smul_sub x, dot_sub_left, dot_smul_left,
    dot_smul_left, dot_one_right, dot_one_right, re_one, mul_one]

omit [NoZeroDivisors F] [TrivialStar F] in
/-- The norm of `α • x - β • 1`: `α² N(x) - 2 α β re x + β²`. -/
theorem dot_smul_sub_smul_one_self (α β : F) (x : Tower F k) :
    dot k (α • x - β • (1 : Tower F k)) (α • x - β • (1 : Tower F k)) =
      α * α * dot k x x - 2 * α * β * re k x + β * β := by
  simp only [dot_sub_left, dot_sub_right, dot_smul_left, dot_smul_right]
  simp only [dot_one_right, dot_comm k 1 x, re_one]
  ring

omit [TrivialStar F] in
/-- An element with `(2 re x - c) • x` a multiple of `1` and `2 re x ≠ c` is `re x • 1`. -/
theorem eq_re_smul_one_of_smul_eq {c d : F} {x : Tower F k} (hc : 2 * re k x - c ≠ 0)
    (h : (2 * re k x - c) • x = d • (1 : Tower F k)) : x = re k x • (1 : Tower F k) := by
  have hd : d = (2 * re k x - c) * re k x := by
    have h1 := congrArg (re k) h
    rw [re_smul, re_smul, re_one, mul_one] at h1
    exact h1.symm
  have h0 : (2 * re k x - c) • (x - re k x • (1 : Tower F k)) = 0 := by
    rw [smul_sub, h, smul_smul, ← hd, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_smul_eq_zero hc h0)

omit [NoZeroDivisors F] in
/-- A multiple of `1` squares to the square of the scalar. -/
theorem smul_one_mul_smul_one (a : F) :
    a • (1 : Tower F k) * a • (1 : Tower F k) = (a * a) • (1 : Tower F k) := by
  rw [smul_mul_assoc', mul_smul_comm', one_mul, smul_smul]

/-- Over a domain with `2 ≠ 0`, `x * x = 0` exactly when `re x = 0` and `N(x) = 0`. -/
theorem mul_self_eq_zero_iff (h2 : (2 : F) ≠ 0) (x : Tower F k) :
    x * x = 0 ↔ re k x = 0 ∧ dot k x x = 0 := by
  refine ⟨fun h => ?_, fun ⟨h1, h2'⟩ => ?_⟩
  · have hre := re_mul_self x
    rw [h, re_zero] at hre
    have ha : re k x = 0 := by
      by_contra ha
      have hlin : (2 * re k x - 0) • x = dot k x x • (1 : Tower F k) := by
        have hq := mul_self_eq_smul_sub x
        rw [h, eq_comm, sub_eq_zero] at hq
        rw [sub_zero, hq]
      have hx := eq_re_smul_one_of_smul_eq (by rw [sub_zero]; exact mul_ne_zero h2 ha) hlin
      have hsq : x * x = (re k x * re k x) • (1 : Tower F k) := by
        conv_lhs => rw [hx]
        exact smul_one_mul_smul_one _
      have h3 := congrArg (re k) (hsq.symm.trans h)
      rw [re_smul, re_one, mul_one, re_zero] at h3
      exact ha (mul_self_eq_zero.mp h3)
    refine ⟨ha, ?_⟩
    rw [ha] at hre
    linear_combination hre
  · rw [mul_self_eq_smul_sub, h1, h2', mul_zero, zero_smul, zero_smul, sub_zero]

/-- Over a domain, `(x * x) * (x * x) = 0` only when `x * x = 0`. When `2 ≠ 0` the square
`y = x * x` has `re y = 2 re(x)² - N(x)` and `N(y) = N(x)²`; when `2 = 0` the square is
`-N(x) • 1`, whose square `N(x)² • 1` vanishes only at `N(x) = 0`. -/
theorem mul_self_eq_zero_of_mul_self_mul_mul_self_eq_zero {x : Tower F k}
    (h : x * x * (x * x) = 0) : x * x = 0 := by
  by_cases h2 : (2 : F) = 0
  · have hsq : x * x = (-dot k x x) • (1 : Tower F k) := by
      rw [mul_self_eq_smul_sub x, h2, zero_mul, zero_smul, zero_sub, neg_smul]
    have h4 : x * x * (x * x) = ((-dot k x x) * (-dot k x x)) • (1 : Tower F k) := by
      conv_lhs => rw [hsq]
      exact smul_one_mul_smul_one _
    have hre := congrArg (re k) (h4.symm.trans h)
    rw [re_smul, re_one, mul_one, re_zero] at hre
    rw [hsq, mul_self_eq_zero.mp hre, zero_smul]
  obtain ⟨hre, hdot⟩ := (mul_self_eq_zero_iff h2 (x * x)).mp h
  have hd : dot k (x * x) (x * x) = dot k x x * dot k x x := by
    rw [mul_self_eq_smul_sub x, dot_smul_sub_smul_one_self]
    ring
  rw [hd] at hdot
  have hd0 : dot k x x = 0 := mul_self_eq_zero.mp hdot
  rw [re_mul_self, hd0, sub_zero] at hre
  have ha : re k x = 0 := by
    rcases mul_eq_zero.mp hre with h' | h'
    · exact (mul_eq_zero.mp h').resolve_left h2
    · exact h'
  exact (mul_self_eq_zero_iff h2 x).mpr ⟨ha, hd0⟩

/-- Over a domain, the `m`-fold iterated square of `x`, for any `m ≥ 1`, is zero exactly when
`x * x = 0`. A square-zero element has every later square zero; conversely the iterated square of
`x` at `m + 1` is the iterated square of `x * x` at `m`, so induction on `m` reduces to
`mul_self_eq_zero_of_mul_self_mul_mul_self_eq_zero`. In the tower the iterated square is the
power `x^(2^m)`: each square stays in the span of `1` and `x` (`mul_self_eq_smul_sub`), on which
the associator vanishes (`associator_span_one_self`). -/
theorem iterate_mul_self_eq_zero_iff {m : ℕ} (hm : 1 ≤ m) (x : Tower F k) :
    (fun y : Tower F k => y * y)^[m] x = 0 ↔ x * x = 0 := by
  induction m, hm using Nat.le_induction generalizing x with
  | base => exact Iff.rfl
  | succ m _ ih =>
    rw [Function.iterate_succ_apply, ih]
    show x * x * (x * x) = 0 ↔ x * x = 0
    exact ⟨mul_self_eq_zero_of_mul_self_mul_mul_self_eq_zero, fun h => by rw [h, mul_zero]⟩

/-- Over a domain, `x * x = x` exactly when `x` is `0` or `1`, or `2 re x = 1` and
`N(x) = 0`; so the idempotents other than `0` and `1` have real part `1/2` and norm `0` when
`2 ≠ 0`. -/
theorem mul_self_eq_self_iff (x : Tower F k) :
    x * x = x ↔ x = 0 ∨ x = 1 ∨ (2 * re k x = 1 ∧ dot k x x = 0) := by
  refine ⟨fun h => ?_, ?_⟩
  · have hlin : (2 * re k x - 1) • x = dot k x x • (1 : Tower F k) := by
      have hq := mul_self_eq_smul_sub x
      rw [h, eq_sub_iff_add_eq] at hq
      rw [sub_smul, one_smul, ← hq]
      abel
    by_cases hc : 2 * re k x - 1 = 0
    · rw [hc, zero_smul] at hlin
      have hd := congrArg (re k) hlin
      rw [re_zero, re_smul, re_one, mul_one] at hd
      exact Or.inr (Or.inr ⟨by linear_combination hc, hd.symm⟩)
    · have hx := eq_re_smul_one_of_smul_eq hc hlin
      have hsq : x * x = (re k x * re k x) • (1 : Tower F k) := by
        conv_lhs => rw [hx]
        exact smul_one_mul_smul_one _
      have h3 := congrArg (re k) (hsq.symm.trans h)
      rw [re_smul, re_one, mul_one] at h3
      have h4 : re k x * (re k x - 1) = 0 := by linear_combination h3
      rcases mul_eq_zero.mp h4 with h0 | h0
      · left
        rw [hx, h0, zero_smul]
      · right; left
        rw [hx, sub_eq_zero.mp h0, one_smul]
  · rintro (h | h | ⟨ha, hd⟩)
    · rw [h, mul_zero]
    · rw [h, mul_one]
    · rw [mul_self_eq_smul_sub, ha, hd, one_smul, zero_smul, sub_zero]

/-- Over a domain in which `2 = 0`, the only idempotents are `0` and `1`: the third case of
`mul_self_eq_self_iff` needs `2 re x = 1`, which reads `0 = 1` and makes `x = 1 • x` zero. -/
theorem mul_self_eq_self_iff_of_two_eq_zero (h2 : (2 : F) = 0) (x : Tower F k) :
    x * x = x ↔ x = 0 ∨ x = 1 := by
  rw [mul_self_eq_self_iff]
  refine ⟨fun h => ?_, fun h => h.elim Or.inl (Or.inr ∘ Or.inl)⟩
  rcases h with h | h | ⟨ha, _⟩
  · exact Or.inl h
  · exact Or.inr h
  · left
    rw [h2, zero_mul] at ha
    rw [← one_smul F x, ← ha, zero_smul]

end Tower

end CayleyDickson
