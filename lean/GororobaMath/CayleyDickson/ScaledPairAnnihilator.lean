/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.HalfFold

/-!
# The annihilator of a scaled pair

Convention: the product of `Tower R k` is the Cayley-Dickson product of
`GororobaMath.CayleyDickson.Tower`, `(a, b) (c, d) = (a c - star d b, d a + b star c)`, and
`Tower.mk` builds a pair. Biss, Dugger and Isaksen, Large annihilators in Cayley-Dickson
algebras (arXiv:math/0511691, 2005), write the same product and the same conjugation
`(a, b)* = (a*, -b)`; their `Ann x` is the kernel of left multiplication by `x`, the library's
`Tower.mulLeft`, and their `A_n` is `Tower ℝ n`. An element is imaginary when its coordinate
of `1` (`Tower.re`) vanishes, equivalently when `star x = -x`. The paper's complex line
`C_n` of `A_n` is the span of `1` and `i_n = (0, 1)`; a vector is orthogonal to it when both
halves are imaginary. The order hypotheses are those of
`GororobaMath.CayleyDickson.AnnihilatorSymmetry`: a commutative ring whose star is the
identity, with a partial order compatible with addition, no zero divisors and nonnegative squares
`hsq`.

## Main results

* `Tower.re_half_snd_eq_zero_of_mk_mul_eq_zero`: when `(a, b) (c, d) = 0`, `a` is imaginary and
  `(c, d)` is nonzero, the second half `b` is imaginary.
* `Tower.re_halves_eq_zero_of_mk_mul_eq_zero`: Lemma 9.5 of the paper: both halves of each
  factor of a vanishing product of nonzero elements are imaginary, so a zero divisor and its
  annihilator are orthogonal to the complex line.
* `Tower.mk_smul_mul_eq_zero_iff`: Theorem 10.1 of the paper with scalars `α, β` of the base
  field: when `α ^ 2 + β ^ 2 ≠ 0`, `(α a, β a) (x, y) = 0` exactly when `a x = 0` and
  `a y = 0`, for every `a`.
* `Tower.finrank_ker_mulLeft_mk_smul`: the kernel of left multiplication by `(α a, β a)` has
  twice the dimension of the kernel of left multiplication by `a`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

open Module

section Ordered

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] [PartialOrder R]
  [IsOrderedAddMonoid R] [NoZeroDivisors R]

/-- If `(a, b) (c, d) = 0` with `a` imaginary and `(c, d)` nonzero, then `b` is imaginary: the
pair `(-star d, c)` annihilates `(b, a)`, since the second half of that product is the star of
the second half of `(a, b) (c, d)`, and a vanishing product of nonzero elements has imaginary
factors. -/
theorem re_snd_eq_zero_of_mk_mul_eq_zero (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ} {a b c d : Tower R k}
    (h : mk a b * mk c d = 0) (hra : re k a = 0) (hw : mk c d ≠ 0) : re k b = 0 := by
  by_cases hb : b = 0
  · rw [hb]
    exact (dot_one_right k 0).symm.trans (dot_zero_left k 1)
  have hpa : star a = -a := star_eq_neg_of_re_eq_zero hra
  rw [mk_mul_mk, zero_eq_mk, mk_inj] at h
  obtain ⟨h1, h2⟩ := h
  have hswap : mk (-star d) c * mk b a = 0 := by
    have e2 : star (d * a + b * star c) = 0 := by rw [h2, star_zero]
    rw [star_add, star_mul, star_mul, star_star, hpa] at e2
    rw [mk_mul_mk, zero_eq_mk, mk_inj]
    refine ⟨?_, ?_⟩
    · rw [hpa, neg_mul, neg_mul, sub_neg_eq_add, neg_add_eq_sub]
      exact h1
    · rw [mul_neg, ← neg_mul]
      exact e2
  have hn1 : mk (-star d) c ≠ 0 := by
    intro h0
    rw [zero_eq_mk, mk_inj, neg_eq_zero, star_eq_zero] at h0
    apply hw
    rw [h0.2, h0.1, ← zero_eq_mk]
  have hn2 : mk b a ≠ 0 := by
    intro h0
    rw [zero_eq_mk, mk_inj] at h0
    exact hb h0.1
  exact (re_eq_zero_of_mul_eq_zero hsq hswap hn1 hn2).2

/-- Lemma 9.5 of Biss, Dugger and Isaksen: when a product of two nonzero elements vanishes, both
halves of each factor are imaginary, so each factor is orthogonal to the complex line spanned by
`1` and `(0, 1)`. -/
theorem re_halves_eq_zero_of_mk_mul_eq_zero (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ}
    {a b c d : Tower R k} (h : mk a b * mk c d = 0) (hu : mk a b ≠ 0) (hw : mk c d ≠ 0) :
    re k a = 0 ∧ re k b = 0 ∧ re k c = 0 ∧ re k d = 0 := by
  obtain ⟨ra, rc⟩ := re_eq_zero_of_mul_eq_zero hsq h hu hw
  exact ⟨ra, re_snd_eq_zero_of_mk_mul_eq_zero hsq h ra hw, rc,
    re_snd_eq_zero_of_mk_mul_eq_zero hsq (mul_eq_zero_rev hsq h) rc hu⟩

end Ordered

section Field

variable {K : Type u} [Field K] [StarRing K] [TrivialStar K] [PartialOrder K]
  [IsOrderedAddMonoid K]

/-- Theorem 10.1 of Biss, Dugger and Isaksen with scalars of the base field: when
`α ^ 2 + β ^ 2 ≠ 0`, the pair `(α a, β a)` annihilates `(x, y)` exactly when `a` annihilates
both `x` and `y`. A vanishing product has imaginary factors (Lemma 9.5), which turns the two
halves of the product into the system `α (a x) + β (y a) = 0`, `α (y a) - β (a x) = 0` of
determinant `α ^ 2 + β ^ 2`; the kernel swap `y a = 0 ↔ a y = 0` finishes. -/
theorem mk_smul_mul_eq_zero_iff (hsq : ∀ x : K, 0 ≤ x * x) {k : ℕ} (a x y : Tower K k) {α β : K}
    (hs : α ^ 2 + β ^ 2 ≠ 0) :
    mk (α • a) (β • a) * mk x y = 0 ↔ a * x = 0 ∧ a * y = 0 := by
  constructor
  · intro h
    by_cases hw : mk x y = 0
    · rw [zero_eq_mk, mk_inj] at hw
      rw [hw.1, hw.2]
      exact ⟨mul_zero a, mul_zero a⟩
    by_cases ha : a = 0
    · rw [ha]
      exact ⟨zero_mul x, zero_mul y⟩
    have hz : mk (α • a) (β • a) ≠ 0 := by
      intro h0
      rw [zero_eq_mk, mk_inj] at h0
      by_cases hα : α = 0
      · have hβ : β ≠ 0 := by
          intro hβ
          apply hs
          rw [hα, hβ]
          norm_num
        exact ha (eq_zero_of_smul_eq_zero hβ h0.2)
      · exact ha (eq_zero_of_smul_eq_zero hα h0.1)
    obtain ⟨-, -, rx, ry⟩ := re_halves_eq_zero_of_mk_mul_eq_zero hsq h hz hw
    have sx : star x = -x := star_eq_neg_of_re_eq_zero rx
    have sy : star y = -y := star_eq_neg_of_re_eq_zero ry
    rw [mk_mul_mk, zero_eq_mk, mk_inj] at h
    obtain ⟨h1, h2⟩ := h
    have e1 : α • (a * x) + β • (y * a) = 0 := by
      rw [smul_mul_assoc', mul_smul_comm', sy, neg_mul, smul_neg, sub_neg_eq_add] at h1
      exact h1
    have e2 : α • (y * a) - β • (a * x) = 0 := by
      rw [mul_smul_comm', smul_mul_assoc', sx, mul_neg, smul_neg, ← sub_eq_add_neg] at h2
      exact h2
    have hP : (α ^ 2 + β ^ 2) • (a * x) = 0 := by
      have : (α ^ 2 + β ^ 2) • (a * x) =
          α • (α • (a * x) + β • (y * a)) - β • (α • (y * a) - β • (a * x)) := by module
      rw [this, e1, e2, smul_zero, smul_zero, sub_zero]
    have hQ : (α ^ 2 + β ^ 2) • (y * a) = 0 := by
      have : (α ^ 2 + β ^ 2) • (y * a) =
          β • (α • (a * x) + β • (y * a)) + α • (α • (y * a) - β • (a * x)) := by module
      rw [this, e1, e2, smul_zero, smul_zero, add_zero]
    exact ⟨eq_zero_of_smul_eq_zero hs hP,
      (mul_eq_zero_iff_rev hsq y a).1 (eq_zero_of_smul_eq_zero hs hQ)⟩
  · rintro ⟨hx, hy⟩
    have hy' : y * a = 0 := (mul_eq_zero_iff_rev hsq a y).1 hy
    have hsy : star y * a = 0 := (mul_eq_zero_iff_star_mul_eq_zero hsq y a).1.1 hy'
    have hsx : a * star x = 0 := (mul_eq_zero_iff_star_mul_eq_zero hsq a x).2.1 hx
    rw [mk_mul_mk, zero_eq_mk, mk_inj]
    refine ⟨?_, ?_⟩
    · rw [smul_mul_assoc', mul_smul_comm', hx, hsy, smul_zero, smul_zero, sub_zero]
    · rw [mul_smul_comm', smul_mul_assoc', hy', hsx, smul_zero, smul_zero, add_zero]

/-- The kernel of left multiplication by `(α a, β a)` at level `k + 1` has twice the
dimension of the kernel of left multiplication by `a` at level `k`, when
`α ^ 2 + β ^ 2 ≠ 0`. -/
theorem finrank_ker_mulLeft_mk_smul (hsq : ∀ x : K, 0 ≤ x * x) {k : ℕ} (a : Tower K k) {α β : K}
    (hs : α ^ 2 + β ^ 2 ≠ 0) :
    finrank K (LinearMap.ker (mulLeft K (k + 1) (mk (α • a) (β • a)))) =
      2 * finrank K (LinearMap.ker (mulLeft K k a)) :=
  finrank_ker_mulLeft_eq_two_mul _ a (LinearEquiv.refl K _) fun c d =>
    mk_smul_mul_eq_zero_iff hsq a c d hs

end Field

end Tower

end CayleyDickson
