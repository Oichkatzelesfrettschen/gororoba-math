/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AnnihilatorSymmetry

/-!
# The conjugate identities of the trace form

Convention: the product of `Tower R k` is the Cayley-Dickson product of
`GororobaMath.CayleyDickson.Tower`, `(a, b) (c, d) = (a c - star d b, d a + b star c)`,
with `star (a, b) = (star a, -b)`, over a commutative ring whose star is the
identity. `Tower.dot k` is the trace form and `Tower.re k` the coordinate of
`1` of `GororobaMath.CayleyDickson.AnnihilatorSymmetry`; an element `a` is
pure when `star a = -a`.

Every element satisfies `star x = (2 * re k x) • 1 - x` (`Tower.star_add_self`),
and scalars pass through the product on both sides. So `x * (star x * y)` and
`star x * (x * y)` both equal `(2 * re k x) • (x * y) - x * (x * y)`, and the
mirror identity holds the same way; no step uses associativity, alternativity or an
order. Over an ordered domain the trace form is definite, and with the adjoint
identities this makes `x * y = 0`, `star x * y = 0` and `x * star y = 0`
equivalent.

## Main results

* `Tower.mul_star_mul_left`: `x * (star x * y) = star x * (x * y)`, the Rocq
  `conj_mul_left` of the functor `CdTower` in `rocq/quantum/CdTowerDomain.v`.
* `Tower.mul_mul_star_right`: `x * y * star y = x * star y * y`, the Rocq
  `conj_mul_right` of the same functor.
* `Tower.mul_eq_zero_iff_star_mul_eq_zero`: Lemma 9.2 of Biss, Dugger and
  Isaksen (arXiv:math/0511691), the Rocq `lemma_9_2` of the same functor.
* `Tower.dot_mul_left_of_star_eq_neg`: left multiplication by a pure element is
  skew for the trace form, `dot (a * y) z = -dot y (a * z)` (Moreno 1997,
  Proposition 1.7), the Rocq `l_x_skew_symm` of
  `rocq/open/theories/C1539_MorSkewSymm.v`, stated there over the interface
  `CDAlgMoreno` with real coefficients and here over the tower at every level;
  `Tower.dot_mul_right_of_star_eq_neg` is its mirror, `r_x_skew_symm`.

The Rocq functor `CdTower` takes an ordered domain; the first two identities
hold here over every commutative ring with the identity as star, and Lemma 9.2
under the ordered hypotheses of `GororobaMath.CayleyDickson.AnnihilatorSymmetry`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

/-- Conjugation is `x ↦ (2 * re k x) • 1 - x`. -/
theorem star_eq_smul_one_sub {k : ℕ} (x : Tower R k) :
    star x = (2 * re k x) • (1 : Tower R k) - x :=
  eq_sub_of_add_eq (star_add_self k x)

/-- The identity of Lemma 9.2 of Biss, Dugger and Isaksen,
`x * (star x * y) = star x * (x * y)`. The Rocq original is `conj_mul_left` of
the functor `CdTower` in `rocq/quantum/CdTowerDomain.v`. -/
theorem mul_star_mul_left {k : ℕ} (x y : Tower R k) :
    x * (star x * y) = star x * (x * y) := by
  rw [star_eq_smul_one_sub, sub_mul, sub_mul, smul_mul_assoc', smul_mul_assoc', one_mul, one_mul,
    mul_sub, mul_smul_comm']

/-- The mirror identity `x * y * star y = x * star y * y`. The Rocq original is
`conj_mul_right` of the functor `CdTower` in `rocq/quantum/CdTowerDomain.v`. -/
theorem mul_mul_star_right {k : ℕ} (x y : Tower R k) :
    x * y * star y = x * star y * y := by
  rw [star_eq_smul_one_sub, mul_sub, mul_sub, mul_smul_comm', mul_smul_comm', mul_one, mul_one,
    sub_mul, smul_mul_assoc']

/-- Left multiplication by a pure element is skew for the trace form (Moreno 1997,
Proposition 1.7). The Rocq original is `l_x_skew_symm` of
`rocq/open/theories/C1539_MorSkewSymm.v`. -/
theorem dot_mul_left_of_star_eq_neg {k : ℕ} {a : Tower R k} (ha : star a = -a)
    (y z : Tower R k) : dot k (a * y) z = -dot k y (a * z) := by
  rw [(dot_mul_adjoint k a y z).1, ha, neg_mul, dot_neg_right]

/-- Right multiplication by a pure element is skew for the trace form. The Rocq
original is `r_x_skew_symm` of `rocq/open/theories/C1539_MorSkewSymm.v`. -/
theorem dot_mul_right_of_star_eq_neg {k : ℕ} {a : Tower R k} (ha : star a = -a)
    (y z : Tower R k) : dot k (y * a) z = -dot k y (z * a) := by
  rw [(dot_mul_adjoint k y a z).2, ha, mul_neg, dot_neg_right]

section Ordered

variable [PartialOrder R] [IsOrderedAddMonoid R] [NoZeroDivisors R]

theorem star_mul_eq_zero_of_mul_eq_zero (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ} {x y : Tower R k}
    (h : x * y = 0) : star x * y = 0 := by
  apply eq_zero_of_dot_self_eq_zero hsq
  rw [(dot_mul_adjoint k (star x) y _).1, star_star, mul_star_mul_left, h, mul_zero,
    dot_zero_right]

theorem mul_star_eq_zero_of_mul_eq_zero (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ} {x y : Tower R k}
    (h : x * y = 0) : x * star y = 0 := by
  apply eq_zero_of_dot_self_eq_zero hsq
  rw [(dot_mul_adjoint k x (star y) _).2, star_star, ← mul_mul_star_right, h, zero_mul,
    dot_zero_right]

/-- Lemma 9.2 of Biss, Dugger and Isaksen: `x * y = 0`, `star x * y = 0` and
`x * star y = 0` are equivalent, at every level, over a commutative ring with the
identity as star, no zero divisors, a partial order compatible with addition and
nonnegative squares. The Rocq original is `lemma_9_2` of the functor `CdTower` in
`rocq/quantum/CdTowerDomain.v`. -/
theorem mul_eq_zero_iff_star_mul_eq_zero (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ} (x y : Tower R k) :
    (x * y = 0 ↔ star x * y = 0) ∧ (x * y = 0 ↔ x * star y = 0) := by
  refine ⟨⟨star_mul_eq_zero_of_mul_eq_zero hsq, fun h => ?_⟩,
    ⟨mul_star_eq_zero_of_mul_eq_zero hsq, fun h => ?_⟩⟩
  · simpa only [star_star] using star_mul_eq_zero_of_mul_eq_zero hsq h
  · simpa only [star_star] using mul_star_eq_zero_of_mul_eq_zero hsq h

end Ordered

/-- The ordered hypotheses hold over the rationals, at level 5. -/
example (x y : Tower ℚ 5) (h : x * y = 0) : star x * y = 0 :=
  ((mul_eq_zero_iff_star_mul_eq_zero (fun r => mul_self_nonneg r) x y).1).1 h

end Tower

end CayleyDickson
