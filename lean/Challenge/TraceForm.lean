/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AnnihilatorSymmetry

/-!
# Challenge: conjugate identities of the trace form

This file restates, with `sorry` as each proof, the headline theorems that the solution
module proves and that the "Lean library" table of `README.md` names, with the
definitions those statements use. It imports the library modules that the solution
module imports. `lake comparator --config` with the JSON file beside this one checks
that each named theorem of the solution module has the statement written here and
depends only on `propext`, `Classical.choice` and `Quot.sound`. No library module
imports this file, and the admission gate does not build it.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

/-- The identity of Lemma 9.2 of Biss, Dugger and Isaksen,
`x * (star x * y) = star x * (x * y)`. The Rocq original is `conj_mul_left` of
the functor `CdTower` in `rocq/quantum/CdTowerDomain.v`. -/
theorem mul_star_mul_left {k : ℕ} (x y : Tower R k) :
    x * (star x * y) = star x * (x * y) := by
  sorry

/-- The mirror identity `x * y * star y = x * star y * y`. The Rocq original is
`conj_mul_right` of the functor `CdTower` in `rocq/quantum/CdTowerDomain.v`. -/
theorem mul_mul_star_right {k : ℕ} (x y : Tower R k) :
    x * y * star y = x * star y * y := by
  sorry

/-- Left multiplication by a pure element is skew for the trace form (Moreno 1997,
Proposition 1.7). The Rocq original is `l_x_skew_symm` of
`rocq/open/theories/C1539_MorSkewSymm.v`. -/
theorem dot_mul_left_of_star_eq_neg {k : ℕ} {a : Tower R k} (ha : star a = -a)
    (y z : Tower R k) : dot k (a * y) z = -dot k y (a * z) := by
  sorry

/-- Right multiplication by a pure element is skew for the trace form. The Rocq
original is `r_x_skew_symm` of `rocq/open/theories/C1539_MorSkewSymm.v`. -/
theorem dot_mul_right_of_star_eq_neg {k : ℕ} {a : Tower R k} (ha : star a = -a)
    (y z : Tower R k) : dot k (y * a) z = -dot k y (z * a) := by
  sorry

/-- `re (x * y) = re (y * x)` at every level (Lemma 2.6 of Biss, Dugger and Isaksen). The Rocq
original is `re_commutator` of the functor `CdTower` in `rocq/quantum/CdTowerDomain.v`, stated
there over an ordered domain; the proof uses the adjoint identities alone. -/
theorem re_mul_comm {k : ℕ} (x y : Tower R k) : re k (x * y) = re k (y * x) := by
  sorry

/-- `re ((x * y) * z) = re (x * (y * z))` at every level (Lemma 2.8 of Biss, Dugger and Isaksen).
The Rocq original is `re_associator` of the functor `CdTower` in
`rocq/quantum/CdTowerDomain.v`. -/
theorem re_mul_assoc {k : ℕ} (x y z : Tower R k) : re k (x * y * z) = re k (x * (y * z)) := by
  sorry

/-- Every right inverse `b` of `a` satisfies `a * (dot a a • b - star a) = 0`. The Rocq original
is `right_inverse_affine` of the functor `CdTower` in `rocq/quantum/CdTowerDomain.v`, stated
there over an ordered domain; the identity needs no order. -/
theorem mul_dot_smul_sub_star_eq_zero {k : ℕ} {a b : Tower R k} (h : a * b = 1) :
    a * (dot k a a • b - star a) = 0 := by
  sorry

/-- The symmetrized associator `x (y z) - (x y) z + z (y x) - (z y) x`, the `flex_sum` of
`rocq/quantum/CdTowerDomain.v`. -/
def flexSum {k : ℕ} (x y z : Tower R k) : Tower R k :=
  x * (y * z) - x * y * z + z * (y * x) - z * y * x

/-- The flexible law `(x * y) * x = x * (y * x)` at every level (Corollary 2.9 of Biss, Dugger and
Isaksen), over a commutative ring with the identity as star in which `2` is left regular
(`IsLeftRegular (2 : R)`, as in an ordered domain). The Rocq original is `flexible` of the
functor `CdTower` in `rocq/quantum/CdTowerDomain.v`. -/
theorem mul_mul_self_eq (h2 : IsLeftRegular (2 : R)) {k : ℕ} (x y : Tower R k) :
    x * y * x = x * (y * x) := by
  sorry

/-- When `2 = 0` in the coefficient ring the product commutes at every level. The Rocq original
is `two_zero_commutative` of the functor `RingTower` in `rocq/quantum/CdTowerRing.v`. -/
theorem mul_comm_of_two_eq_zero (h2 : (2 : R) = 0) :
    ∀ {k : ℕ} (x y : Tower R k), x * y = y * x := by
  sorry

section Gram

variable {k : ℕ}

end Gram

section Ordered

variable [PartialOrder R] [IsOrderedAddMonoid R] [NoZeroDivisors R]

/-- Lemma 9.2 of Biss, Dugger and Isaksen: `x * y = 0`, `star x * y = 0` and
`x * star y = 0` are equivalent, at every level, over a commutative ring with the
identity as star, no zero divisors, a partial order compatible with addition and
nonnegative squares. The Rocq original is `lemma_9_2` of the functor `CdTower` in
`rocq/quantum/CdTowerDomain.v`. -/
theorem mul_eq_zero_iff_star_mul_eq_zero (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ} (x y : Tower R k) :
    (x * y = 0 ↔ star x * y = 0) ∧ (x * y = 0 ↔ x * star y = 0) := by
  sorry

/-- Both factors of `z * a = 0` are pure when nonzero (Lemma 9.4 of Biss, Dugger and Isaksen,
on the other side). The Rocq original is `purity_right` of the functor `CdTower` in
`rocq/quantum/CdTowerDomain.v`. -/
theorem re_eq_zero_of_mul_eq_zero_rev (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ} {a z : Tower R k}
    (h : z * a = 0) (ha : a ≠ 0) (hz : z ≠ 0) : re k a = 0 ∧ re k z = 0 := by
  sorry

/-- A left zero divisor of level `k + 1` is orthogonal to `1` and to the adjoined unit
`(0, 1)` (Lemma 9.5 of Biss, Dugger and Isaksen). The Rocq original is `lemma_9_5` of the functor
`CdTower` in `rocq/quantum/CdTowerDomain.v`. -/
theorem dot_one_eq_zero_and_dot_mk_zero_one_of_mul_eq_zero (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ}
    {x y : Tower R (k + 1)} (h : x * y = 0) (hy : y ≠ 0) :
    dot (k + 1) x 1 = 0 ∧ dot (k + 1) x (mk 0 1) = 0 := by
  sorry

/-- A right zero divisor of level `k + 1` is orthogonal to `1` and to the adjoined unit. The
Rocq original is `annihilator_orthogonal` of the functor `CdTower` in
`rocq/quantum/CdTowerDomain.v`. -/
theorem dot_one_eq_zero_and_dot_mk_zero_one_of_mul_eq_zero_right (hsq : ∀ x : R, 0 ≤ x * x)
    {k : ℕ} {x y : Tower R (k + 1)} (hx : x ≠ 0) (h : x * y = 0) :
    dot (k + 1) y 1 = 0 ∧ dot (k + 1) y (mk 0 1) = 0 := by
  sorry

end Ordered

section Field

variable {K : Type u} [Field K] [StarRing K] [TrivialStar K] [PartialOrder K] [IsOrderedAddMonoid K]

/-- Over an ordered field every right inverse `b` of `a` is `(dot a a)⁻¹ • star a` plus an element
of the kernel of left multiplication by `a`. The Rocq original is `right_inverse_form` of the
functor `CdTowerField` in `rocq/quantum/CdTowerDomain.v`. -/
theorem exists_eq_inv_dot_smul_star_add (hsq : ∀ x : K, 0 ≤ x * x) {k : ℕ} {a b : Tower K k}
    (h : a * b = 1) : ∃ w, a * w = 0 ∧ b = (dot k a a)⁻¹ • star a + w := by
  sorry

end Field

section Instances

end Instances

end Tower

end CayleyDickson
