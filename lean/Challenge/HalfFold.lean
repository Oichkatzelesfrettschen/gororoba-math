/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TraceForm
public import GororobaMath.CayleyDickson.RingLaws
public import GororobaMath.CayleyDickson.AssociatorSpace

/-!
# Challenge: the half-fold of the kernel of left multiplication

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

open Module

section Ordered

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] [PartialOrder R]
  [IsOrderedAddMonoid R] [NoZeroDivisors R]

/-- `(a, 0) (c, d) = 0` exactly when `a c = 0` and `a d = 0`. The Rocq original is `first_half`
of the module `HalfFold` in `rocq/quantum/CdHalfFold.v`. -/
theorem mk_left_mul_eq_zero_iff (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ} (a c d : Tower R k) :
    mk a 0 * mk c d = 0 ↔ a * c = 0 ∧ a * d = 0 := by
  sorry

/-- `(0, b) (c, d) = 0` exactly when `b c = 0` and `b d = 0`. The Rocq original is `second_half`
of the module `HalfFold` in `rocq/quantum/CdHalfFold.v`. -/
theorem mk_right_mul_eq_zero_iff (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ} (b c d : Tower R k) :
    mk 0 b * mk c d = 0 ↔ b * c = 0 ∧ b * d = 0 := by
  sorry

end Ordered

section Field

variable {K : Type u} [Field K] [StarRing K] [TrivialStar K]

/-- The conjugation of `Tower K k` as a linear equivalence. -/
def starEquiv (k : ℕ) : Tower K k ≃ₗ[K] Tower K k where
  toFun := star
  map_add' := star_add
  map_smul' r x := star_smul' r x
  invFun := star
  left_inv := star_star
  right_inv := star_star

/-- The kernel of left multiplication by `(a, 0)` at level `k + 1` has twice the dimension of the
kernel of `a` at level `k`, over an ordered field. The Rocq original is
`half_fold_dimension_low` of the module `RealHalfFoldDimension` in
`rocq/quantum/CdHalfFold.v`. -/
theorem finrank_ker_mulLeft_mk_left [PartialOrder K] [IsOrderedAddMonoid K]
    (hsq : ∀ x : K, 0 ≤ x * x) {k : ℕ} (a : Tower K k) :
    finrank K (LinearMap.ker (mulLeft K (k + 1) (mk a 0))) =
      2 * finrank K (LinearMap.ker (mulLeft K k a)) := by
  sorry

/-- The kernel of left multiplication by `(0, b)` at level `k + 1` has twice the dimension of the
kernel of `b` at level `k`, over an ordered field. The Rocq original is
`half_fold_dimension_high` of the module `RealHalfFoldDimension` in
`rocq/quantum/CdHalfFold.v`. -/
theorem finrank_ker_mulLeft_mk_right [PartialOrder K] [IsOrderedAddMonoid K]
    (hsq : ∀ x : K, 0 ≤ x * x) {k : ℕ} (b : Tower K k) :
    finrank K (LinearMap.ker (mulLeft K (k + 1) (mk 0 b))) =
      2 * finrank K (LinearMap.ker (mulLeft K k b)) := by
  sorry

/-- For a pure `a`, the left nullity of `(a, 0)` at level `k + 1` is twice the left nullity of
`a` at level `k`; the order of the real original is replaced by purity. The Rocq original is
`pure_doubling_nullity` of `rocq/open/theories/CDPureDoublingKernel.v`. -/
theorem finrank_ker_mulLeft_mk_left_of_star_eq_neg {k : ℕ} {a : Tower K k} (ha : star a = -a) :
    finrank K (LinearMap.ker (mulLeft K (k + 1) (mk a 0))) =
      2 * finrank K (LinearMap.ker (mulLeft K k a)) := by
  sorry

/-- For a pure `a`, right and left multiplication by `a` have equal rank. The Rocq original is
`pure_right_left_rank` of `rocq/open/theories/CDPureDoublingKernel.v`. -/
theorem finrank_range_mulRight_of_star_eq_neg {k : ℕ} {a : Tower K k} (ha : star a = -a) :
    finrank K (LinearMap.range (mulRight K k a)) = finrank K (LinearMap.range (mulLeft K k a)) := by
  sorry

end Field

end Tower

end CayleyDickson
