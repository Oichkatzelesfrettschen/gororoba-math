/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TraceForm
public import GororobaMath.CayleyDickson.RingLaws
public import GororobaMath.CayleyDickson.AssociatorSpace

/-!
# Half folds of the kernel of left multiplication

Convention: `Tower R k` is the tower of `GororobaMath.CayleyDickson.Tower` over a commutative
ring `R` whose star is the identity, with the product
`(a, b) (c, d) = (a c - star d b, d a + b star c)`. `Tower.mulLeft R k x` is left multiplication
by `x` as an `R`-linear map. In the ordered section (a partial order compatible with addition,
no zero divisors, and nonnegative squares `hsq`) the kernel swap `x * y = 0 ↔ y * x = 0` holds.

The product of `(a, 0)` with `(c, d)` is `(a c, d a)` and that of `(0, b)` with `(c, d)` is
`(-(star d b), b star c)`, so `(a, 0) (c, d) = 0` exactly when `a c = 0 = a d`, and
`(0, b) (c, d) = 0` exactly when `b c = 0 = b d`. The kernel of left multiplication by
`(a, 0)` at level `k + 1` is then the product of two copies of the kernel of `a` at level `k`,
so its dimension doubles (`Tower.finrank_ker_mulLeft_mk_left`). For a pure `a`, the second copy
is the image of the kernel under `star`, which needs no order
(`Tower.finrank_ker_mulLeft_mk_left_of_star_eq_neg`).

## Main results

* `Tower.mk_left_mul_eq_zero_iff`: the Rocq `first_half` of the module `HalfFold` in
  `rocq/quantum/CdHalfFold.v`.
* `Tower.mk_right_mul_eq_zero_iff`: the Rocq `second_half` of the same module.
* `Tower.finrank_ker_mulLeft_mk_left`, `Tower.finrank_ker_mulLeft_mk_right`: the Rocq
  `half_fold_dimension_low` and `half_fold_dimension_high` of the module
  `RealHalfFoldDimension` in the same file, stated there with a `has_dim` predicate over the
  reals and here over every ordered field.
* `Tower.finrank_ker_mulLeft_mk_left_of_star_eq_neg`: the Rocq `pure_doubling_nullity` of
  `rocq/open/theories/CDPureDoublingKernel.v`, over every field with the identity as star.
* `Tower.finrank_range_mulRight_of_star_eq_neg`: the Rocq `pure_right_left_rank` of the same
  file.
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
  rw [mk_mul_mk, zero_eq_mk, mk_inj, mul_zero, sub_zero, zero_mul, add_zero,
    mul_eq_zero_iff_rev hsq d a]

/-- `(0, b) (c, d) = 0` exactly when `b c = 0` and `b d = 0`. The Rocq original is `second_half`
of the module `HalfFold` in `rocq/quantum/CdHalfFold.v`. -/
theorem mk_right_mul_eq_zero_iff (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ} (b c d : Tower R k) :
    mk 0 b * mk c d = 0 ↔ b * c = 0 ∧ b * d = 0 := by
  have h1 : star d * b = 0 ↔ b * d = 0 :=
    (mul_eq_zero_iff_rev hsq (star d) b).trans (mul_eq_zero_iff_star_mul_eq_zero hsq b d).2.symm
  have h2 : b * star c = 0 ↔ b * c = 0 := (mul_eq_zero_iff_star_mul_eq_zero hsq b c).2.symm
  rw [mk_mul_mk, zero_eq_mk, mk_inj, zero_mul, zero_sub, mul_zero, zero_add, neg_eq_zero, h1, h2]
  exact and_comm

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

/-- If `z * (c, d) = 0` exactly when `a * c = 0` and `a * σ d = 0` for a linear equivalence `σ`,
then the kernel of left multiplication by `z` at level `k + 1` has twice the dimension of the
kernel of left multiplication by `a` at level `k`. -/
theorem finrank_ker_mulLeft_eq_two_mul {k : ℕ} (z : Tower K (k + 1)) (a : Tower K k)
    (σ : Tower K k ≃ₗ[K] Tower K k)
    (h : ∀ c d : Tower K k, z * mk c d = 0 ↔ a * c = 0 ∧ a * σ d = 0) :
    finrank K (LinearMap.ker (mulLeft K (k + 1) z)) =
      2 * finrank K (LinearMap.ker (mulLeft K k a)) := by
  have hx : ∀ x : LinearMap.ker (mulLeft K (k + 1) z),
      a * CayleyDickson.re (A := Tower K k) x.1 = 0 ∧
        a * σ (CayleyDickson.im (A := Tower K k) x.1) = 0 := fun x =>
    (h (CayleyDickson.re (A := Tower K k) x.1) (CayleyDickson.im (A := Tower K k) x.1)).1 x.2
  let e : LinearMap.ker (mulLeft K (k + 1) z) ≃ₗ[K]
      LinearMap.ker (mulLeft K k a) × LinearMap.ker (mulLeft K k a) :=
    { toFun := fun x => (⟨CayleyDickson.re (A := Tower K k) x.1, (hx x).1⟩,
        ⟨σ (CayleyDickson.im (A := Tower K k) x.1), (hx x).2⟩)
      invFun := fun p => ⟨mk p.1.1 (σ.symm p.2.1), (h _ _).2
        ⟨p.1.2, by rw [LinearEquiv.apply_symm_apply]; exact p.2.2⟩⟩
      map_add' := fun x y => Prod.ext (Subtype.ext rfl) (Subtype.ext (map_add σ _ _))
      map_smul' := fun m x => Prod.ext (Subtype.ext rfl) (Subtype.ext (map_smul σ _ _))
      left_inv := fun x => Subtype.ext (by
        change mk (CayleyDickson.re (A := Tower K k) x.1)
          (σ.symm (σ (CayleyDickson.im (A := Tower K k) x.1))) = x.1
        rw [LinearEquiv.symm_apply_apply]
        rfl)
      right_inv := fun p => Prod.ext (Subtype.ext rfl) (Subtype.ext (σ.apply_symm_apply _)) }
  rw [e.finrank_eq, Module.finrank_prod, two_mul]

/-- The kernel of left multiplication by `(a, 0)` at level `k + 1` has twice the dimension of the
kernel of `a` at level `k`, over an ordered field. The Rocq original is
`half_fold_dimension_low` of the module `RealHalfFoldDimension` in
`rocq/quantum/CdHalfFold.v`. -/
theorem finrank_ker_mulLeft_mk_left [PartialOrder K] [IsOrderedAddMonoid K]
    (hsq : ∀ x : K, 0 ≤ x * x) {k : ℕ} (a : Tower K k) :
    finrank K (LinearMap.ker (mulLeft K (k + 1) (mk a 0))) =
      2 * finrank K (LinearMap.ker (mulLeft K k a)) :=
  finrank_ker_mulLeft_eq_two_mul _ a (LinearEquiv.refl K _) fun c d =>
    mk_left_mul_eq_zero_iff hsq a c d

/-- The kernel of left multiplication by `(0, b)` at level `k + 1` has twice the dimension of the
kernel of `b` at level `k`, over an ordered field. The Rocq original is
`half_fold_dimension_high` of the module `RealHalfFoldDimension` in
`rocq/quantum/CdHalfFold.v`. -/
theorem finrank_ker_mulLeft_mk_right [PartialOrder K] [IsOrderedAddMonoid K]
    (hsq : ∀ x : K, 0 ≤ x * x) {k : ℕ} (b : Tower K k) :
    finrank K (LinearMap.ker (mulLeft K (k + 1) (mk 0 b))) =
      2 * finrank K (LinearMap.ker (mulLeft K k b)) :=
  finrank_ker_mulLeft_eq_two_mul _ b (LinearEquiv.refl K _) fun c d =>
    mk_right_mul_eq_zero_iff hsq b c d

/-- For a pure `a`, the left nullity of `(a, 0)` at level `k + 1` is twice the left nullity of
`a` at level `k`; the order of the real original is replaced by purity. The Rocq original is
`pure_doubling_nullity` of `rocq/open/theories/CDPureDoublingKernel.v`. -/
theorem finrank_ker_mulLeft_mk_left_of_star_eq_neg {k : ℕ} {a : Tower K k} (ha : star a = -a) :
    finrank K (LinearMap.ker (mulLeft K (k + 1) (mk a 0))) =
      2 * finrank K (LinearMap.ker (mulLeft K k a)) :=
  finrank_ker_mulLeft_eq_two_mul _ a (starEquiv k) fun c d =>
    mk_mul_mk_eq_zero_iff_of_star_eq_neg ha c d

/-- For a pure `a`, right and left multiplication by `a` have equal rank. The Rocq original is
`pure_right_left_rank` of `rocq/open/theories/CDPureDoublingKernel.v`. -/
theorem finrank_range_mulRight_of_star_eq_neg {k : ℕ} {a : Tower K k} (ha : star a = -a) :
    finrank K (LinearMap.range (mulRight K k a)) = finrank K (LinearMap.range (mulLeft K k a)) := by
  let e : LinearMap.ker (mulRight K k a) ≃ₗ[K] LinearMap.ker (mulLeft K k a) :=
    { toFun := fun x => ⟨star x.1, (mul_eq_zero_iff_mul_star_of_star_eq_neg ha x.1).1 x.2⟩
      invFun := fun y => ⟨star y.1, by
        have h := (mul_eq_zero_iff_star_mul_of_star_eq_neg ha y.1).1 y.2
        exact h⟩
      map_add' := fun x y => Subtype.ext (star_add _ _)
      map_smul' := fun m x => Subtype.ext (star_smul' m x.1)
      left_inv := fun x => Subtype.ext (star_star _)
      right_inv := fun y => Subtype.ext (star_star _) }
  have h1 := LinearMap.finrank_range_add_finrank_ker (mulRight K k a)
  have h2 := LinearMap.finrank_range_add_finrank_ker (mulLeft K k a)
  have h3 := e.finrank_eq
  omega

end Field

end Tower

end CayleyDickson
