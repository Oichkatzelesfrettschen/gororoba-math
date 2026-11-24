/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.LeftMulMatrix
public import GororobaMath.CayleyDickson.AssociatorSpace
public import Mathlib.LinearAlgebra.Determinant

/-!
# The determinant of left multiplication under doubling

Convention: the product of `Tower R k` is the Cayley-Dickson product of
`GororobaMath.CayleyDickson.Tower`, `(a, b) (c, d) = (a c - conj(d) b, d a + b conj(c))`
(`Tower.mk_mul_mk`), over a commutative ring with the identity as star. `Tower.mulLeft R k a` is
`x ↦ a x` and `Tower.mulRight R k a` is `x ↦ x a`, both `R`-linear endomorphisms of the free
module `Tower R k` of rank `2 ^ k`, and `LinearMap.det` is the determinant of an endomorphism of a
finite free module, which no choice of basis changes.

The double of `a` is `(a, 0)`, and `(a, 0) (c, d) = (a c, d a)`: in the pair decomposition
`Tower R (k + 1) ≃ₗ Tower R k × Tower R k` left multiplication by `(a, 0)` is block diagonal with
blocks left and right multiplication by `a`. Conjugation reverses products, `conj (x y) =
conj y conj x`, so `x a = conj (conj a conj x)` and right multiplication by `a` is left
multiplication by `conj a` conjugated by the linear involution `conj`; the matrix of left
multiplication by `conj a` is the transpose of that of `a` (`Tower.toMatrix_mulLeft_star`).
This is the step of the determinant factorization of Koebisu, "Determinant Factorization of Left
Multiplication in the 32-Dimensional Cayley-Dickson Algebra" (2026, Lemma 8.2) that holds at every
level; the factorization `det L_x = N^2 D14^2` at dimension 32 is a fixed-dimension polynomial
identity and is not stated here.

## Main results

* `Tower.det_mulRight_eq_det_mulLeft`: `det R_a = det L_a`.
* `Tower.det_mulLeft_mk_zero_eq_mul`: `det L_(a, 0) = det L_a * det R_a`.
* `Tower.det_mulLeft_mk_zero`: `det L_(a, 0) = (det L_a) ^ 2`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] {k : ℕ}

variable (R k) in
/-- Conjugation of `Tower R k` as a linear equivalence; it is its own inverse. -/
def starLinearEquiv : Tower R k ≃ₗ[R] Tower R k where
  toFun := star
  map_add' := star_add
  map_smul' r x := star_smul' r x
  invFun := star
  left_inv := star_star
  right_inv := star_star

@[simp] theorem starLinearEquiv_apply (x : Tower R k) : starLinearEquiv R k x = star x := rfl

@[simp] theorem starLinearEquiv_symm_apply (x : Tower R k) :
    (starLinearEquiv R k).symm x = star x := rfl

/-- Right multiplication by `a` is left multiplication by `star a`, conjugated by `star`, since
`x a = star (star a * star x)`. -/
theorem mulRight_eq_conj_mulLeft_star (a : Tower R k) :
    mulRight R k a = (starLinearEquiv R k : Tower R k →ₗ[R] Tower R k) ∘ₗ mulLeft R k (star a) ∘ₗ
      ((starLinearEquiv R k).symm : Tower R k →ₗ[R] Tower R k) := by
  refine LinearMap.ext fun x => ?_
  simp only [mulRight_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, starLinearEquiv_symm_apply,
    mulLeft_apply, starLinearEquiv_apply, star_mul, star_star]

/-- Left multiplication by `star a` has the determinant of left multiplication by `a`, because its
matrix is the transpose. -/
theorem det_mulLeft_star (a : Tower R k) :
    LinearMap.det (mulLeft R k (star a)) = LinearMap.det (mulLeft R k a) := by
  rw [← LinearMap.det_toMatrix (basis R k) (mulLeft R k (star a)),
    ← LinearMap.det_toMatrix (basis R k) (mulLeft R k a), toMatrix_mulLeft_star,
    Matrix.det_transpose]

/-- Right and left multiplication by the same element have the same determinant. -/
theorem det_mulRight_eq_det_mulLeft (a : Tower R k) :
    LinearMap.det (mulRight R k a) = LinearMap.det (mulLeft R k a) := by
  rw [mulRight_eq_conj_mulLeft_star, LinearMap.det_conj, det_mulLeft_star]

/-- The pair decomposition of the double as a linear equivalence. -/
def doubleEquiv (R : Type u) [CommRing R] [StarRing R] [TrivialStar R] (k : ℕ) :
    Tower R (k + 1) ≃ₗ[R] Tower R k × Tower R k :=
  linearEquivProd (Tower R k) R

/-- In the pair decomposition of the double, left multiplication by `(a, 0)` is the product map of
left and right multiplication by `a`. -/
theorem conj_mulLeft_mk_zero (a : Tower R k) :
    (doubleEquiv R k : Tower R (k + 1) →ₗ[R] Tower R k × Tower R k) ∘ₗ
        mulLeft R (k + 1) (mk a 0) ∘ₗ
      ((doubleEquiv R k).symm : Tower R k × Tower R k →ₗ[R] Tower R (k + 1)) =
      (mulLeft R k a).prodMap (mulRight R k a) := by
  refine LinearMap.ext fun p => ?_
  obtain ⟨c, d⟩ := p
  have h : mk a 0 * mk c d = mk (a * c) (d * a) := by
    rw [mk_mul_mk]
    simp only [mul_zero, sub_zero, zero_mul, add_zero]
  exact congrArg (doubleEquiv R k) h

/-- The determinant of left multiplication by `(a, 0)` is the product of the determinants of left
and right multiplication by `a`. -/
theorem det_mulLeft_mk_zero_eq_mul (a : Tower R k) :
    LinearMap.det (mulLeft R (k + 1) (mk a 0)) =
      LinearMap.det (mulLeft R k a) * LinearMap.det (mulRight R k a) := by
  rw [← LinearMap.det_conj (mulLeft R (k + 1) (mk a 0))
      (doubleEquiv R k), conj_mulLeft_mk_zero, LinearMap.det_prodMap]

/-- The determinant of left multiplication by the double `(a, 0)` is the square of that of left
multiplication by `a`. -/
theorem det_mulLeft_mk_zero (a : Tower R k) :
    LinearMap.det (mulLeft R (k + 1) (mk a 0)) = LinearMap.det (mulLeft R k a) ^ 2 := by
  rw [det_mulLeft_mk_zero_eq_mul, det_mulRight_eq_det_mulLeft, sq]

end Tower

end CayleyDickson
