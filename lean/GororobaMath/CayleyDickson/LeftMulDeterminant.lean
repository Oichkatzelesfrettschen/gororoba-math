/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.LeftMulMatrix
public import GororobaMath.CayleyDickson.AssociatorSpace
public import GororobaMath.CayleyDickson.AlternativeIdentities
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Ring.Real

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
* `Tower.det_mulLeft_sq_of_le_three`: `(det L_a) ^ 2 = (dot a a) ^ (2 ^ k)` at levels 0 to 3,
  from the left inverse property `conj a * (a * y) = dot a a • y`.
* `Tower.det_mulLeft_eq_or_eq_neg_of_le_three`: in a domain, `det L_a = ± (dot a a) ^ (2 ^ j)` at
  level `j + 1 ≤ 3`.
* `Tower.det_mulLeft_nonneg`: `0 ≤ det L_x` over `ℝ` at every level `k + 1`, from
  `L_x = re x • id + L_u` with `L_u` skew.
* `Tower.det_mulLeft_eq_dot_pow_of_le_three`: `det L_a = (dot a a) ^ (2 ^ j)` over `ℝ` at level
  `j + 1 ≤ 3`.
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

section Composition

/-- At levels 0 to 3 the square of the determinant of left multiplication by `a` is the `2 ^ k`-th
power of `dot a a`, because left multiplication by `conj a` after left multiplication by `a` is
the scalar `dot a a` and `det L_(conj a) = det L_a`. -/
theorem det_mulLeft_sq_of_le_three [Nontrivial R] (hk : k ≤ 3) (a : Tower R k) :
    LinearMap.det (mulLeft R k a) ^ 2 = dot k a a ^ (2 ^ k) := by
  have hcomp : mulLeft R k (star a) ∘ₗ mulLeft R k a = dot k a a • LinearMap.id := by
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, mulLeft_apply, LinearMap.smul_apply, LinearMap.id_apply]
    exact star_mul_mul_of_le_three hk a y
  have h := congrArg LinearMap.det hcomp
  rw [LinearMap.det_comp, det_mulLeft_star, LinearMap.det_smul, LinearMap.det_id, finrank_eq,
    mul_one] at h
  rw [sq]
  exact h

/-- In a domain, `det L_a = ± (dot a a) ^ (2 ^ j)` at levels 1 to 3 (`k = j + 1`). -/
theorem det_mulLeft_eq_or_eq_neg_of_le_three [IsDomain R] {j : ℕ}
    (hk : j + 1 ≤ 3) (a : Tower R (j + 1)) :
    LinearMap.det (mulLeft R (j + 1) a) = dot (j + 1) a a ^ (2 ^ j) ∨
      LinearMap.det (mulLeft R (j + 1) a) = -dot (j + 1) a a ^ (2 ^ j) := by
  refine sq_eq_sq_iff_eq_or_eq_neg.1 ?_
  rw [det_mulLeft_sq_of_le_three hk, ← pow_mul, pow_succ, mul_comm]

end Composition

section Real

/-- For a real skew matrix `S`, `det (1 + s S)` is positive for every real `s`: it never vanishes,
since `v ⬝ (1 + s S) v = v ⬝ v`, and it is `1` at `s = 0`. -/
theorem det_one_add_smul_skew_pos {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ)
    (hS : S.transpose = -S) (s : ℝ) : 0 < (1 + s • S).det := by
  have hne : ∀ s : ℝ, (1 + s • S).det ≠ 0 := by
    intro s h0
    obtain ⟨v, hv, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have h1 : v ⬝ᵥ (1 + s • S).mulVec v = 0 := by rw [hmv]; simp
    have e : Matrix.vecMul v S = -(S.mulVec v) := by
      rw [← Matrix.mulVec_transpose, hS, Matrix.neg_mulVec]
    have h2 : v ⬝ᵥ S.mulVec v = 0 := by
      have : v ⬝ᵥ S.mulVec v = -(v ⬝ᵥ S.mulVec v) := by
        calc v ⬝ᵥ S.mulVec v = Matrix.vecMul v S ⬝ᵥ v := Matrix.dotProduct_mulVec v S v
          _ = -(S.mulVec v) ⬝ᵥ v := by rw [e]
          _ = -(S.mulVec v ⬝ᵥ v) := neg_dotProduct _ _
          _ = -(v ⬝ᵥ S.mulVec v) := by rw [dotProduct_comm]
      linarith
    simp only [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, h2, smul_zero, add_zero] at h1
    exact hv (dotProduct_self_eq_zero.1 h1)
  have hc : Continuous fun s : ℝ => (1 + s • S).det :=
    Continuous.matrix_det (continuous_const.add (continuous_id.smul continuous_const))
  by_contra hneg
  have hlt : (1 + s • S).det < 0 := lt_of_le_of_ne (not_lt.1 hneg) (hne s)
  obtain ⟨s', hs'⟩ := intermediate_value_univ s 0 hc ⟨hlt.le, by simp⟩
  exact hne s' hs'

/-- For a real skew matrix `S` of even size, `det (t • 1 + S) ≥ 0` for every real `t`. -/
theorem det_smul_one_add_skew_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ)
    (hS : S.transpose = -S) (hev : Even (Fintype.card ι)) (t : ℝ) :
    0 ≤ (t • (1 : Matrix ι ι ℝ) + S).det := by
  have hpos : ∀ t : ℝ, t ≠ 0 → 0 < (t • (1 : Matrix ι ι ℝ) + S).det := by
    intro t ht
    have h : t • (1 : Matrix ι ι ℝ) + S = t • (1 + t⁻¹ • S) := by
      rw [smul_add, smul_smul, mul_inv_cancel₀ ht, one_smul]
    rw [h, Matrix.det_smul]
    exact mul_pos (hev.pow_pos ht) (det_one_add_smul_skew_pos S hS _)
  have hc : Continuous fun t : ℝ => (t • (1 : Matrix ι ι ℝ) + S).det :=
    Continuous.matrix_det ((continuous_id.smul continuous_const).add continuous_const)
  by_cases h0 : t = 0
  · subst h0
    refine ge_of_tendsto (x := nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) ?_
    exact eventually_nhdsWithin_of_forall fun u hu => (hpos u (ne_of_gt hu)).le
  · exact (hpos t h0).le

/-- Left multiplication by a real element `x` of level `k + 1` has a nonnegative determinant: `L_x`
is `re x` times the identity plus left multiplication by the pure element `x - re x`, a skew
matrix (Koebisu 2026, the nonnegativity statement of the determinant section). -/
theorem det_mulLeft_nonneg {k : ℕ} (x : Tower ℝ (k + 1)) :
    0 ≤ LinearMap.det (mulLeft ℝ (k + 1) x) := by
  set r : ℝ := re (k + 1) x with hr
  set u : Tower ℝ (k + 1) := x - r • 1 with hu
  have hstar : star u = -u := by
    have h1 : star (r • (1 : Tower ℝ (k + 1))) = r • 1 := by rw [star_smul', star_one]
    rw [hu, star_sub, h1, star_eq_smul_one_sub x, ← hr]
    have : (2 * r) • (1 : Tower ℝ (k + 1)) = r • 1 + r • 1 := by rw [two_mul, add_smul]
    rw [this]
    abel
  have hL : mulLeft ℝ (k + 1) x = r • LinearMap.id + mulLeft ℝ (k + 1) u := by
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, mulLeft_apply, hu,
      sub_mul, smul_mul_assoc', one_mul]
    abel
  have hneg : mulLeft ℝ (k + 1) (-u) = -mulLeft ℝ (k + 1) u :=
    LinearMap.ext fun y => by simp only [mulLeft_apply, LinearMap.neg_apply, neg_mul]
  set S := LinearMap.toMatrix (basis ℝ (k + 1)) (basis ℝ (k + 1)) (mulLeft ℝ (k + 1) u) with hSdef
  have hS : S.transpose = -S := by
    rw [hSdef, ← toMatrix_mulLeft_star, hstar, hneg, map_neg]
  have hcard : Fintype.card (BitVec (k + 1)) = 2 ^ (k + 1) :=
    (Module.finrank_eq_card_basis (basis ℝ (k + 1))).symm.trans (finrank_eq ℝ (k + 1))
  rw [← LinearMap.det_toMatrix (basis ℝ (k + 1)), hL, map_add, map_smul, LinearMap.toMatrix_id]
  exact det_smul_one_add_skew_nonneg S hS (hcard ▸ ⟨2 ^ k, by ring⟩) r

/-- At levels 1 to 3 over the reals, `det L_a = (dot a a) ^ (2 ^ j)` (`k = j + 1`). -/
theorem det_mulLeft_eq_dot_pow_of_le_three {j : ℕ} (hk : j + 1 ≤ 3) (a : Tower ℝ (j + 1)) :
    LinearMap.det (mulLeft ℝ (j + 1) a) = dot (j + 1) a a ^ (2 ^ j) := by
  have hsq : ∀ x : ℝ, 0 ≤ x * x := fun x => mul_self_nonneg x
  have hN : 0 ≤ dot (j + 1) a a ^ (2 ^ j) := pow_nonneg (dot_self_nonneg hsq (j + 1) a) _
  refine (pow_left_inj₀ (det_mulLeft_nonneg a) hN two_ne_zero).1 ?_
  rw [det_mulLeft_sq_of_le_three hk, ← pow_mul, pow_succ, mul_comm]

end Real

end Tower

end CayleyDickson
