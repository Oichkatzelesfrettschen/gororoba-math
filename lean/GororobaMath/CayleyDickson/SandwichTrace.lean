/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.LinearCombination

/-!
# Trace of a sandwiched bivector against symmetric forms

Convention: matrices are `Mathlib.Matrix` over a commutative ring `R` indexed by a finite type
`ι`, `vecMulVec a b` is the matrix with entries `a i * b j`, `M *ᵥ x` is the product of `M` with
a column vector, and `x ⬝ᵥ y` is the dot product. For vectors `u v` the skew matrix of the
bivector `u ∧ v` is `P = vecMulVec u v - vecMulVec v u` (entry `(i, j)` is
`u i * v j - v i * u j`). A matrix `M` with `Mᵀ = M` is the symmetric form
`c x y = x ⬝ᵥ M *ᵥ y`.

## Main results

* `Matrix.skew_mul_mul_skew`: the sandwich `P * D * P` is a combination of four rank-one
  matrices with the coefficients `x ⬝ᵥ D *ᵥ y` for `x, y ∈ {u, v}`.
* `Matrix.trace_mul_skew_mul_skew`: for symmetric `C` and `D`,
  `trace (C * (P * D * P)) = 2 * c u v * d u v - c u u * d v v - c v v * d u u`.
* `Matrix.trace_mul_skew_mul_skew_of_rank_one`: when `d` factors through a function `l` on
  `u` and `v`, the trace is `-c w w` with `w = l v • u - l u • v`.
-/

@[expose] public section

namespace Matrix

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]

/-- A rank-one matrix sandwiched by `D` is a scalar multiple of a rank-one matrix: the middle
factors contract to `b ⬝ᵥ D *ᵥ c`. -/
theorem vecMulVec_mul_mul_vecMulVec (a b c e : ι → R) (D : Matrix ι ι R) :
    vecMulVec a b * D * vecMulVec c e = (b ⬝ᵥ D *ᵥ c) • vecMulVec a e := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, smul_apply, smul_eq_mul, dotProduct, mulVec,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- The trace of `C` against a rank-one matrix is the value of `C` on its two vectors. -/
theorem trace_mul_vecMulVec (C : Matrix ι ι R) (a b : ι → R) :
    trace (C * vecMulVec a b) = b ⬝ᵥ C *ᵥ a := by
  simp only [trace, diag_apply, Matrix.mul_apply, vecMulVec_apply, dotProduct, mulVec,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- The quadratic form of a symmetric matrix is symmetric in its two arguments. -/
theorem dotProduct_mulVec_comm_of_transpose_eq {D : Matrix ι ι R} (hD : Dᵀ = D) (x y : ι → R) :
    x ⬝ᵥ D *ᵥ y = y ⬝ᵥ D *ᵥ x := by
  rw [dotProduct_mulVec, ← hD, vecMul_transpose, hD, dotProduct_comm]

/-- The sandwich of a bivector matrix `P = u vᵀ - v uᵀ` around `D` expands in the four rank-one
matrices of `u` and `v`. -/
theorem skew_mul_mul_skew (u v : ι → R) (D : Matrix ι ι R) :
    (vecMulVec u v - vecMulVec v u) * D * (vecMulVec u v - vecMulVec v u) =
      (v ⬝ᵥ D *ᵥ u) • vecMulVec u v - (v ⬝ᵥ D *ᵥ v) • vecMulVec u u
        - (u ⬝ᵥ D *ᵥ u) • vecMulVec v v + (u ⬝ᵥ D *ᵥ v) • vecMulVec v u := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, vecMulVec_mul_mul_vecMulVec]
  abel

/-- For symmetric `C` and `D`, the trace of `C * (P * D * P)` for `P = u vᵀ - v uᵀ` is
`2 c(u,v) d(u,v) - c(u,u) d(v,v) - c(v,v) d(u,u)`. -/
theorem trace_mul_skew_mul_skew {C D : Matrix ι ι R} (hC : Cᵀ = C) (hD : Dᵀ = D) (u v : ι → R) :
    trace (C * ((vecMulVec u v - vecMulVec v u) * D * (vecMulVec u v - vecMulVec v u))) =
      2 * (u ⬝ᵥ C *ᵥ v) * (u ⬝ᵥ D *ᵥ v) - (u ⬝ᵥ C *ᵥ u) * (v ⬝ᵥ D *ᵥ v)
        - (v ⬝ᵥ C *ᵥ v) * (u ⬝ᵥ D *ᵥ u) := by
  rw [skew_mul_mul_skew]
  simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul, trace_add, trace_sub, trace_smul,
    trace_mul_vecMulVec, smul_eq_mul]
  rw [dotProduct_mulVec_comm_of_transpose_eq hD v u, dotProduct_mulVec_comm_of_transpose_eq hC v u]
  ring

/-- If `d` factors as `l * l` on `u` and `v`, the trace of `trace_mul_skew_mul_skew` is
`-c(w,w)` for `w = l v • u - l u • v`; the proof uses that `C` is symmetric. -/
theorem trace_mul_skew_mul_skew_of_rank_one {C : Matrix ι ι R} (hC : Cᵀ = C) (u v : ι → R)
    (l : (ι → R) → R) (d : (ι → R) → (ι → R) → R) (huu : d u u = l u * l u)
    (hvv : d v v = l v * l v) (huv : d u v = l u * l v) :
    2 * (u ⬝ᵥ C *ᵥ v) * d u v - (u ⬝ᵥ C *ᵥ u) * d v v - (v ⬝ᵥ C *ᵥ v) * d u u =
      -((l v • u - l u • v) ⬝ᵥ C *ᵥ (l v • u - l u • v)) := by
  rw [huu, hvv, huv]
  simp only [mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  rw [dotProduct_mulVec_comm_of_transpose_eq hC v u]
  ring

/-- Over a field with `2 ≠ 0`, take a subspace `K`, a linear form `l` that is nonzero on `K`
and a symmetric `D` with `x ⬝ᵥ D *ᵥ y = l x * l y` on `K`. The trace of
`trace_mul_skew_mul_skew` vanishes for every `u, v ∈ K` exactly when the symmetric form of `C`
vanishes on pairs of vectors of `K` that `l` kills. -/
theorem trace_mul_skew_mul_skew_eq_zero_iff {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (K : Submodule F (ι → F)) (l : (ι → F) →ₗ[F] F) (hl : ∃ k ∈ K, l k ≠ 0)
    {C D : Matrix ι ι F} (hC : Cᵀ = C) (hD : Dᵀ = D)
    (hd : ∀ x ∈ K, ∀ y ∈ K, x ⬝ᵥ D *ᵥ y = l x * l y) :
    (∀ u ∈ K, ∀ v ∈ K,
        trace (C * ((vecMulVec u v - vecMulVec v u) * D * (vecMulVec u v - vecMulVec v u))) = 0) ↔
      ∀ x ∈ K, ∀ y ∈ K, l x = 0 → l y = 0 → x ⬝ᵥ C *ᵥ y = 0 := by
  have key : ∀ u ∈ K, ∀ v ∈ K,
      trace (C * ((vecMulVec u v - vecMulVec v u) * D * (vecMulVec u v - vecMulVec v u))) =
        -((l v • u - l u • v) ⬝ᵥ C *ᵥ (l v • u - l u • v)) := by
    intro u hu v hv
    rw [trace_mul_skew_mul_skew hC hD]
    exact trace_mul_skew_mul_skew_of_rank_one hC u v l (fun x y => x ⬝ᵥ D *ᵥ y)
      (hd u hu u hu) (hd v hv v hv) (hd u hu v hv)
  constructor
  · intro h
    obtain ⟨k, hkK, hk⟩ := hl
    have hq : ∀ w ∈ K, l w = 0 → w ⬝ᵥ C *ᵥ w = 0 := by
      intro w hw hlw
      have hk' : (l k)⁻¹ • k ∈ K := K.smul_mem _ hkK
      have h1 := h w hw _ hk'
      rw [key w hw _ hk'] at h1
      have hl1 : l ((l k)⁻¹ • k) = 1 := by
        rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hk]
      rw [hl1, hlw, one_smul, zero_smul, sub_zero] at h1
      exact neg_eq_zero.mp h1
    intro x hx y hy hlx hly
    have hxy := hq (x + y) (K.add_mem hx hy) (by rw [map_add, hlx, hly, add_zero])
    simp only [mulVec_add, dotProduct_add, add_dotProduct] at hxy
    rw [dotProduct_mulVec_comm_of_transpose_eq hC y x, hq x hx hlx, hq y hy hly] at hxy
    have : (2 : F) * (x ⬝ᵥ C *ᵥ y) = 0 := by linear_combination hxy
    exact (mul_eq_zero.mp this).resolve_left h2
  · intro h u hu v hv
    rw [key u hu v hv]
    have hw : l v • u - l u • v ∈ K := K.sub_mem (K.smul_mem _ hu) (K.smul_mem _ hv)
    have hlw : l (l v • u - l u • v) = 0 := by
      rw [map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]; ring
    rw [h _ hw _ hw hlw hlw, neg_zero]

end Matrix
