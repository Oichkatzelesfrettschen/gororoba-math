/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.CzMatrix
public import GororobaMath.CayleyDickson.Strata
public import GororobaMath.CayleyDickson.LeftMulMatrix
public import GororobaMath.LinearAlgebra.BorderedKernel
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Left multiplication by a pure element is a bordered skew matrix; nullity is `2^k - 2 - rank C_z`

Convention: `Tower K k` is the Cayley-Dickson tower of `GororobaMath.CayleyDickson.Tower` over a
field `K` whose star is the identity, with the basis `Tower.basis K k` indexed by `BitVec k`
(index `p` is `p.toNat` of `cd_core.cd_sign`). A pure element `y` is one whose coordinate at index
`0` vanishes, and `p y` is the vector of its coordinates at the nonzero indices
(`NonzeroIndex k`). `Tower.borderEquiv k` identifies `Unit ⊕ NonzeroIndex k` with `BitVec k`,
the `Unit` summand being index `0`. `Matrix.bordered M p` is `[[0, -pᵀ], [p, M]]` of
`GororobaMath.LinearAlgebra.BorderedKernel`, and `Tower.czMatrix y` is the matrix `C_y` of
`GororobaMath.CayleyDickson.CzMatrix`. The inner product `p y ⬝ᵥ p y` is the bilinear sum of
squares of the coordinates, with no conjugation. `Tower.nullity K k y` is the dimension of the
kernel of left multiplication by `y`.

## Main results

* `Tower.mulLeft_matrix_bordered`: for a pure `y`, the matrix of left multiplication by `y`,
  reindexed by `borderEquiv`, is `bordered (czMatrix y) (p y)`.
* `Tower.nullity_add_rank_add_two`: for a pure `y` with `p y ⬝ᵥ p y ≠ 0`,
  `nullity y + rank C_y + 2 = 2 ^ k`.
* `Tower.nullity_add_rank_add_two_of_ne_zero`: the same hypothesis holds for every nonzero pure
  `y` over an ordered field.
* `Tower.nullity_add_rank_level_five`: at level `5`, `nullity y + rank C_y = 30`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

open Module Matrix

/-- The identification of `Unit ⊕ NonzeroIndex k` with `BitVec k`: the `Unit` summand is index
`0`. -/
def borderEquiv (k : ℕ) : Unit ⊕ NonzeroIndex k ≃ BitVec k where
  toFun := Sum.elim (fun _ => 0#k) Subtype.val
  invFun i := if h : i = 0#k then Sum.inl () else Sum.inr ⟨i, h⟩
  left_inv := by
    rintro (⟨⟩ | ⟨i, hi⟩)
    · simp
    · simp [hi]
  right_inv i := by
    by_cases h : i = 0#k <;> simp [h]

@[simp] theorem borderEquiv_inl (k : ℕ) (u : Unit) : borderEquiv k (Sum.inl u) = 0#k := rfl

@[simp] theorem borderEquiv_inr (k : ℕ) (c : NonzeroIndex k) : borderEquiv k (Sum.inr c) = c.1 :=
  rfl

/-- The rank of a square matrix plus the dimension of its kernel is the size. -/
theorem _root_.Matrix.rank_add_finrank_ker_toLin' {K : Type*} [Field K] {n : Type*} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) :
    M.rank + finrank K (LinearMap.ker (Matrix.toLin' M)) = Fintype.card n := by
  have h := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  rw [Matrix.toLin'_apply']
  exact h

variable {K : Type u} [Field K] [StarRing K] [TrivialStar K] {k : ℕ}

/-- The sign of `e c * e c` is `-1` for `c ≠ 0`. -/
theorem sign_self_of_ne {c : BitVec k} (hc : c ≠ 0#k) : sign k c c = -1 := by
  simp [sign, negSign_self k c hc]

/-- The sign of `e p * e 0` is `1`. -/
theorem sign_zero_right_eq_one (p : BitVec k) : sign k p 0#k = 1 := by
  simp [sign, negSign_zero_right]

theorem toMatrix_mulLeft_apply (y : Tower K k) (i j : BitVec k) :
    LinearMap.toMatrix (basis K k) (basis K k) (mulLeft K k y) i j =
      (basis K k).repr (y * e K k j) i := by
  simp [LinearMap.toMatrix_apply, basis_apply]

/-- For a pure `y` the matrix of left multiplication by `y` is `[[0, -pᵀ], [p, C_y]]` in the
basis ordered as index `0` first: `y * 1 = y` gives the column `p`, and the coordinate of
`y * e c` at `0` is `sign c c * y_c = -y_c`. -/
theorem mulLeft_matrix_bordered {y : Tower K k} (hy : (basis K k).repr y 0#k = 0) :
    (LinearMap.toMatrix (basis K k) (basis K k) (mulLeft K k y)).submatrix (borderEquiv k)
        (borderEquiv k) =
      Matrix.bordered (czMatrix y) (fun c : NonzeroIndex k => (basis K k).repr y c.1) := by
  ext (⟨⟩ | r) (⟨⟩ | c)
  · rw [submatrix_apply, borderEquiv_inl, toMatrix_mulLeft_apply, e_zero, mul_one, hy]
    simp [bordered]
  · rw [submatrix_apply, borderEquiv_inl, borderEquiv_inr, toMatrix_mulLeft_apply, repr_mul_e,
      BitVec.zero_xor, sign_self_of_ne c.2]
    simp [bordered]
  · rw [submatrix_apply, borderEquiv_inr, borderEquiv_inl, toMatrix_mulLeft_apply, e_zero,
      mul_one]
    simp [bordered]
  · rw [submatrix_apply, borderEquiv_inr, borderEquiv_inr, toMatrix_mulLeft_apply]
    simp [bordered, czMatrix]

/-- For a pure `y` whose coordinate vector `p` has `p ⬝ᵥ p ≠ 0`, the nullity of `y`, the rank of
`C_y` and `2` add to `2 ^ k`: `ker L_y` is `ker C_y ⊓ p^⊥`, one dimension below `ker C_y`. -/
theorem nullity_add_rank_add_two {y : Tower K k} (hy : (basis K k).repr y 0#k = 0)
    (hyy : (fun c : NonzeroIndex k => (basis K k).repr y c.1) ⬝ᵥ
      (fun c : NonzeroIndex k => (basis K k).repr y c.1) ≠ 0) :
    nullity K k y + (czMatrix y).rank + 2 = 2 ^ k := by
  have hB := mulLeft_matrix_bordered hy
  have hcard : Fintype.card (NonzeroIndex k) + 1 = 2 ^ k := by
    have h := Fintype.card_congr (borderEquiv k)
    rw [Fintype.card_sum, Fintype.card_unit] at h
    have h2 : Fintype.card (BitVec k) = 2 ^ k := by
      have := Module.finrank_eq_card_basis (basis K k)
      rw [finrank_eq] at this
      exact this.symm
    omega
  have h1 : (LinearMap.toMatrix (basis K k) (basis K k) (mulLeft K k y)).rank + nullity K k y =
      2 ^ k := by
    rw [Matrix.rank_eq_finrank_range_toLin _ (basis K k) (basis K k), Matrix.toLin_toMatrix]
    have := LinearMap.finrank_range_add_finrank_ker (mulLeft K k y)
    rw [finrank_eq] at this
    exact this
  have h2 : (Matrix.bordered (czMatrix y) (fun c : NonzeroIndex k => (basis K k).repr y c.1)).rank =
      (LinearMap.toMatrix (basis K k) (basis K k) (mulLeft K k y)).rank := by
    rw [← hB]
    exact Matrix.rank_submatrix _ _ _
  have h3 := Matrix.rank_add_finrank_ker_toLin'
    (Matrix.bordered (czMatrix y) (fun c : NonzeroIndex k => (basis K k).repr y c.1))
  have h4 := Matrix.finrank_ker_bordered_add_one (czMatrix y)
    (fun c : NonzeroIndex k => (basis K k).repr y c.1)
    (fun c : NonzeroIndex k => (basis K k).repr y c.1) (czMatrix_transpose hy)
    (czMatrix_mulVec_repr hy) hyy
  have h5 := Matrix.rank_add_finrank_ker_toLin' (czMatrix y)
  have h6 : Fintype.card (Unit ⊕ NonzeroIndex k) = Fintype.card (NonzeroIndex k) + 1 := by
    simp [Fintype.card_sum, add_comm]
  omega

/-- Over an ordered field the hypothesis `p ⬝ᵥ p ≠ 0` holds for every nonzero pure `y`. -/
theorem nullity_add_rank_add_two_of_ne_zero [LinearOrder K] [IsStrictOrderedRing K]
    {y : Tower K k} (hy : (basis K k).repr y 0#k = 0) (hne : y ≠ 0) :
    nullity K k y + (czMatrix y).rank + 2 = 2 ^ k := by
  refine nullity_add_rank_add_two hy ?_
  intro h
  rw [dotProduct_self_eq_zero] at h
  apply hne
  refine (basis K k).ext_elem fun i => ?_
  by_cases hi : i = 0#k
  · rw [hi, hy]; simp
  · simpa using congrFun h ⟨i, hi⟩

/-- At level `5` the nullity of a pure `y` with `p ⬝ᵥ p ≠ 0` is `30 - rank C_y`. -/
theorem nullity_add_rank_level_five {y : Tower K 5} (hy : (basis K 5).repr y 0#5 = 0)
    (hyy : (fun c : NonzeroIndex 5 => (basis K 5).repr y c.1) ⬝ᵥ
      (fun c : NonzeroIndex 5 => (basis K 5).repr y c.1) ≠ 0) :
    nullity K 5 y + (czMatrix y).rank = 30 := by
  have := nullity_add_rank_add_two hy hyy
  omega

end Tower

end CayleyDickson
