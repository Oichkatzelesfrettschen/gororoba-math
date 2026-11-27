/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.TensorProduct.Matrix
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Data.Matrix.Block

/-!
# Rank of block-diagonal and Kronecker-product matrices

Notice of modification (Apache-2.0 section 4(b)): `rank_fromBlocks_diagonal` and
`rank_kronecker` are adapted from `lean/OAI/LinearAlgebra/SpectralBooks/BlockDiagRank.lean` and
`KroneckerRank.lean` of https://github.com/openai/math (Apache-2.0) at commit 3344da599. This file
modifies them for Lean 4.35.0 and Mathlib v4.35.0: both declarations sit in `namespace Matrix`, and
`rank_kronecker` takes `Finite` in place of `Fintype` on its row types `m` and `p`;
`rank_fromBlocks_diagonal` keeps the upstream hypotheses. Date of the change: 2026-11-26.

Convention: a matrix `A : Matrix m n K` over a field `K` has `Matrix.rank A` the dimension of the
range of `A.mulVecLin`, with rows indexed by `m` and columns by `n`. `Matrix.fromBlocks A 0 0 B`
is block diagonal over the index types `m ⊕ m'` and `n ⊕ n'`; `Matrix.blockDiagonal' M` places a
family `M k : Matrix (m' k) (n' k) K` on the diagonal of `Σ k, m' k` by `Σ k, n' k`; the
Kronecker product `A ⊗ₖ B` has entry `A i j * B k l` at `(i, k)` and `(j, l)`. A grading of the rows
and columns by a finite type `ι` is a pair of maps `c : m → ι` and `d : n → ι`, and the `s`-block of
`A` is the submatrix on the rows of `c ⁻¹' {s}` and the columns of `d ⁻¹' {s}`.

## Main results

* `Matrix.rank_fromBlocks_diagonal`: `rank (fromBlocks A 0 0 B) = rank A + rank B`.
* `Matrix.finrank_range_piMap`: the range of a product of linear maps has dimension the sum of the
  dimensions of the component ranges.
* `Matrix.rank_blockDiagonal'`: the rank of `blockDiagonal' M` is the sum of the ranks of the `M k`.
* `Matrix.rank_kronecker`: `rank (A ⊗ₖ B) = rank A * rank B`.
* `Matrix.rank_eq_sum_rank_gradedBlock`: if the entries of `A` vanish between rows and columns of
  different values of the grading, the rank of `A` is the sum of the ranks of its blocks.
-/

@[expose] public section

namespace Matrix

open scoped Kronecker

variable {K : Type*} [Field K]

/-- The rank of a rectangular block diagonal matrix is the sum of its block ranks, through the
direct-sum decomposition of the range of `mulVecLin`. -/
theorem rank_fromBlocks_diagonal {I J I' J' : Type*} [Fintype J] [Fintype J']
    (A : Matrix I J K) (B : Matrix I' J' K) :
    (Matrix.fromBlocks A 0 0 B).rank = A.rank + B.rank := by
  let e := LinearEquiv.sumArrowLequivProdArrow I I' K K
  let d := LinearEquiv.sumArrowLequivProdArrow J J' K K
  have h : (Matrix.fromBlocks A 0 0 B).mulVecLin =
      e.symm.toLinearMap ∘ₗ (A.mulVecLin.prodMap B.mulVecLin) ∘ₗ d.toLinearMap := by
    apply LinearMap.ext
    intro x
    ext (i | i)
    · simp only [mulVecBilin_apply, fromBlocks_mulVec, zero_mulVec, add_zero, Sum.elim_inl,
        LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.prodMap_apply,
        LinearEquiv.sumArrowLequivProdArrow_symm_apply_inl, e, d]
      rfl
    · simp only [mulVecBilin_apply, fromBlocks_mulVec, zero_mulVec, zero_add, Sum.elim_inr,
        LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.prodMap_apply,
        LinearEquiv.sumArrowLequivProdArrow_symm_apply_inr, e, d]
      rfl
  rw [Matrix.rank, h, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top, LinearEquiv.finrank_map_eq, LinearMap.range_prodMap,
    (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]
  rfl

/-- The range of `piMap f` is the product of the ranges of the `f k`, which embeds into the target
with the dimension of a finite product. -/
theorem finrank_range_piMap {κ : Type*} [Fintype κ] {φ ψ : κ → Type*}
    [∀ k, AddCommGroup (φ k)] [∀ k, Module K (φ k)]
    [∀ k, AddCommGroup (ψ k)] [∀ k, Module K (ψ k)]
    [∀ k, Module.Finite K (φ k)]
    (f : ∀ k, φ k →ₗ[K] ψ k) :
    Module.finrank K (LinearMap.range (LinearMap.piMap f)) =
      ∑ k, Module.finrank K (LinearMap.range (f k)) := by
  classical
  let g : (∀ k, LinearMap.range (f k)) →ₗ[K] ∀ k, ψ k :=
    LinearMap.piMap fun k => (LinearMap.range (f k)).subtype
  have hinj : Function.Injective g := fun x y hxy =>
    funext fun k => Subtype.ext (congrFun hxy k)
  have hrange : LinearMap.range (LinearMap.piMap f) = LinearMap.range g := by
    apply SetLike.ext'
    simp only [LinearMap.coe_range, LinearMap.coe_piMap, g, Set.range_piMap]
    ext x
    simp [Set.mem_pi]
  rw [hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi_fintype]

/-- Curry-uncurry equivalences turn `blockDiagonal' M` into `piMap` of the `mulVecLin`, whose range
dimension is the sum of the block ranks. -/
theorem rank_blockDiagonal' {κ : Type*} [Fintype κ] [DecidableEq κ] {m' n' : κ → Type*}
    [∀ k, Fintype (n' k)] (M : ∀ k, Matrix (m' k) (n' k) K) :
    (Matrix.blockDiagonal' M).rank = ∑ k, (M k).rank := by
  let e := LinearEquiv.piCurry K (fun k (_ : m' k) => K)
  let d := LinearEquiv.piCurry K (fun k (_ : n' k) => K)
  have h : (Matrix.blockDiagonal' M).mulVecLin =
      e.symm.toLinearMap ∘ₗ (LinearMap.piMap fun k => (M k).mulVecLin) ∘ₗ d.toLinearMap := by
    apply LinearMap.ext
    intro x
    ext ⟨k, i⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, LinearMap.comp_apply,
      LinearEquiv.coe_coe, Fintype.sum_sigma, Matrix.blockDiagonal'_apply]
    refine (Finset.sum_eq_single k ?_ ?_).trans ?_
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
    · simp only [cast_eq]
      rfl
  rw [Matrix.rank, h, LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range,
    Submodule.map_top, LinearEquiv.finrank_map_eq, finrank_range_piMap]
  rfl

/-- The Kronecker product acts as the tensor product of the two maps, whose range is flat-injected
into the tensor product of the ranges. -/
theorem rank_kronecker {m n p q : Type*}
    [Finite m] [Fintype n] [Finite p] [Fintype q]
    (A : Matrix m n K) (B : Matrix p q K) :
    (A ⊗ₖ B).rank = A.rank * B.rank := by
  classical
  let bm := Pi.basisFun K m
  let bn := Pi.basisFun K n
  let bp := Pi.basisFun K p
  let bq := Pi.basisFun K q
  rw [(A ⊗ₖ B).rank_eq_finrank_range_toLin (bm.tensorProduct bp) (bn.tensorProduct bq),
    Matrix.toLin_kronecker, A.rank_eq_finrank_range_toLin bm bn,
    B.rank_eq_finrank_range_toLin bp bq, TensorProduct.range_map, ← TensorProduct.range_mapIncl,
    LinearMap.finrank_range_of_inj (Module.Flat.tensorProduct_mapIncl_injective_of_right _ _),
    Module.finrank_tensorProduct]

/-- Reindexing rows and columns by the fibers of the grading makes the matrix block diagonal, so
`rank_blockDiagonal'` applies. -/
theorem rank_eq_sum_rank_gradedBlock {ι m n : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype n] (c : m → ι) (d : n → ι) (A : Matrix m n K)
    (h : ∀ i j, c i ≠ d j → A i j = 0) :
    A.rank = ∑ s : ι, (A.submatrix (fun i : { i // c i = s } => i.1)
      (fun j : { j // d j = s } => j.1)).rank := by
  rw [← Matrix.rank_reindex (Equiv.sigmaFiberEquiv c).symm (Equiv.sigmaFiberEquiv d).symm A,
    ← Matrix.rank_blockDiagonal']
  congr 1
  ext ⟨s, i⟩ ⟨t, j⟩
  by_cases hst : s = t
  · subst hst
    simp [Matrix.blockDiagonal'_apply_eq, Matrix.reindex_apply, Equiv.sigmaFiberEquiv]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hst]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      Equiv.sigmaFiberEquiv_apply]
    refine h _ _ ?_
    rw [i.2, j.2]
    exact hst

end Matrix
