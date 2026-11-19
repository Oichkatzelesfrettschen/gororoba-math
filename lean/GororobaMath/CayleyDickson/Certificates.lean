/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Certificates of left inverses and of splittings

Convention: matrices are `Mathlib.Matrix` over a commutative ring `S`, `M *ᵥ x` is the product
of `M` with a column vector, and `d • 1` is `d` times the identity matrix. A matrix `M`
with a left inverse up to the scalar `d` (`L * M = d • 1`) has independent columns whenever `d`
is left regular, and a splitting `P * M + V * C = d • 1` expresses `d` times every kernel vector
of `M` through `V`.

## Main results

* `Matrix.linearIndependent_cols_of_mul_eq_smul_one`: the Rocq original is `columns_independent`
  of the module `LeftInverseCertificate` in `rocq/quantum/MatrixLeftInverseCertificate.v`. The
  transport of the certificate from its source ring to the target ring is the base-change step
  of `rocq/quantum/CdTowerRingBaseChange.v`; Lean states the target-ring lemma.
* `Matrix.smul_eq_mulVec_of_splitting`: the Rocq original is `solutions_spanned` of the module
  `SplittingCertificate` in `rocq/quantum/MatrixSplittingCertificate.v`.
-/

@[expose] public section

namespace Matrix

variable {S : Type*} [CommRing S] {m n : Type*} [Fintype m] [DecidableEq n]

/-- From `L * M = d • 1` with `d` left regular, the columns of `M` are linearly independent
(the rows of `Mᵀ`). The Rocq original is `columns_independent` of the module
`LeftInverseCertificate` in `rocq/quantum/MatrixLeftInverseCertificate.v`. -/
theorem linearIndependent_cols_of_mul_eq_smul_one [Finite n] (M : Matrix m n S)
    (L : Matrix n m S) (d : S) (hd : IsLeftRegular d) (h : L * M = d • (1 : Matrix n n S)) :
    LinearIndependent S (fun j : n => Mᵀ j) := by
  cases nonempty_fintype n
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hM : M *ᵥ g = 0 := by
    rw [← hg]
    ext j
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have hLM : d • g = 0 := by
    have := congrArg (fun v => L *ᵥ v) hM
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_zero, h, Matrix.smul_mulVec, Matrix.one_mulVec] at this
    exact this
  intro i
  have hi := congrFun hLM i
  exact hd (by simpa using hi)

/-- From `P * M + V * C = d • 1`, every solution `x` of `M *ᵥ x = 0` satisfies
`d • x = V *ᵥ (C *ᵥ x)`. The Rocq original is `solutions_spanned` of the module
`SplittingCertificate` in `rocq/quantum/MatrixSplittingCertificate.v`. -/
theorem smul_eq_mulVec_of_splitting [Fintype n] {t : Type*} [Fintype t] (M : Matrix m n S)
    (P : Matrix n m S) (V : Matrix n t S) (C : Matrix t n S) (d : S)
    (h : P * M + V * C = d • (1 : Matrix n n S)) (x : n → S) (hx : M *ᵥ x = 0) :
    d • x = V *ᵥ (C *ᵥ x) := by
  have := congrArg (fun A => A *ᵥ x) h
  simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, zero_add,
    Matrix.smul_mulVec, Matrix.one_mulVec] at this
  exact this.symm

end Matrix
