/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.Clifford.ZeroEight
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The Gram operator of an anticommuting pair of skew complex units

Convention. A matrix is a function of its row and column (`Matrix n n R`), the product is the
matrix product, `Aᵀ` is the transpose, and `ι : R` is a fixed element of a commutative ring with
`ι * ι = -1`. The Hermitian adjoint of `A + ι • B` is read in two ways: directly as
`Aᵀ - ι • Bᵀ` over any commutative ring (`gram_eq`), and as `conjTranspose` over a commutative
ring with a star that sends `ι` to `-ι` and fixes the entries of `A` and `B`
(`conjTranspose_mul_self_eq`). The matrices are the left multiplications of two imaginary
units of a Cayley-Dickson algebra whose left tables are skew (`L_aᵀ = -L_a`), square to `-1`
and anticommute; the Gram identity and the kernel characterization below are the first part of
the gororoba-quantum findings ledger row A5-629.

The kernel statement needs only `A * A = -1`: both inclusions are one multiplication by `A`, so
neither a field nor an invertible `2` enters.

The instance fixes the sedenion units `e_1 .. e_8` of `Clifford.ZeroEight`. Row A5-629 states
further, and this file leaves unproved: that `ι • (A * B)` is a traceless Hermitian involution
and that the kernel has half the dimension; the complement law
`nullity (e_a + ι e_b) = D/2 - nullity (e_a + e_b)` for every two-term operand; the `A_5` slice
kernel `ker K_1 ∩ ker (i L_1 J - I)` with the Gram multiplicities of 0, 2 and 4; and the other
anticommuting pairs (63, 171 and 435 at dimensions 16, 32 and 64).

## Main results

* `Clifford.AnticommutingPair.gram_eq`: `(Aᵀ - ι • Bᵀ) * (A + ι • B) = 2 • (1 - ι • (A * B))`.
* `Clifford.AnticommutingPair.conjTranspose_mul_self_eq`: the same with `conjTranspose`.
* `Clifford.AnticommutingPair.mulVec_eq_zero_iff`: `(A + ι • B) *ᵥ v = 0` exactly when
  `(ι • (A * B)) *ᵥ v = v`.
* `Clifford.AnticommutingPair.genMat_gram`, `Clifford.AnticommutingPair.genMat_mulVec_eq_zero_iff`:
  the Gram identity for the units `e_(i + 1)`, `e_(j + 1)`, `i ≠ j`, of the sedenions, and the
  kernel characterization for all `i`, `j`.
-/

@[expose] public section

namespace Clifford.AnticommutingPair

open Matrix

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The Gram operator of `A + ι B` is `2 (1 - ι A B)` for skew anticommuting `A`, `B` of square
`-1`: the four-term expansion has the same-factor terms `-A² + ι² B²` and the cross terms
`-ι A B + ι B A`. -/
theorem gram_eq (A B : Matrix n n R) (ι : R) (hι : ι * ι = -1)
    (hAt : Aᵀ = -A) (hBt : Bᵀ = -B) (hAA : A * A = -1) (hBB : B * B = -1)
    (hAB : A * B = -(B * A)) :
    (Aᵀ - ι • Bᵀ) * (A + ι • B) = (2 : R) • (1 - ι • (A * B)) := by
  have hBA : B * A = -(A * B) := by rw [hAB, neg_neg]
  have h : (Aᵀ - ι • Bᵀ) * (A + ι • B) =
      -(A * A) - ι • (A * B) + ι • (B * A) + (ι * ι) • (B * B) := by
    rw [hAt, hBt]
    simp only [sub_mul, mul_add, neg_mul, smul_mul_assoc, mul_smul_comm, smul_neg]
    module
  rw [h, hAA, hBB, hBA, hι]
  module

/-- The Gram identity with the Hermitian adjoint of a ring with a star that conjugates `ι` and
fixes the entries of `A` and `B`: the adjoint equals `Aᵀ - ι • Bᵀ`, which is `gram_eq`. -/
theorem conjTranspose_mul_self_eq [StarRing R] (A B : Matrix n n R) (ι : R) (hι : ι * ι = -1)
    (hstar : star ι = -ι) (hAs : A.map star = A) (hBs : B.map star = B)
    (hAt : Aᵀ = -A) (hBt : Bᵀ = -B) (hAA : A * A = -1) (hBB : B * B = -1)
    (hAB : A * B = -(B * A)) :
    (A + ι • B)ᴴ * (A + ι • B) = (2 : R) • (1 - ι • (A * B)) := by
  have hc : ∀ M : Matrix n n R, M.map star = M → Mᴴ = Mᵀ := fun M hM => by
    ext j k
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply]
    exact congrFun (congrFun hM k) j
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hc A hAs, hc B hBs, hstar, neg_smul,
    ← sub_eq_add_neg]
  exact gram_eq A B ι hι hAt hBt hAA hBB hAB

/-- The kernel of `A + ι B` is the fixed space of `ι A B` whenever `A² = -1`: multiplying by `A`
sends `(A + ι B) v = 0` to `ι A B v = v`, and `A` inverts that step. -/
theorem mulVec_eq_zero_iff (A B : Matrix n n R) (ι : R) (hAA : A * A = -1) (v : n → R) :
    (A + ι • B) *ᵥ v = 0 ↔ (ι • (A * B)) *ᵥ v = v := by
  have hL : A * (A + ι • B) = -1 + ι • (A * B) := by
    rw [mul_add, mul_smul_comm, hAA]
  have hM : A * (ι • (A * B)) = -(ι • B) := by
    rw [mul_smul_comm, ← Matrix.mul_assoc, hAA, neg_mul, Matrix.one_mul, smul_neg]
  constructor
  · intro h
    have h2 : (A * (A + ι • B)) *ᵥ v = 0 := by
      rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
    rw [hL, Matrix.add_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec] at h2
    exact (neg_add_eq_zero.mp h2).symm
  · intro h
    have h2 : A *ᵥ v = -((ι • B) *ᵥ v) := by
      conv_lhs => rw [← h]
      rw [Matrix.mulVec_mulVec, hM, Matrix.neg_mulVec]
    rw [Matrix.add_mulVec, h2, neg_add_cancel]

open ZeroEight in
/-- The matrix of left multiplication by `e_(i + 1)` of the sedenions, over `R`. -/
def genMatR (R : Type*) [CommRing R] (i : Fin 8) : Matrix (Fin 16) (Fin 16) R :=
  (Int.castRingHom R).mapMatrix (genMat i)

open ZeroEight in
/-- Each of the eight integer tables is skew: 8 tables of 256 entries, one `decide +kernel`
(the whole module builds in 3.2 s, Lean 4.35.0). -/
theorem genMat_transpose : ∀ i : Fin 8, (genMat i)ᵀ = -genMat i := by decide +kernel

open ZeroEight in
/-- Each table of the units `e_(k + 1)` squares to `-1`: the integer identity `genMat_sq` maps
through the ring homomorphism `ℤ → R`. -/
theorem genMatR_sq (k : Fin 8) : genMatR R k * genMatR R k = -1 := by
  simp only [genMatR, ← map_mul, genMat_sq k, map_neg, map_one]

open ZeroEight in
/-- The Gram operator of the sedenion unit pair `e_(i + 1) + ι e_(j + 1)`, `i ≠ j`: `gram_eq` with
skew tables, squares `-1` and the anticommutation `genMat_anti`. -/
theorem genMat_gram (ι : R) (hι : ι * ι = -1) {i j : Fin 8} (h : i ≠ j) :
    ((genMatR R i)ᵀ - ι • (genMatR R j)ᵀ) * (genMatR R i + ι • genMatR R j) =
      (2 : R) • (1 - ι • (genMatR R i * genMatR R j)) := by
  have hsk : ∀ k : Fin 8, (genMatR R k)ᵀ = -genMatR R k := fun k => by
    ext a b
    have hk := congrFun (congrFun (genMat_transpose k) a) b
    simp only [genMatR, RingHom.mapMatrix_apply, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.neg_apply] at hk ⊢
    rw [hk, map_neg]
  refine gram_eq _ _ ι hι (hsk i) (hsk j) (genMatR_sq i) (genMatR_sq j) ?_
  have hanti := eq_neg_of_add_eq_zero_left (genMat_anti i j h)
  simp only [genMatR, ← map_mul]
  rw [hanti, map_neg]

/-- The kernel of `e_(i + 1) + ι e_(j + 1)` on the coordinates of the sedenions is the fixed
space of `ι L_i L_j`, for all `i`, `j`: `mulVec_eq_zero_iff` needs only `L_i² = -1`. -/
theorem genMat_mulVec_eq_zero_iff (ι : R) (i j : Fin 8) (v : Fin 16 → R) :
    (genMatR R i + ι • genMatR R j) *ᵥ v = 0 ↔
      (ι • (genMatR R i * genMatR R j)) *ᵥ v = v :=
  mulVec_eq_zero_iff _ _ ι (genMatR_sq i) v

end Clifford.AnticommutingPair
