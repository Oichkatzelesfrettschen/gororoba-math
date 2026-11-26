/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.LinearAlgebra.PfaffianSchurBlock
public import Mathlib.Algebra.MvPolynomial.Basic

/-!
# The bordered sixteen-by-sixteen Pfaffian identity over every commutative ring

Convention: as in `GororobaMath.LinearAlgebra.PfaffianSixteen`, `borderedA z t` is the level-4 left
multiplication by a pure element bordered by `t`, read on the indices `0, ..., 15`, and
`rhsv z t = -(z.t) Q G`. `A16 z t` is that matrix on `Fin 16`. The indices split into
`F = 0, ..., 7` and `S = 8, ..., 15`: `Bm` is the block on `S` (right multiplication by `u`),
`Xm` the block from `S` to `F` and `Dm` the block on `F`, each on `Fin 8` with `S` shifted by
`8`; `e16` sends `Sum.inl i` to `8 + i` and `Sum.inr j` to `j`.

The proof clears `Bm` in the Schur law (`Matrix.schur_cleared_of_mul`) with `c = U` and
`M = -(Bm Xm)`, since `Bm Bm = -U`: `U ^ 8 Pf A = Pf Bm * U ^ 4 * Pf S'` with `Pf Bm = U ^ 2` and
`Pf S' = -U ^ 2 (z.t) Q G` from the Pfaffian adjugate of the Schur block
(`PfaffianSchurBlock.adjPf_schurN`). Over the integer polynomial ring `U ^ 8` cancels, and
evaluation carries the identity to every commutative ring.

## Main results

* `PfaffianSixteenSchur.pow_mul_pfaffian`: `U ^ 8 Pf A = U ^ 8 * rhsv z t` when `2` is
  left-regular.
* `PfaffianSixteenSchur.pfaffian_sixteen`: `Pf A(z, t) = -(z.t) Q G` over every commutative ring.
-/

@[expose] public section

namespace PfaffianSixteenSchur

open PfaffianCross PfaffianSixteen PfaffianSchur PfaffianSchurBlock

open scoped Matrix

attribute [local simp]
  PfaffianSchurBlock.sedSign_1_1 PfaffianSchurBlock.sedSign_1_2 PfaffianSchurBlock.sedSign_1_3
  PfaffianSchurBlock.sedSign_1_4 PfaffianSchurBlock.sedSign_1_5 PfaffianSchurBlock.sedSign_1_6
  PfaffianSchurBlock.sedSign_1_7 PfaffianSchurBlock.sedSign_1_8 PfaffianSchurBlock.sedSign_1_9
  PfaffianSchurBlock.sedSign_1_10 PfaffianSchurBlock.sedSign_1_11 PfaffianSchurBlock.sedSign_1_12
  PfaffianSchurBlock.sedSign_1_13 PfaffianSchurBlock.sedSign_1_14 PfaffianSchurBlock.sedSign_1_15
  PfaffianSchurBlock.sedSign_2_1 PfaffianSchurBlock.sedSign_2_2 PfaffianSchurBlock.sedSign_2_3
  PfaffianSchurBlock.sedSign_2_4 PfaffianSchurBlock.sedSign_2_5 PfaffianSchurBlock.sedSign_2_6
  PfaffianSchurBlock.sedSign_2_7 PfaffianSchurBlock.sedSign_2_8 PfaffianSchurBlock.sedSign_2_9
  PfaffianSchurBlock.sedSign_2_10 PfaffianSchurBlock.sedSign_2_11 PfaffianSchurBlock.sedSign_2_12
  PfaffianSchurBlock.sedSign_2_13 PfaffianSchurBlock.sedSign_2_14 PfaffianSchurBlock.sedSign_2_15
  PfaffianSchurBlock.sedSign_3_1 PfaffianSchurBlock.sedSign_3_2 PfaffianSchurBlock.sedSign_3_3
  PfaffianSchurBlock.sedSign_3_4 PfaffianSchurBlock.sedSign_3_5 PfaffianSchurBlock.sedSign_3_6
  PfaffianSchurBlock.sedSign_3_7 PfaffianSchurBlock.sedSign_3_8 PfaffianSchurBlock.sedSign_3_9
  PfaffianSchurBlock.sedSign_3_10 PfaffianSchurBlock.sedSign_3_11 PfaffianSchurBlock.sedSign_3_12
  PfaffianSchurBlock.sedSign_3_13 PfaffianSchurBlock.sedSign_3_14 PfaffianSchurBlock.sedSign_3_15
  PfaffianSchurBlock.sedSign_4_1 PfaffianSchurBlock.sedSign_4_2 PfaffianSchurBlock.sedSign_4_3
  PfaffianSchurBlock.sedSign_4_4 PfaffianSchurBlock.sedSign_4_5 PfaffianSchurBlock.sedSign_4_6
  PfaffianSchurBlock.sedSign_4_7 PfaffianSchurBlock.sedSign_4_8 PfaffianSchurBlock.sedSign_4_9
  PfaffianSchurBlock.sedSign_4_10 PfaffianSchurBlock.sedSign_4_11 PfaffianSchurBlock.sedSign_4_12
  PfaffianSchurBlock.sedSign_4_13 PfaffianSchurBlock.sedSign_4_14 PfaffianSchurBlock.sedSign_4_15
  PfaffianSchurBlock.sedSign_5_1 PfaffianSchurBlock.sedSign_5_2 PfaffianSchurBlock.sedSign_5_3
  PfaffianSchurBlock.sedSign_5_4 PfaffianSchurBlock.sedSign_5_5 PfaffianSchurBlock.sedSign_5_6
  PfaffianSchurBlock.sedSign_5_7 PfaffianSchurBlock.sedSign_5_8 PfaffianSchurBlock.sedSign_5_9
  PfaffianSchurBlock.sedSign_5_10 PfaffianSchurBlock.sedSign_5_11 PfaffianSchurBlock.sedSign_5_12
  PfaffianSchurBlock.sedSign_5_13 PfaffianSchurBlock.sedSign_5_14 PfaffianSchurBlock.sedSign_5_15
  PfaffianSchurBlock.sedSign_6_1 PfaffianSchurBlock.sedSign_6_2 PfaffianSchurBlock.sedSign_6_3
  PfaffianSchurBlock.sedSign_6_4 PfaffianSchurBlock.sedSign_6_5 PfaffianSchurBlock.sedSign_6_6
  PfaffianSchurBlock.sedSign_6_7 PfaffianSchurBlock.sedSign_6_8 PfaffianSchurBlock.sedSign_6_9
  PfaffianSchurBlock.sedSign_6_10 PfaffianSchurBlock.sedSign_6_11 PfaffianSchurBlock.sedSign_6_12
  PfaffianSchurBlock.sedSign_6_13 PfaffianSchurBlock.sedSign_6_14 PfaffianSchurBlock.sedSign_6_15
  PfaffianSchurBlock.sedSign_7_1 PfaffianSchurBlock.sedSign_7_2 PfaffianSchurBlock.sedSign_7_3
  PfaffianSchurBlock.sedSign_7_4 PfaffianSchurBlock.sedSign_7_5 PfaffianSchurBlock.sedSign_7_6
  PfaffianSchurBlock.sedSign_7_7 PfaffianSchurBlock.sedSign_7_8 PfaffianSchurBlock.sedSign_7_9
  PfaffianSchurBlock.sedSign_7_10 PfaffianSchurBlock.sedSign_7_11 PfaffianSchurBlock.sedSign_7_12
  PfaffianSchurBlock.sedSign_7_13 PfaffianSchurBlock.sedSign_7_14 PfaffianSchurBlock.sedSign_7_15
  PfaffianSchurBlock.sedSign_8_1 PfaffianSchurBlock.sedSign_8_2 PfaffianSchurBlock.sedSign_8_3
  PfaffianSchurBlock.sedSign_8_4 PfaffianSchurBlock.sedSign_8_5 PfaffianSchurBlock.sedSign_8_6
  PfaffianSchurBlock.sedSign_8_7 PfaffianSchurBlock.sedSign_8_8 PfaffianSchurBlock.sedSign_8_9
  PfaffianSchurBlock.sedSign_8_10 PfaffianSchurBlock.sedSign_8_11 PfaffianSchurBlock.sedSign_8_12
  PfaffianSchurBlock.sedSign_8_13 PfaffianSchurBlock.sedSign_8_14 PfaffianSchurBlock.sedSign_8_15
  PfaffianSchurBlock.sedSign_9_1 PfaffianSchurBlock.sedSign_9_2 PfaffianSchurBlock.sedSign_9_3
  PfaffianSchurBlock.sedSign_9_4 PfaffianSchurBlock.sedSign_9_5 PfaffianSchurBlock.sedSign_9_6
  PfaffianSchurBlock.sedSign_9_7 PfaffianSchurBlock.sedSign_9_8 PfaffianSchurBlock.sedSign_9_9
  PfaffianSchurBlock.sedSign_9_10 PfaffianSchurBlock.sedSign_9_11 PfaffianSchurBlock.sedSign_9_12
  PfaffianSchurBlock.sedSign_9_13 PfaffianSchurBlock.sedSign_9_14 PfaffianSchurBlock.sedSign_9_15
  PfaffianSchurBlock.sedSign_10_1 PfaffianSchurBlock.sedSign_10_2 PfaffianSchurBlock.sedSign_10_3
  PfaffianSchurBlock.sedSign_10_4 PfaffianSchurBlock.sedSign_10_5 PfaffianSchurBlock.sedSign_10_6
  PfaffianSchurBlock.sedSign_10_7 PfaffianSchurBlock.sedSign_10_8 PfaffianSchurBlock.sedSign_10_9
  PfaffianSchurBlock.sedSign_10_10 PfaffianSchurBlock.sedSign_10_11 PfaffianSchurBlock.sedSign_10_12
  PfaffianSchurBlock.sedSign_10_13 PfaffianSchurBlock.sedSign_10_14 PfaffianSchurBlock.sedSign_10_15
  PfaffianSchurBlock.sedSign_11_1 PfaffianSchurBlock.sedSign_11_2 PfaffianSchurBlock.sedSign_11_3
  PfaffianSchurBlock.sedSign_11_4 PfaffianSchurBlock.sedSign_11_5 PfaffianSchurBlock.sedSign_11_6
  PfaffianSchurBlock.sedSign_11_7 PfaffianSchurBlock.sedSign_11_8 PfaffianSchurBlock.sedSign_11_9
  PfaffianSchurBlock.sedSign_11_10 PfaffianSchurBlock.sedSign_11_11 PfaffianSchurBlock.sedSign_11_12
  PfaffianSchurBlock.sedSign_11_13 PfaffianSchurBlock.sedSign_11_14 PfaffianSchurBlock.sedSign_11_15
  PfaffianSchurBlock.sedSign_12_1 PfaffianSchurBlock.sedSign_12_2 PfaffianSchurBlock.sedSign_12_3
  PfaffianSchurBlock.sedSign_12_4 PfaffianSchurBlock.sedSign_12_5 PfaffianSchurBlock.sedSign_12_6
  PfaffianSchurBlock.sedSign_12_7 PfaffianSchurBlock.sedSign_12_8 PfaffianSchurBlock.sedSign_12_9
  PfaffianSchurBlock.sedSign_12_10 PfaffianSchurBlock.sedSign_12_11 PfaffianSchurBlock.sedSign_12_12
  PfaffianSchurBlock.sedSign_12_13 PfaffianSchurBlock.sedSign_12_14 PfaffianSchurBlock.sedSign_12_15
  PfaffianSchurBlock.sedSign_13_1 PfaffianSchurBlock.sedSign_13_2 PfaffianSchurBlock.sedSign_13_3
  PfaffianSchurBlock.sedSign_13_4 PfaffianSchurBlock.sedSign_13_5 PfaffianSchurBlock.sedSign_13_6
  PfaffianSchurBlock.sedSign_13_7 PfaffianSchurBlock.sedSign_13_8 PfaffianSchurBlock.sedSign_13_9
  PfaffianSchurBlock.sedSign_13_10 PfaffianSchurBlock.sedSign_13_11 PfaffianSchurBlock.sedSign_13_12
  PfaffianSchurBlock.sedSign_13_13 PfaffianSchurBlock.sedSign_13_14 PfaffianSchurBlock.sedSign_13_15
  PfaffianSchurBlock.sedSign_14_1 PfaffianSchurBlock.sedSign_14_2 PfaffianSchurBlock.sedSign_14_3
  PfaffianSchurBlock.sedSign_14_4 PfaffianSchurBlock.sedSign_14_5 PfaffianSchurBlock.sedSign_14_6
  PfaffianSchurBlock.sedSign_14_7 PfaffianSchurBlock.sedSign_14_8 PfaffianSchurBlock.sedSign_14_9
  PfaffianSchurBlock.sedSign_14_10 PfaffianSchurBlock.sedSign_14_11 PfaffianSchurBlock.sedSign_14_12
  PfaffianSchurBlock.sedSign_14_13 PfaffianSchurBlock.sedSign_14_14 PfaffianSchurBlock.sedSign_14_15
  PfaffianSchurBlock.sedSign_15_1 PfaffianSchurBlock.sedSign_15_2 PfaffianSchurBlock.sedSign_15_3
  PfaffianSchurBlock.sedSign_15_4 PfaffianSchurBlock.sedSign_15_5 PfaffianSchurBlock.sedSign_15_6
  PfaffianSchurBlock.sedSign_15_7 PfaffianSchurBlock.sedSign_15_8 PfaffianSchurBlock.sedSign_15_9
  PfaffianSchurBlock.sedSign_15_10 PfaffianSchurBlock.sedSign_15_11 PfaffianSchurBlock.sedSign_15_12
  PfaffianSchurBlock.sedSign_15_13 PfaffianSchurBlock.sedSign_15_14 PfaffianSchurBlock.sedSign_15_15

/-- The sedenion sign table is skew off the diagonal. -/
theorem sedSign_skew {a b : ℕ} (ha : 1 ≤ a) (ha16 : a < 16) (hb : 1 ≤ b) (hb16 : b < 16)
    (hab : a ≠ b) : sedSign a b = -sedSign b a := by
  interval_cases a <;> interval_cases b <;> first | exact absurd rfl hab | decide

variable {R : Type*} [CommRing R]

/-- The first row of the bordered matrix is `-t`. -/
theorem borderedA_zero_left (z t : ℕ → R) {b : ℕ} (hb : b ≠ 0) : borderedA z t 0 b = -t b := by
  simp [borderedA, Ne.symm hb]

/-- The first column of the bordered matrix is `t`. -/
theorem borderedA_zero_right (z t : ℕ → R) {a : ℕ} (ha : a ≠ 0) : borderedA z t a 0 = t a := by
  simp [borderedA, ha]

/-- The bordered matrix is skew on `0, ..., 15`. -/
theorem borderedA_skew (z t : ℕ → R) {a b : ℕ} (ha : a < 16) (hb : b < 16) :
    borderedA z t a b = -borderedA z t b a := by
  by_cases hab : a = b
  · subst hab
    simp [borderedA_self]
  by_cases ha0 : a = 0
  · subst ha0
    rw [borderedA_zero_left z t (Ne.symm hab), borderedA_zero_right z t (Ne.symm hab)]
  by_cases hb0 : b = 0
  · subst hb0
    rw [borderedA_zero_left z t ha0, borderedA_zero_right z t ha0, neg_neg]
  rw [borderedA_of_pos z t (by omega) ha (by omega) hb hab,
    borderedA_of_pos z t (by omega) hb (by omega) ha (Ne.symm hab),
    sedSign_skew (by omega) ha (by omega) hb hab, Nat.xor_comm b a]
  push_cast
  ring

/-- The bordered matrix on `Fin 16`. -/
def A16 (z t : ℕ → R) : Matrix (Fin 16) (Fin 16) R := Matrix.of fun a b => borderedA z t a b

/-- The block on `S = 8, ..., 15`. -/
def Bm (z t : ℕ → R) : Matrix (Fin 8) (Fin 8) R :=
  Matrix.of fun i j => borderedA z t (8 + (i : ℕ)) (8 + (j : ℕ))

/-- The block from `S` to `F = 0, ..., 7`. -/
def Xm (z t : ℕ → R) : Matrix (Fin 8) (Fin 8) R :=
  Matrix.of fun i j => borderedA z t (8 + (i : ℕ)) j

/-- The block on `F`. -/
def Dm (z t : ℕ → R) : Matrix (Fin 8) (Fin 8) R := Matrix.of fun i j => borderedA z t i j

/-- The index map of the block order: `S` first, then `F`. -/
def e16 : Fin 8 ⊕ Fin 8 → Fin 16 :=
  Sum.elim (fun i => ⟨8 + i, by have := i.isLt; omega⟩) (fun j => ⟨j, by have := j.isLt; omega⟩)

/-- The bordered matrix on `Fin 16` is skew. -/
theorem A16_skew (z t : ℕ → R) (a b : Fin 16) : A16 z t a b = -A16 z t b a := by
  simp only [A16, Matrix.of_apply]
  exact borderedA_skew z t a.isLt b.isLt

/-- The block on `S` is skew. -/
theorem Bm_transpose (z t : ℕ → R) : (Bm z t)ᵀ = -Bm z t := by
  ext i j
  simp only [Bm, Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply]
  exact borderedA_skew z t (by have := j.isLt; omega) (by have := i.isLt; omega)

/-- The block on `F` is skew. -/
theorem Dm_transpose (z t : ℕ → R) : (Dm z t)ᵀ = -Dm z t := by
  ext i j
  simp only [Dm, Matrix.transpose_apply, Matrix.neg_apply, Matrix.of_apply]
  exact borderedA_skew z t (by have := j.isLt; omega) (by have := i.isLt; omega)

/-- In the block order the bordered matrix is `[[Bm, Xm], [-Xmᵀ, Dm]]`. -/
theorem fromBlocks_eq (z t : ℕ → R) :
    Matrix.fromBlocks (Bm z t) (Xm z t) (-(Xm z t)ᵀ) (Dm z t) =
      fun a b => A16 z t (e16 a) (e16 b) := by
  funext a b
  rcases a with i | i <;> rcases b with j | j
  · rfl
  · rfl
  · simp only [Matrix.fromBlocks_apply₂₁, Matrix.neg_apply, Matrix.transpose_apply, Xm, A16, e16,
      Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    exact (borderedA_skew z t (by have := i.isLt; omega) (by have := j.isLt; omega)).symm
  · rfl

private theorem bb_0 (z t : ℕ → R) (j : Fin 8) :
    (Bm z t * Bm z t) 0 j = (-(uv z • (1 : Matrix (Fin 8) (Fin 8) R))) 0 j := by
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_eight, Bm, borderedA_self,
      borderedA_of_pos, uv, Finset.sum_range_succ] <;> ring

private theorem bb_1 (z t : ℕ → R) (j : Fin 8) :
    (Bm z t * Bm z t) 1 j = (-(uv z • (1 : Matrix (Fin 8) (Fin 8) R))) 1 j := by
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_eight, Bm, borderedA_self,
      borderedA_of_pos, uv, Finset.sum_range_succ] <;> ring

private theorem bb_2 (z t : ℕ → R) (j : Fin 8) :
    (Bm z t * Bm z t) 2 j = (-(uv z • (1 : Matrix (Fin 8) (Fin 8) R))) 2 j := by
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_eight, Bm, borderedA_self,
      borderedA_of_pos, uv, Finset.sum_range_succ] <;> ring

private theorem bb_3 (z t : ℕ → R) (j : Fin 8) :
    (Bm z t * Bm z t) 3 j = (-(uv z • (1 : Matrix (Fin 8) (Fin 8) R))) 3 j := by
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_eight, Bm, borderedA_self,
      borderedA_of_pos, uv, Finset.sum_range_succ] <;> ring

private theorem bb_4 (z t : ℕ → R) (j : Fin 8) :
    (Bm z t * Bm z t) 4 j = (-(uv z • (1 : Matrix (Fin 8) (Fin 8) R))) 4 j := by
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_eight, Bm, borderedA_self,
      borderedA_of_pos, uv, Finset.sum_range_succ] <;> ring

private theorem bb_5 (z t : ℕ → R) (j : Fin 8) :
    (Bm z t * Bm z t) 5 j = (-(uv z • (1 : Matrix (Fin 8) (Fin 8) R))) 5 j := by
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_eight, Bm, borderedA_self,
      borderedA_of_pos, uv, Finset.sum_range_succ] <;> ring

private theorem bb_6 (z t : ℕ → R) (j : Fin 8) :
    (Bm z t * Bm z t) 6 j = (-(uv z • (1 : Matrix (Fin 8) (Fin 8) R))) 6 j := by
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_eight, Bm, borderedA_self,
      borderedA_of_pos, uv, Finset.sum_range_succ] <;> ring

private theorem bb_7 (z t : ℕ → R) (j : Fin 8) :
    (Bm z t * Bm z t) 7 j = (-(uv z • (1 : Matrix (Fin 8) (Fin 8) R))) 7 j := by
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_eight, Bm, borderedA_self,
      borderedA_of_pos, uv, Finset.sum_range_succ] <;> ring

/-- The block on `S` squares to `-U`: right multiplication by a pure octonion. -/
theorem Bm_mul_self (z t : ℕ → R) : Bm z t * Bm z t = -(uv z • (1 : Matrix (Fin 8) (Fin 8) R)) := by
  ext i j
  fin_cases i
  · exact bb_0 z t j
  · exact bb_1 z t j
  · exact bb_2 z t j
  · exact bb_3 z t j
  · exact bb_4 z t j
  · exact bb_5 z t j
  · exact bb_6 z t j
  · exact bb_7 z t j

/-- The Pfaffian of the block on `S` is `U ^ 2`. -/
theorem pfaffian_Bm (z t : ℕ → R) : Matrix.pfaffian (Bm z t) = uv z ^ 2 := by
  have h := Matrix.pfaffianAux_reindex (borderedA z t) (fun i : Fin 8 => 8 + (i : ℕ)) 8
    (List.finRange 8) (by simp)
  have hl : (List.finRange 8).map (fun i : Fin 8 => 8 + (i : ℕ)) =
      [8, 9, 10, 11, 12, 13, 14, 15] := by decide
  unfold Matrix.pfaffian
  change Matrix.pfaffianAux (fun a b : Fin 8 => borderedA z t (8 + (a : ℕ)) (8 + (b : ℕ)))
    (List.finRange 8) = _
  rw [h, hl, Matrix.pfaffianAux_eight_indices]
  simp [Matrix.pfaffianAux_six_indices, borderedA_of_pos, uv, Finset.sum_range_succ]
  ring

/-- The cleared Schur complement `U Dm - Xmᵀ Bm Xm` is `schurN`. -/
theorem schurS_eq (z t : ℕ → R) (i j : Fin 8) :
    (uv z • Dm z t + (Xm z t)ᵀ * -(Bm z t * Xm z t)) i j = schurN z t i j := by
  simp [Matrix.mul_apply, Fin.sum_univ_eight, Finset.sum_range_succ, schurN, Dm, Xm, Bm]
  ring

/-- The Pfaffian of the cleared Schur complement is that of `schurN` on `0, ..., 7`. -/
theorem pfaffian_schurS (z t : ℕ → R) :
    Matrix.pfaffianAux (uv z • Dm z t + (Xm z t)ᵀ * -(Bm z t * Xm z t)) (List.finRange 8) =
      Matrix.pfaffianAux (schurN z t) [0, 1, 2, 3, 4, 5, 6, 7] := by
  rw [Matrix.pfaffianAux_congr _ (fun a b : Fin 8 => schurN z t a b) _ _ rfl
    (fun a _ b _ => schurS_eq z t a b),
    Matrix.pfaffianAux_reindex (schurN z t) (fun a : Fin 8 => (a : ℕ)) 8 _ (by simp)]
  exact congrArg _ (by decide)

private theorem row_1 (z t : ℕ → R) :
    schurN z t 0 1 =
      -z 1 ^ 2 * t 1 - z 2 ^ 2 * t 1 - z 3 ^ 2 * t 1 - z 4 ^ 2 * t 1 - z 5 ^ 2 * t 1 - z 6 ^ 2 * t 1
      - z 7 ^ 2 * t 1 - z 1 * z 8 * t 8 - z 2 * z 11 * t 8 + z 3 * z 10 * t 8 - z 4 * z 13 * t 8
      + z 5 * z 12 * t 8 + z 6 * z 15 * t 8 - z 7 * z 14 * t 8 - z 1 * z 9 * t 9 + z 3 * z 11 * t 9
      + z 2 * z 10 * t 9 + z 5 * z 13 * t 9 + z 4 * z 12 * t 9 + z 7 * z 15 * t 9 + z 6 * z 14 * t 9
      - z 2 * z 9 * t 10 - z 3 * z 8 * t 10 - z 1 * z 10 * t 10 + z 6 * z 13 * t 10
      - z 7 * z 12 * t 10 + z 4 * z 15 * t 10 - z 5 * z 14 * t 10 - z 3 * z 9 * t 11
      + z 2 * z 8 * t 11 - z 1 * z 11 * t 11 + z 7 * z 13 * t 11 + z 6 * z 12 * t 11
      - z 5 * z 15 * t 11 - z 4 * z 14 * t 11 - z 4 * z 9 * t 12 - z 5 * z 8 * t 12
      - z 6 * z 11 * t 12 + z 7 * z 10 * t 12 - z 1 * z 12 * t 12 - z 2 * z 15 * t 12
      + z 3 * z 14 * t 12 - z 5 * z 9 * t 13 + z 4 * z 8 * t 13 - z 7 * z 11 * t 13
      - z 6 * z 10 * t 13 - z 1 * z 13 * t 13 + z 3 * z 15 * t 13 + z 2 * z 14 * t 13
      - z 6 * z 9 * t 14 + z 7 * z 8 * t 14 + z 4 * z 11 * t 14 + z 5 * z 10 * t 14
      - z 2 * z 13 * t 14 - z 3 * z 12 * t 14 - z 1 * z 14 * t 14 - z 7 * z 9 * t 15
      - z 6 * z 8 * t 15 + z 5 * z 11 * t 15 - z 4 * z 10 * t 15 - z 3 * z 13 * t 15
      + z 2 * z 12 * t 15 - z 1 * z 15 * t 15 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, borderedA_zero_left,
    borderedA_zero_right, uv]
  ring

private theorem row_2 (z t : ℕ → R) :
    schurN z t 0 2 =
      -z 1 ^ 2 * t 2 - z 2 ^ 2 * t 2 - z 3 ^ 2 * t 2 - z 4 ^ 2 * t 2 - z 5 ^ 2 * t 2 - z 6 ^ 2 * t 2
      - z 7 ^ 2 * t 2 + z 1 * z 11 * t 8 - z 2 * z 8 * t 8 - z 3 * z 9 * t 8 - z 4 * z 14 * t 8
      - z 5 * z 15 * t 8 + z 6 * z 12 * t 8 + z 7 * z 13 * t 8 - z 1 * z 10 * t 9 + z 3 * z 8 * t 9
      - z 2 * z 9 * t 9 + z 5 * z 14 * t 9 - z 4 * z 15 * t 9 + z 7 * z 12 * t 9 - z 6 * z 13 * t 9
      - z 2 * z 10 * t 10 + z 3 * z 11 * t 10 + z 1 * z 9 * t 10 + z 6 * z 14 * t 10
      + z 7 * z 15 * t 10 + z 4 * z 12 * t 10 + z 5 * z 13 * t 10 - z 3 * z 10 * t 11
      - z 2 * z 11 * t 11 - z 1 * z 8 * t 11 + z 7 * z 14 * t 11 - z 6 * z 15 * t 11
      - z 5 * z 12 * t 11 + z 4 * z 13 * t 11 - z 4 * z 10 * t 12 + z 5 * z 11 * t 12
      - z 6 * z 8 * t 12 - z 7 * z 9 * t 12 + z 1 * z 15 * t 12 - z 2 * z 12 * t 12
      - z 3 * z 13 * t 12 - z 5 * z 10 * t 13 - z 4 * z 11 * t 13 - z 7 * z 8 * t 13
      + z 6 * z 9 * t 13 - z 1 * z 14 * t 13 + z 3 * z 12 * t 13 - z 2 * z 13 * t 13
      - z 6 * z 10 * t 14 - z 7 * z 11 * t 14 + z 4 * z 8 * t 14 - z 5 * z 9 * t 14
      - z 2 * z 14 * t 14 + z 3 * z 15 * t 14 + z 1 * z 13 * t 14 - z 7 * z 10 * t 15
      + z 6 * z 11 * t 15 + z 5 * z 8 * t 15 + z 4 * z 9 * t 15 - z 3 * z 14 * t 15
      - z 2 * z 15 * t 15 - z 1 * z 12 * t 15 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, borderedA_zero_left,
    borderedA_zero_right, uv]
  ring

private theorem row_3 (z t : ℕ → R) :
    schurN z t 0 3 =
      -z 1 ^ 2 * t 3 - z 2 ^ 2 * t 3 - z 3 ^ 2 * t 3 - z 4 ^ 2 * t 3 - z 5 ^ 2 * t 3 - z 6 ^ 2 * t 3
      - z 7 ^ 2 * t 3 - z 1 * z 10 * t 8 + z 2 * z 9 * t 8 - z 3 * z 8 * t 8 - z 4 * z 15 * t 8
      + z 5 * z 14 * t 8 - z 6 * z 13 * t 8 + z 7 * z 12 * t 8 - z 1 * z 11 * t 9 - z 3 * z 9 * t 9
      - z 2 * z 8 * t 9 + z 5 * z 15 * t 9 + z 4 * z 14 * t 9 - z 7 * z 13 * t 9 - z 6 * z 12 * t 9
      - z 2 * z 11 * t 10 - z 3 * z 10 * t 10 + z 1 * z 8 * t 10 + z 6 * z 15 * t 10
      - z 7 * z 14 * t 10 - z 4 * z 13 * t 10 + z 5 * z 12 * t 10 - z 3 * z 11 * t 11
      + z 2 * z 10 * t 11 + z 1 * z 9 * t 11 + z 7 * z 15 * t 11 + z 6 * z 14 * t 11
      + z 5 * z 13 * t 11 + z 4 * z 12 * t 11 - z 4 * z 11 * t 12 - z 5 * z 10 * t 12
      + z 6 * z 9 * t 12 - z 7 * z 8 * t 12 - z 1 * z 14 * t 12 + z 2 * z 13 * t 12
      - z 3 * z 12 * t 12 - z 5 * z 11 * t 13 + z 4 * z 10 * t 13 + z 7 * z 9 * t 13
      + z 6 * z 8 * t 13 - z 1 * z 15 * t 13 - z 3 * z 13 * t 13 - z 2 * z 12 * t 13
      - z 6 * z 11 * t 14 + z 7 * z 10 * t 14 - z 4 * z 9 * t 14 - z 5 * z 8 * t 14
      - z 2 * z 15 * t 14 - z 3 * z 14 * t 14 + z 1 * z 12 * t 14 - z 7 * z 11 * t 15
      - z 6 * z 10 * t 15 - z 5 * z 9 * t 15 + z 4 * z 8 * t 15 - z 3 * z 15 * t 15
      + z 2 * z 14 * t 15 + z 1 * z 13 * t 15 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, borderedA_zero_left,
    borderedA_zero_right, uv]
  ring

private theorem row_4 (z t : ℕ → R) :
    schurN z t 0 4 =
      -z 1 ^ 2 * t 4 - z 2 ^ 2 * t 4 - z 3 ^ 2 * t 4 - z 4 ^ 2 * t 4 - z 5 ^ 2 * t 4 - z 6 ^ 2 * t 4
      - z 7 ^ 2 * t 4 + z 1 * z 13 * t 8 + z 2 * z 14 * t 8 + z 3 * z 15 * t 8 - z 4 * z 8 * t 8
      - z 5 * z 9 * t 8 - z 6 * z 10 * t 8 - z 7 * z 11 * t 8 - z 1 * z 12 * t 9 - z 3 * z 14 * t 9
      + z 2 * z 15 * t 9 + z 5 * z 8 * t 9 - z 4 * z 9 * t 9 - z 7 * z 10 * t 9 + z 6 * z 11 * t 9
      - z 2 * z 12 * t 10 + z 3 * z 13 * t 10 - z 1 * z 15 * t 10 + z 6 * z 8 * t 10
      + z 7 * z 9 * t 10 - z 4 * z 10 * t 10 - z 5 * z 11 * t 10 - z 3 * z 12 * t 11
      - z 2 * z 13 * t 11 + z 1 * z 14 * t 11 + z 7 * z 8 * t 11 - z 6 * z 9 * t 11
      + z 5 * z 10 * t 11 - z 4 * z 11 * t 11 - z 4 * z 12 * t 12 + z 5 * z 13 * t 12
      + z 6 * z 14 * t 12 + z 7 * z 15 * t 12 + z 1 * z 9 * t 12 + z 2 * z 10 * t 12
      + z 3 * z 11 * t 12 - z 5 * z 12 * t 13 - z 4 * z 13 * t 13 + z 7 * z 14 * t 13
      - z 6 * z 15 * t 13 - z 1 * z 8 * t 13 - z 3 * z 10 * t 13 + z 2 * z 11 * t 13
      - z 6 * z 12 * t 14 - z 7 * z 13 * t 14 - z 4 * z 14 * t 14 + z 5 * z 15 * t 14
      - z 2 * z 8 * t 14 + z 3 * z 9 * t 14 - z 1 * z 11 * t 14 - z 7 * z 12 * t 15
      + z 6 * z 13 * t 15 - z 5 * z 14 * t 15 - z 4 * z 15 * t 15 - z 3 * z 8 * t 15
      - z 2 * z 9 * t 15 + z 1 * z 10 * t 15 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, borderedA_zero_left,
    borderedA_zero_right, uv]
  ring

private theorem row_5 (z t : ℕ → R) :
    schurN z t 0 5 =
      -z 1 ^ 2 * t 5 - z 2 ^ 2 * t 5 - z 3 ^ 2 * t 5 - z 4 ^ 2 * t 5 - z 5 ^ 2 * t 5 - z 6 ^ 2 * t 5
      - z 7 ^ 2 * t 5 - z 1 * z 12 * t 8 + z 2 * z 15 * t 8 - z 3 * z 14 * t 8 + z 4 * z 9 * t 8
      - z 5 * z 8 * t 8 + z 6 * z 11 * t 8 - z 7 * z 10 * t 8 - z 1 * z 13 * t 9 - z 3 * z 15 * t 9
      - z 2 * z 14 * t 9 - z 5 * z 9 * t 9 - z 4 * z 8 * t 9 + z 7 * z 11 * t 9 + z 6 * z 10 * t 9
      - z 2 * z 13 * t 10 - z 3 * z 12 * t 10 + z 1 * z 14 * t 10 - z 6 * z 9 * t 10
      + z 7 * z 8 * t 10 + z 4 * z 11 * t 10 - z 5 * z 10 * t 10 - z 3 * z 13 * t 11
      + z 2 * z 12 * t 11 + z 1 * z 15 * t 11 - z 7 * z 9 * t 11 - z 6 * z 8 * t 11
      - z 5 * z 11 * t 11 - z 4 * z 10 * t 11 - z 4 * z 13 * t 12 - z 5 * z 12 * t 12
      + z 6 * z 15 * t 12 - z 7 * z 14 * t 12 + z 1 * z 8 * t 12 - z 2 * z 11 * t 12
      + z 3 * z 10 * t 12 - z 5 * z 13 * t 13 + z 4 * z 12 * t 13 + z 7 * z 15 * t 13
      + z 6 * z 14 * t 13 + z 1 * z 9 * t 13 + z 3 * z 11 * t 13 + z 2 * z 10 * t 13
      - z 6 * z 13 * t 14 + z 7 * z 12 * t 14 - z 4 * z 15 * t 14 - z 5 * z 14 * t 14
      + z 2 * z 9 * t 14 + z 3 * z 8 * t 14 - z 1 * z 10 * t 14 - z 7 * z 13 * t 15
      - z 6 * z 12 * t 15 - z 5 * z 15 * t 15 + z 4 * z 14 * t 15 + z 3 * z 9 * t 15
      - z 2 * z 8 * t 15 - z 1 * z 11 * t 15 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, borderedA_zero_left,
    borderedA_zero_right, uv]
  ring

private theorem row_6 (z t : ℕ → R) :
    schurN z t 0 6 =
      -z 1 ^ 2 * t 6 - z 2 ^ 2 * t 6 - z 3 ^ 2 * t 6 - z 4 ^ 2 * t 6 - z 5 ^ 2 * t 6 - z 6 ^ 2 * t 6
      - z 7 ^ 2 * t 6 - z 1 * z 15 * t 8 - z 2 * z 12 * t 8 + z 3 * z 13 * t 8 + z 4 * z 10 * t 8
      - z 5 * z 11 * t 8 - z 6 * z 8 * t 8 + z 7 * z 9 * t 8 - z 1 * z 14 * t 9 + z 3 * z 12 * t 9
      + z 2 * z 13 * t 9 - z 5 * z 10 * t 9 - z 4 * z 11 * t 9 - z 7 * z 8 * t 9 - z 6 * z 9 * t 9
      - z 2 * z 14 * t 10 - z 3 * z 15 * t 10 - z 1 * z 13 * t 10 - z 6 * z 10 * t 10
      + z 7 * z 11 * t 10 - z 4 * z 8 * t 10 + z 5 * z 9 * t 10 - z 3 * z 14 * t 11
      + z 2 * z 15 * t 11 - z 1 * z 12 * t 11 - z 7 * z 10 * t 11 - z 6 * z 11 * t 11
      + z 5 * z 8 * t 11 + z 4 * z 9 * t 11 - z 4 * z 14 * t 12 - z 5 * z 15 * t 12
      - z 6 * z 12 * t 12 + z 7 * z 13 * t 12 + z 1 * z 11 * t 12 + z 2 * z 8 * t 12
      - z 3 * z 9 * t 12 - z 5 * z 14 * t 13 + z 4 * z 15 * t 13 - z 7 * z 12 * t 13
      - z 6 * z 13 * t 13 + z 1 * z 10 * t 13 - z 3 * z 8 * t 13 - z 2 * z 9 * t 13
      - z 6 * z 14 * t 14 + z 7 * z 15 * t 14 + z 4 * z 12 * t 14 + z 5 * z 13 * t 14
      + z 2 * z 10 * t 14 + z 3 * z 11 * t 14 + z 1 * z 9 * t 14 - z 7 * z 14 * t 15
      - z 6 * z 15 * t 15 + z 5 * z 12 * t 15 - z 4 * z 13 * t 15 + z 3 * z 10 * t 15
      - z 2 * z 11 * t 15 + z 1 * z 8 * t 15 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, borderedA_zero_left,
    borderedA_zero_right, uv]
  ring

private theorem row_7 (z t : ℕ → R) :
    schurN z t 0 7 =
      -z 1 ^ 2 * t 7 - z 2 ^ 2 * t 7 - z 3 ^ 2 * t 7 - z 4 ^ 2 * t 7 - z 5 ^ 2 * t 7 - z 6 ^ 2 * t 7
      - z 7 ^ 2 * t 7 + z 1 * z 14 * t 8 - z 2 * z 13 * t 8 - z 3 * z 12 * t 8 + z 4 * z 11 * t 8
      + z 5 * z 10 * t 8 - z 6 * z 9 * t 8 - z 7 * z 8 * t 8 - z 1 * z 15 * t 9 + z 3 * z 13 * t 9
      - z 2 * z 12 * t 9 - z 5 * z 11 * t 9 + z 4 * z 10 * t 9 - z 7 * z 9 * t 9 + z 6 * z 8 * t 9
      - z 2 * z 15 * t 10 + z 3 * z 14 * t 10 + z 1 * z 12 * t 10 - z 6 * z 11 * t 10
      - z 7 * z 10 * t 10 - z 4 * z 9 * t 10 - z 5 * z 8 * t 10 - z 3 * z 15 * t 11
      - z 2 * z 14 * t 11 - z 1 * z 13 * t 11 - z 7 * z 11 * t 11 + z 6 * z 10 * t 11
      + z 5 * z 9 * t 11 - z 4 * z 8 * t 11 - z 4 * z 15 * t 12 + z 5 * z 14 * t 12
      - z 6 * z 13 * t 12 - z 7 * z 12 * t 12 - z 1 * z 10 * t 12 + z 2 * z 9 * t 12
      + z 3 * z 8 * t 12 - z 5 * z 15 * t 13 - z 4 * z 14 * t 13 - z 7 * z 13 * t 13
      + z 6 * z 12 * t 13 + z 1 * z 11 * t 13 - z 3 * z 9 * t 13 + z 2 * z 8 * t 13
      - z 6 * z 15 * t 14 - z 7 * z 14 * t 14 + z 4 * z 13 * t 14 - z 5 * z 12 * t 14
      + z 2 * z 11 * t 14 - z 3 * z 10 * t 14 - z 1 * z 8 * t 14 - z 7 * z 15 * t 15
      + z 6 * z 14 * t 15 + z 5 * z 13 * t 15 + z 4 * z 12 * t 15 + z 3 * z 11 * t 15
      + z 2 * z 10 * t 15 + z 1 * z 9 * t 15 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, borderedA_zero_left,
    borderedA_zero_right, uv]
  ring

/-- The border row of the Schur block against `u`: `∑ S'(0, f) z_f = -U (z.t)`. -/
theorem schurN_row (z t : ℕ → R) :
    schurN z t 0 1 * z 1 + schurN z t 0 2 * z 2 + schurN z t 0 3 * z 3 + schurN z t 0 4 * z 4 +
        schurN z t 0 5 * z 5 + schurN z t 0 6 * z 6 + schurN z t 0 7 * z 7 =
      -uv z * ∑ k ∈ Finset.range 15, z (k + 1) * t (k + 1) := by
  rw [row_1, row_2, row_3, row_4, row_5, row_6, row_7]
  simp [uv, Finset.sum_range_succ]
  ring

/-- The Pfaffian of the Schur block, by expansion along its border row. -/
theorem pfaffian_schurN (z t : ℕ → R) :
    Matrix.pfaffianAux (schurN z t) [0, 1, 2, 3, 4, 5, 6, 7] =
      -(uv z * qv z * gv z) * (uv z * ∑ k ∈ Finset.range 15, z (k + 1) * t (k + 1)) := by
  have h1 : (-1 : R) ^ 0 * Matrix.pfaffianAux (schurN z t) [2, 3, 4, 5, 6, 7] =
      uv z * qv z * gv z * z 1 := adjPf_schurN z t (f := 1) (by norm_num) (by norm_num)
  have h2 : (-1 : R) ^ 1 * Matrix.pfaffianAux (schurN z t) [1, 3, 4, 5, 6, 7] =
      uv z * qv z * gv z * z 2 := adjPf_schurN z t (f := 2) (by norm_num) (by norm_num)
  have h3 : (-1 : R) ^ 2 * Matrix.pfaffianAux (schurN z t) [1, 2, 4, 5, 6, 7] =
      uv z * qv z * gv z * z 3 := adjPf_schurN z t (f := 3) (by norm_num) (by norm_num)
  have h4 : (-1 : R) ^ 3 * Matrix.pfaffianAux (schurN z t) [1, 2, 3, 5, 6, 7] =
      uv z * qv z * gv z * z 4 := adjPf_schurN z t (f := 4) (by norm_num) (by norm_num)
  have h5 : (-1 : R) ^ 4 * Matrix.pfaffianAux (schurN z t) [1, 2, 3, 4, 6, 7] =
      uv z * qv z * gv z * z 5 := adjPf_schurN z t (f := 5) (by norm_num) (by norm_num)
  have h6 : (-1 : R) ^ 5 * Matrix.pfaffianAux (schurN z t) [1, 2, 3, 4, 5, 7] =
      uv z * qv z * gv z * z 6 := adjPf_schurN z t (f := 6) (by norm_num) (by norm_num)
  have h7 : (-1 : R) ^ 6 * Matrix.pfaffianAux (schurN z t) [1, 2, 3, 4, 5, 6] =
      uv z * qv z * gv z * z 7 := adjPf_schurN z t (f := 7) (by norm_num) (by norm_num)
  have hr := schurN_row z t
  rw [Matrix.pfaffianAux_eight_indices]
  linear_combination schurN z t 0 1 * h1 + schurN z t 0 2 * h2 + schurN z t 0 3 * h3 +
    schurN z t 0 4 * h4 + schurN z t 0 5 * h5 + schurN z t 0 6 * h6 + schurN z t 0 7 * h7 +
    uv z * qv z * gv z * hr

/-- The block order of the indices gives the Pfaffian of the bordered matrix: the block swap has
sign `(-1) ^ 64 = 1`. -/
theorem pfaffian_A16_swap (z t : ℕ → R) :
    Matrix.pfaffianAux (A16 z t) ([8, 9, 10, 11, 12, 13, 14, 15] ++ [0, 1, 2, 3, 4, 5, 6, 7]) =
      Matrix.pfaffian (A16 z t) := by
  rw [Matrix.pfaffianAux_append_swap_blocks _ (A16_skew z t)]
  have hl : ([0, 1, 2, 3, 4, 5, 6, 7] ++ [8, 9, 10, 11, 12, 13, 14, 15] : List (Fin 16)) =
      List.finRange 16 := by decide
  rw [hl]
  norm_num [Matrix.pfaffian]

/-- `U ^ 8 Pf A = U ^ 8 * rhsv z t` when `2` is left-regular. -/
theorem pow_mul_pfaffian (h2 : IsLeftRegular (2 : R)) (z t : ℕ → R) :
    uv z ^ 8 * Matrix.pfaffian (A16 z t) = uv z ^ 8 * rhsv z t := by
  have hBM : Bm z t * -(Bm z t * Xm z t) = uv z • Xm z t := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, Bm_mul_self, Matrix.neg_mul, neg_neg, Matrix.smul_mul,
      Matrix.one_mul]
  have hS := Matrix.schur_cleared_of_mul h2 (Bm z t) (Xm z t) (Dm z t) (Bm_transpose z t)
    (Dm_transpose z t) (uv z) (-(Bm z t * Xm z t)) hBM (List.finRange 8) (by simp)
  have hL : ((List.finRange 8).map Sum.inl ++ (List.finRange 8).map Sum.inr).map e16 =
      ([8, 9, 10, 11, 12, 13, 14, 15] ++ [0, 1, 2, 3, 4, 5, 6, 7] : List (Fin 16)) := by decide
  rw [fromBlocks_eq, Matrix.pfaffianAux_reindex (A16 z t) e16 16
    ((List.finRange 8).map Sum.inl ++ (List.finRange 8).map Sum.inr) (by simp), hL,
    pfaffian_A16_swap, pfaffian_Bm, pfaffian_schurS, pfaffian_schurN, List.length_finRange,
    show (8 : ℕ) / 2 = 4 from rfl] at hS
  unfold rhsv
  linear_combination hS

/-- The integer polynomial variables `z_k = X k`. -/
noncomputable def Zp : ℕ → MvPolynomial ℕ ℤ := fun k => MvPolynomial.X k

/-- The integer polynomial variables `t_k = X (k + 16)`. -/
noncomputable def Tp : ℕ → MvPolynomial ℕ ℤ := fun k => MvPolynomial.X (k + 16)

/-- The identity over the integer polynomial ring, where `U ^ 8` cancels. -/
theorem pfaffian_A16_poly : Matrix.pfaffian (A16 Zp Tp) = rhsv Zp Tp := by
  have h2 : IsLeftRegular (2 : MvPolynomial ℕ ℤ) := mul_right_injective₀ two_ne_zero
  have hU : uv Zp ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval fun _ => (1 : ℤ)) h
    simp [uv, Zp, Finset.sum_range_succ] at this
  exact mul_left_cancel₀ (pow_ne_zero 8 hU) (pow_mul_pfaffian h2 Zp Tp)

/-- The bordered matrix is natural under ring homomorphisms. -/
theorem map_borderedA {S : Type*} [CommRing S] (f : S →+* R) (z t : ℕ → S) (a b : ℕ) :
    f (borderedA z t a b) = borderedA (f ∘ z) (f ∘ t) a b := by
  unfold borderedA
  split_ifs <;> simp

/-- The bordered matrix on `0, ..., 15` reads `z` only below `16`. -/
theorem borderedA_congr {z z' t t' : ℕ → R} (hz : ∀ k < 16, z' k = z k) (ht : ∀ k, t' k = t k)
    {a b : ℕ} (ha : a < 16) (hb : b < 16) : borderedA z' t' a b = borderedA z t a b := by
  have hx : a ^^^ b < 16 := Nat.xor_lt_two_pow (n := 4) (by omega) (by omega)
  unfold borderedA
  split_ifs <;> simp [ht, hz _ hx]

/-- The right-hand side is natural under ring homomorphisms. -/
theorem map_rhsv {S : Type*} [CommRing S] (f : S →+* R) (z t : ℕ → S) :
    f (rhsv z t) = rhsv (f ∘ z) (f ∘ t) := by
  simp only [rhsv, qv, gv, uv, vv, wv, map_neg, map_mul, map_sub, map_pow, map_sum, map_ofNat,
    Function.comp_apply]

/-- The right-hand side reads `z` only below `16`. -/
theorem rhsv_congr {z z' t t' : ℕ → R} (hz : ∀ k < 16, z' k = z k) (ht : ∀ k, t' k = t k) :
    rhsv z' t' = rhsv z t := by
  simp [rhsv, qv, gv, uv, vv, wv, Finset.sum_range_succ, hz, ht]

/-- The identity `Pf A(z, t) = -(z.t) Q G` over every commutative ring, by evaluation of the integer
polynomial identity. -/
theorem pfaffian_sixteen (z t : ℕ → R) :
    Matrix.pfaffian (Matrix.of fun a b : Fin 16 => borderedA z t a b) = rhsv z t := by
  let φ : MvPolynomial ℕ ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) fun n => if n < 16 then z n else t (n - 16)
  have hz : ∀ k < 16, (φ ∘ Zp) k = z k := by
    intro k hk
    simp [φ, Zp, hk]
  have ht : ∀ k, (φ ∘ Tp) k = t k := by
    intro k
    simp [φ, Tp]
  have h := congrArg φ pfaffian_A16_poly
  rw [map_rhsv, rhsv_congr hz ht] at h
  rw [← h]
  unfold Matrix.pfaffian
  rw [Matrix.map_pfaffianAux φ (A16 Zp Tp) (List.finRange 16)]
  congr 1
  funext a b
  simp only [A16, Matrix.of_apply]
  rw [map_borderedA φ Zp Tp, borderedA_congr hz ht a.isLt b.isLt]

end PfaffianSixteenSchur
