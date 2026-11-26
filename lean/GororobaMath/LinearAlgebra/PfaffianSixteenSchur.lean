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
evaluation carries the identity to every commutative ring. The proof evaluates only the 210
sign-table cases of `PfaffianSchurBlock.sedSign_eq_sign` (by `decide +kernel`), the 210 cases of
the skew symmetry of that table and four index-list equalities (by `decide`); the Pfaffian
identity itself is symbolic.

## Main results

* `PfaffianSixteenSchur.pow_mul_pfaffian`: `U ^ 8 Pf A = U ^ 8 * rhsv z t` when `2` is
  left-regular.
* `PfaffianSixteenSchur.pfaffian_sixteen`: `Pf A(z, t) = -(z.t) Q G` over every commutative ring.
-/

@[expose] public section

namespace PfaffianSixteenSchur

open PfaffianCross PfaffianSixteen PfaffianSchur PfaffianSchurBlock

open scoped Matrix

/-- The sedenion sign table is skew off the diagonal. -/
theorem sedSign_skew {a b : ℕ} (ha : 1 ≤ a) (ha16 : a < 16) (hb : 1 ≤ b) (hb16 : b < 16)
    (hab : a ≠ b) : sedSign a b = -sedSign b a := by
  interval_cases a <;> interval_cases b <;> first | exact absurd rfl hab | decide

variable {R : Type*} [CommRing R]

/-- The first row of the bordered matrix is `-t`. -/
theorem borderedA_zero_left (z t : ℕ → R) {b : ℕ} (hb : b ≠ 0) : borderedA z t 0 b = -t b := by
  simp only [borderedA, Ne.symm hb, ↓reduceIte]

/-- The first column of the bordered matrix is `t`. -/
theorem borderedA_zero_right (z t : ℕ → R) {a : ℕ} (ha : a ≠ 0) : borderedA z t a 0 = t a := by
  simp only [borderedA, ha, ↓reduceIte]

/-- The bordered matrix is skew on `0, ..., 15`. -/
theorem borderedA_skew (z t : ℕ → R) {a b : ℕ} (ha : a < 16) (hb : b < 16) :
    borderedA z t a b = -borderedA z t b a := by
  by_cases hab : a = b
  · subst hab
    simp only [borderedA_self, neg_zero]
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
    simp only [Bm, Fin.isValue, Fin.zero_eta, Matrix.mul_apply, Matrix.of_apply,
        Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Nat.one_le_ofNat, Nat.reduceLT,
        Fin.sum_univ_eight, borderedA_self, mul_zero, Nat.one_mod, Nat.reduceAdd, ne_eq,
        Nat.reduceEqDiff, not_false_eq_true, borderedA_of_pos, sedSign_8_9, Int.reduceNeg,
        Int.cast_neg, Int.cast_one, Nat.reduceXor, neg_mul, one_mul, Nat.succ_ne_self, sedSign_9_8,
        zero_add, Nat.reduceMod, sedSign_8_10, sedSign_10_8, sedSign_8_11, sedSign_11_8,
        sedSign_8_12, sedSign_12_8, sedSign_8_13, sedSign_13_8, sedSign_8_14, sedSign_14_8,
        Nat.mod_succ, Nat.lt_add_one, sedSign_8_15, sedSign_15_8, uv, Finset.sum_range_succ,
        Finset.range_one, Finset.sum_singleton, Matrix.neg_apply, Matrix.smul_apply,
        Matrix.one_apply_eq, smul_eq_mul, mul_one, neg_add_rev, Fin.mk_one, mul_neg, zero_mul,
        neg_zero, sedSign_10_9, neg_neg, sedSign_11_9, sedSign_12_9, sedSign_13_9, sedSign_14_9,
        sedSign_15_9, zero_ne_one, Matrix.one_apply_ne, Fin.reduceFinMk, sedSign_9_10,
        sedSign_11_10, sedSign_12_10, sedSign_13_10, sedSign_14_10, sedSign_15_10, Fin.reduceEq,
        sedSign_9_11, sedSign_10_11, sedSign_12_11, sedSign_13_11, sedSign_14_11, sedSign_15_11,
        sedSign_9_12, sedSign_10_12, sedSign_11_12, sedSign_13_12, sedSign_14_12, sedSign_15_12,
        sedSign_9_13, sedSign_10_13, sedSign_11_13, sedSign_12_13, sedSign_14_13, sedSign_15_13,
        sedSign_9_14, sedSign_10_14, sedSign_11_14, sedSign_12_14, sedSign_13_14, sedSign_15_14,
        sedSign_9_15, sedSign_10_15, sedSign_11_15, sedSign_12_15, sedSign_13_15,
        sedSign_14_15] <;> ring

private theorem bb_1 (z t : ℕ → R) (j : Fin 8) :
    (Bm z t * Bm z t) 1 j = (-(uv z • (1 : Matrix (Fin 8) (Fin 8) R))) 1 j := by
  fin_cases j <;>
    simp only [Bm, Fin.isValue, Fin.zero_eta, Matrix.mul_apply, Matrix.of_apply,
        Fin.coe_ofNat_eq_mod, Nat.one_mod, Nat.reduceAdd, Nat.one_le_ofNat, Nat.reduceLT,
        Nat.zero_mod, add_zero, Fin.sum_univ_eight, ne_eq, Nat.succ_ne_self, not_false_eq_true,
        borderedA_of_pos, sedSign_9_8, Int.cast_one, Nat.reduceXor, one_mul, borderedA_self,
        mul_zero, zero_mul, Nat.reduceMod, Nat.reduceEqDiff, sedSign_9_10, sedSign_10_8, zero_add,
        sedSign_9_11, Int.reduceNeg, Int.cast_neg, neg_mul, sedSign_11_8, sedSign_9_12,
        sedSign_12_8, sedSign_9_13, sedSign_13_8, sedSign_9_14, sedSign_14_8, Nat.mod_succ,
        Nat.lt_add_one, sedSign_9_15, sedSign_15_8, uv, Finset.sum_range_succ, Finset.range_one,
        Finset.sum_singleton, Matrix.neg_apply, Matrix.smul_apply, one_ne_zero, Matrix.one_apply_ne,
        smul_eq_mul, neg_zero, Fin.mk_one, sedSign_8_9, mul_neg, sedSign_10_9, sedSign_11_9,
        sedSign_12_9, sedSign_13_9, sedSign_14_9, sedSign_15_9, Matrix.one_apply_eq, mul_one,
        neg_add_rev, Fin.reduceFinMk, sedSign_8_10, sedSign_11_10, neg_neg, sedSign_12_10,
        sedSign_13_10, sedSign_14_10, sedSign_15_10, Fin.reduceEq, sedSign_8_11, sedSign_10_11,
        sedSign_12_11, sedSign_13_11, sedSign_14_11, sedSign_15_11, sedSign_8_12, sedSign_10_12,
        sedSign_11_12, sedSign_13_12, sedSign_14_12, sedSign_15_12, sedSign_8_13, sedSign_10_13,
        sedSign_11_13, sedSign_12_13, sedSign_14_13, sedSign_15_13, sedSign_8_14, sedSign_10_14,
        sedSign_11_14, sedSign_12_14, sedSign_13_14, sedSign_15_14, sedSign_8_15, sedSign_10_15,
        sedSign_11_15, sedSign_12_15, sedSign_13_15, sedSign_14_15] <;> ring

private theorem bb_2 (z t : ℕ → R) (j : Fin 8) :
    (Bm z t * Bm z t) 2 j = (-(uv z • (1 : Matrix (Fin 8) (Fin 8) R))) 2 j := by
  fin_cases j <;>
    simp only [Bm, Fin.isValue, Fin.zero_eta, Matrix.mul_apply, Matrix.of_apply,
        Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.one_le_ofNat, Nat.reduceLT,
        Nat.zero_mod, add_zero, Fin.sum_univ_eight, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
        borderedA_of_pos, sedSign_10_8, Int.cast_one, Nat.reduceXor, one_mul, borderedA_self,
        mul_zero, Nat.one_mod, Nat.succ_ne_self, sedSign_10_9, Int.reduceNeg, Int.cast_neg, neg_mul,
        sedSign_9_8, zero_add, zero_mul, sedSign_10_11, sedSign_11_8, sedSign_10_12, sedSign_12_8,
        sedSign_10_13, sedSign_13_8, sedSign_10_14, sedSign_14_8, Nat.mod_succ, Nat.lt_add_one,
        sedSign_10_15, sedSign_15_8, uv, Finset.sum_range_succ, Finset.range_one,
        Finset.sum_singleton, Matrix.neg_apply, Matrix.smul_apply, Fin.reduceEq,
        Matrix.one_apply_ne, smul_eq_mul, neg_zero, Fin.mk_one, sedSign_8_9, mul_neg, sedSign_11_9,
        sedSign_12_9, sedSign_13_9, sedSign_14_9, sedSign_15_9, neg_neg, Fin.reduceFinMk,
        sedSign_8_10, sedSign_9_10, sedSign_11_10, sedSign_12_10, sedSign_13_10, sedSign_14_10,
        sedSign_15_10, Matrix.one_apply_eq, mul_one, neg_add_rev, sedSign_8_11, sedSign_9_11,
        sedSign_12_11, sedSign_13_11, sedSign_14_11, sedSign_15_11, sedSign_8_12, sedSign_9_12,
        sedSign_11_12, sedSign_13_12, sedSign_14_12, sedSign_15_12, sedSign_8_13, sedSign_9_13,
        sedSign_11_13, sedSign_12_13, sedSign_14_13, sedSign_15_13, sedSign_8_14, sedSign_9_14,
        sedSign_11_14, sedSign_12_14, sedSign_13_14, sedSign_15_14, sedSign_8_15, sedSign_9_15,
        sedSign_11_15, sedSign_12_15, sedSign_13_15, sedSign_14_15] <;> ring

private theorem bb_3 (z t : ℕ → R) (j : Fin 8) :
    (Bm z t * Bm z t) 3 j = (-(uv z • (1 : Matrix (Fin 8) (Fin 8) R))) 3 j := by
  fin_cases j <;>
    simp only [Bm, Fin.isValue, Fin.zero_eta, Matrix.mul_apply, Matrix.of_apply,
        Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.one_le_ofNat, Nat.reduceLT,
        Nat.zero_mod, add_zero, Fin.sum_univ_eight, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
        borderedA_of_pos, sedSign_11_8, Int.cast_one, Nat.reduceXor, one_mul, borderedA_self,
        mul_zero, Nat.one_mod, sedSign_11_9, Nat.succ_ne_self, sedSign_9_8, zero_add, sedSign_11_10,
        Int.reduceNeg, Int.cast_neg, neg_mul, sedSign_10_8, zero_mul, sedSign_11_12, sedSign_12_8,
        sedSign_11_13, sedSign_13_8, sedSign_11_14, sedSign_14_8, Nat.mod_succ, Nat.lt_add_one,
        sedSign_11_15, sedSign_15_8, uv, Finset.sum_range_succ, Finset.range_one,
        Finset.sum_singleton, Matrix.neg_apply, Matrix.smul_apply, Fin.reduceEq,
        Matrix.one_apply_ne, smul_eq_mul, neg_zero, Fin.mk_one, sedSign_8_9, mul_neg, sedSign_10_9,
        neg_neg, sedSign_12_9, sedSign_13_9, sedSign_14_9, sedSign_15_9, Fin.reduceFinMk,
        sedSign_8_10, sedSign_9_10, sedSign_12_10, sedSign_13_10, sedSign_14_10, sedSign_15_10,
        sedSign_8_11, sedSign_9_11, sedSign_10_11, sedSign_12_11, sedSign_13_11, sedSign_14_11,
        sedSign_15_11, Matrix.one_apply_eq, mul_one, neg_add_rev, sedSign_8_12, sedSign_9_12,
        sedSign_10_12, sedSign_13_12, sedSign_14_12, sedSign_15_12, sedSign_8_13, sedSign_9_13,
        sedSign_10_13, sedSign_12_13, sedSign_14_13, sedSign_15_13, sedSign_8_14, sedSign_9_14,
        sedSign_10_14, sedSign_12_14, sedSign_13_14, sedSign_15_14, sedSign_8_15, sedSign_9_15,
        sedSign_10_15, sedSign_12_15, sedSign_13_15, sedSign_14_15] <;> ring

private theorem bb_4 (z t : ℕ → R) (j : Fin 8) :
    (Bm z t * Bm z t) 4 j = (-(uv z • (1 : Matrix (Fin 8) (Fin 8) R))) 4 j := by
  fin_cases j <;>
    simp only [Bm, Fin.isValue, Fin.zero_eta, Matrix.mul_apply, Matrix.of_apply,
        Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.one_le_ofNat, Nat.reduceLT,
        Nat.zero_mod, add_zero, Fin.sum_univ_eight, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
        borderedA_of_pos, sedSign_12_8, Int.cast_one, Nat.reduceXor, one_mul, borderedA_self,
        mul_zero, Nat.one_mod, sedSign_12_9, Int.reduceNeg, Int.cast_neg, neg_mul, Nat.succ_ne_self,
        sedSign_9_8, zero_add, sedSign_12_10, sedSign_10_8, sedSign_12_11, sedSign_11_8, zero_mul,
        sedSign_12_13, sedSign_13_8, sedSign_12_14, sedSign_14_8, Nat.mod_succ, Nat.lt_add_one,
        sedSign_12_15, sedSign_15_8, uv, Finset.sum_range_succ, Finset.range_one,
        Finset.sum_singleton, Matrix.neg_apply, Matrix.smul_apply, Fin.reduceEq,
        Matrix.one_apply_ne, smul_eq_mul, neg_zero, Fin.mk_one, sedSign_8_9, mul_neg, sedSign_10_9,
        neg_neg, sedSign_11_9, sedSign_13_9, sedSign_14_9, sedSign_15_9, Fin.reduceFinMk,
        sedSign_8_10, sedSign_9_10, sedSign_11_10, sedSign_13_10, sedSign_14_10, sedSign_15_10,
        sedSign_8_11, sedSign_9_11, sedSign_10_11, sedSign_13_11, sedSign_14_11, sedSign_15_11,
        sedSign_8_12, sedSign_9_12, sedSign_10_12, sedSign_11_12, sedSign_13_12, sedSign_14_12,
        sedSign_15_12, Matrix.one_apply_eq, mul_one, neg_add_rev, sedSign_8_13, sedSign_9_13,
        sedSign_10_13, sedSign_11_13, sedSign_14_13, sedSign_15_13, sedSign_8_14, sedSign_9_14,
        sedSign_10_14, sedSign_11_14, sedSign_13_14, sedSign_15_14, sedSign_8_15, sedSign_9_15,
        sedSign_10_15, sedSign_11_15, sedSign_13_15, sedSign_14_15] <;> ring

private theorem bb_5 (z t : ℕ → R) (j : Fin 8) :
    (Bm z t * Bm z t) 5 j = (-(uv z • (1 : Matrix (Fin 8) (Fin 8) R))) 5 j := by
  fin_cases j <;>
    simp only [Bm, Fin.isValue, Fin.zero_eta, Matrix.mul_apply, Matrix.of_apply,
        Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.one_le_ofNat, Nat.reduceLT,
        Nat.zero_mod, add_zero, Fin.sum_univ_eight, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
        borderedA_of_pos, sedSign_13_8, Int.cast_one, Nat.reduceXor, one_mul, borderedA_self,
        mul_zero, Nat.one_mod, sedSign_13_9, Nat.succ_ne_self, sedSign_9_8, zero_add, sedSign_13_10,
        Int.reduceNeg, Int.cast_neg, neg_mul, sedSign_10_8, sedSign_13_11, sedSign_11_8,
        sedSign_13_12, sedSign_12_8, zero_mul, sedSign_13_14, sedSign_14_8, Nat.mod_succ,
        Nat.lt_add_one, sedSign_13_15, sedSign_15_8, uv, Finset.sum_range_succ, Finset.range_one,
        Finset.sum_singleton, Matrix.neg_apply, Matrix.smul_apply, Fin.reduceEq,
        Matrix.one_apply_ne, smul_eq_mul, neg_zero, Fin.mk_one, sedSign_8_9, mul_neg, sedSign_10_9,
        neg_neg, sedSign_11_9, sedSign_12_9, sedSign_14_9, sedSign_15_9, Fin.reduceFinMk,
        sedSign_8_10, sedSign_9_10, sedSign_11_10, sedSign_12_10, sedSign_14_10, sedSign_15_10,
        sedSign_8_11, sedSign_9_11, sedSign_10_11, sedSign_12_11, sedSign_14_11, sedSign_15_11,
        sedSign_8_12, sedSign_9_12, sedSign_10_12, sedSign_11_12, sedSign_14_12, sedSign_15_12,
        sedSign_8_13, sedSign_9_13, sedSign_10_13, sedSign_11_13, sedSign_12_13, sedSign_14_13,
        sedSign_15_13, Matrix.one_apply_eq, mul_one, neg_add_rev, sedSign_8_14, sedSign_9_14,
        sedSign_10_14, sedSign_11_14, sedSign_12_14, sedSign_15_14, sedSign_8_15, sedSign_9_15,
        sedSign_10_15, sedSign_11_15, sedSign_12_15, sedSign_14_15] <;> ring

private theorem bb_6 (z t : ℕ → R) (j : Fin 8) :
    (Bm z t * Bm z t) 6 j = (-(uv z • (1 : Matrix (Fin 8) (Fin 8) R))) 6 j := by
  fin_cases j <;>
    simp only [Bm, Fin.isValue, Fin.zero_eta, Matrix.mul_apply, Matrix.of_apply,
        Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceAdd, Nat.one_le_ofNat, Nat.reduceLT,
        Nat.zero_mod, add_zero, Fin.sum_univ_eight, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
        borderedA_of_pos, sedSign_14_8, Int.cast_one, Nat.reduceXor, one_mul, borderedA_self,
        mul_zero, Nat.one_mod, sedSign_14_9, Nat.succ_ne_self, sedSign_9_8, zero_add, sedSign_14_10,
        sedSign_10_8, sedSign_14_11, Int.reduceNeg, Int.cast_neg, neg_mul, sedSign_11_8,
        sedSign_14_12, sedSign_12_8, sedSign_14_13, sedSign_13_8, zero_mul, Nat.mod_succ,
        Nat.lt_add_one, sedSign_14_15, sedSign_15_8, uv, Finset.sum_range_succ, Finset.range_one,
        Finset.sum_singleton, Matrix.neg_apply, Matrix.smul_apply, Fin.reduceEq,
        Matrix.one_apply_ne, smul_eq_mul, neg_zero, Fin.mk_one, sedSign_8_9, mul_neg, sedSign_10_9,
        sedSign_11_9, sedSign_12_9, neg_neg, sedSign_13_9, sedSign_15_9, Fin.reduceFinMk,
        sedSign_8_10, sedSign_9_10, sedSign_11_10, sedSign_12_10, sedSign_13_10, sedSign_15_10,
        sedSign_8_11, sedSign_9_11, sedSign_10_11, sedSign_12_11, sedSign_13_11, sedSign_15_11,
        sedSign_8_12, sedSign_9_12, sedSign_10_12, sedSign_11_12, sedSign_13_12, sedSign_15_12,
        sedSign_8_13, sedSign_9_13, sedSign_10_13, sedSign_11_13, sedSign_12_13, sedSign_15_13,
        sedSign_8_14, sedSign_9_14, sedSign_10_14, sedSign_11_14, sedSign_12_14, sedSign_13_14,
        sedSign_15_14, Matrix.one_apply_eq, mul_one, neg_add_rev, sedSign_8_15, sedSign_9_15,
        sedSign_10_15, sedSign_11_15, sedSign_12_15, sedSign_13_15] <;> ring

private theorem bb_7 (z t : ℕ → R) (j : Fin 8) :
    (Bm z t * Bm z t) 7 j = (-(uv z • (1 : Matrix (Fin 8) (Fin 8) R))) 7 j := by
  fin_cases j <;>
    simp only [Bm, Fin.isValue, Fin.zero_eta, Matrix.mul_apply, Matrix.of_apply,
        Fin.coe_ofNat_eq_mod, Nat.mod_succ, Nat.reduceAdd, Nat.one_le_ofNat, Nat.lt_add_one,
        Nat.zero_mod, add_zero, Fin.sum_univ_eight, Nat.reduceLT, ne_eq, Nat.reduceEqDiff,
        not_false_eq_true, borderedA_of_pos, sedSign_15_8, Int.cast_one, Nat.reduceXor, one_mul,
        borderedA_self, mul_zero, Nat.one_mod, sedSign_15_9, Int.reduceNeg, Int.cast_neg, neg_mul,
        Nat.succ_ne_self, sedSign_9_8, zero_add, Nat.reduceMod, sedSign_15_10, sedSign_10_8,
        sedSign_15_11, sedSign_11_8, sedSign_15_12, sedSign_12_8, sedSign_15_13, sedSign_13_8,
        sedSign_15_14, sedSign_14_8, zero_mul, uv, Finset.sum_range_succ, Finset.range_one,
        Finset.sum_singleton, Matrix.neg_apply, Matrix.smul_apply, Fin.reduceEq,
        Matrix.one_apply_ne, smul_eq_mul, neg_zero, Fin.mk_one, sedSign_8_9, mul_neg, sedSign_10_9,
        sedSign_11_9, sedSign_12_9, neg_neg, sedSign_13_9, sedSign_14_9, Fin.reduceFinMk,
        sedSign_8_10, sedSign_9_10, sedSign_11_10, sedSign_12_10, sedSign_13_10, sedSign_14_10,
        sedSign_8_11, sedSign_9_11, sedSign_10_11, sedSign_12_11, sedSign_13_11, sedSign_14_11,
        sedSign_8_12, sedSign_9_12, sedSign_10_12, sedSign_11_12, sedSign_13_12, sedSign_14_12,
        sedSign_8_13, sedSign_9_13, sedSign_10_13, sedSign_11_13, sedSign_12_13, sedSign_14_13,
        sedSign_8_14, sedSign_9_14, sedSign_10_14, sedSign_11_14, sedSign_12_14, sedSign_13_14,
        sedSign_8_15, sedSign_9_15, sedSign_10_15, sedSign_11_15, sedSign_12_15, sedSign_13_15,
        sedSign_14_15, Matrix.one_apply_eq, mul_one, neg_add_rev] <;> ring

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
    (List.finRange 8) (by simp only [List.length_finRange])
  have hl : (List.finRange 8).map (fun i : Fin 8 => 8 + (i : ℕ)) =
      [8, 9, 10, 11, 12, 13, 14, 15] := by decide
  unfold Matrix.pfaffian
  change Matrix.pfaffianAux (fun a b : Fin 8 => borderedA z t (8 + (a : ℕ)) (8 + (b : ℕ)))
    (List.finRange 8) = _
  rw [h, hl, Matrix.pfaffianAux_eight_indices]
  simp only [Nat.one_le_ofNat, Nat.reduceLT, ne_eq, Nat.reduceEqDiff, not_false_eq_true,
      borderedA_of_pos, sedSign_8_9, Int.reduceNeg, Int.cast_neg, Int.cast_one, Nat.reduceXor,
      neg_mul, one_mul, Matrix.pfaffianAux_six_indices, sedSign_10_11, sedSign_12_13,
      Nat.lt_add_one, sedSign_14_15, mul_neg, sedSign_12_14, sedSign_13_15, sedSign_12_15,
      sedSign_13_14, sedSign_10_12, sedSign_11_13, neg_neg, sedSign_11_14, sedSign_11_15,
      sedSign_10_13, sedSign_11_12, sedSign_10_14, sub_neg_eq_add, sedSign_10_15, sedSign_8_10,
      sedSign_9_11, sedSign_9_12, sedSign_9_13, sedSign_9_14, sedSign_9_15, sedSign_8_11,
      sedSign_9_10, sedSign_8_12, sedSign_8_13, sedSign_8_14, sedSign_8_15, uv,
      Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, zero_add, Nat.reduceAdd]
  ring

/-- The cleared Schur complement `U Dm - Xmᵀ Bm Xm` is `schurN`. -/
theorem schurS_eq (z t : ℕ → R) (i j : Fin 8) :
    (uv z • Dm z t + (Xm z t)ᵀ * -(Bm z t * Xm z t)) i j = schurN z t i j := by
  simp only [Dm, Matrix.smul_of, Xm, Bm, mul_neg, Matrix.add_apply, Matrix.of_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.neg_apply, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_eight,
      Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, Nat.one_mod, Nat.reduceAdd,
      Nat.reduceMod, Nat.mod_succ, neg_add_rev, schurN, Finset.sum_range_succ, Finset.range_one,
      Finset.sum_singleton, zero_add]
  ring

/-- The Pfaffian of the cleared Schur complement is that of `schurN` on `0, ..., 7`. -/
theorem pfaffian_schurS (z t : ℕ → R) :
    Matrix.pfaffianAux (uv z • Dm z t + (Xm z t)ᵀ * -(Bm z t * Xm z t)) (List.finRange 8) =
      Matrix.pfaffianAux (schurN z t) [0, 1, 2, 3, 4, 5, 6, 7] := by
  rw [Matrix.pfaffianAux_congr _ (fun a b : Fin 8 => schurN z t a b) _ _ rfl
    (fun a _ b _ => schurS_eq z t a b),
    Matrix.pfaffianAux_reindex (schurN z t) (fun a : Fin 8 => (a : ℕ)) 8 _ (by simp only [
        List.length_finRange])]
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
  simp only [schurN, uv, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, zero_add,
      Nat.reduceAdd, ne_eq, one_ne_zero, not_false_eq_true, borderedA_zero_left, mul_neg,
      le_add_iff_nonneg_left, zero_le, Nat.add_eq_zero_iff, OfNat.ofNat_ne_zero, and_false,
      borderedA_zero_right, Nat.one_le_ofNat, Nat.reduceLT, Std.le_refl, Nat.one_lt_ofNat,
      OfNat.ofNat_ne_one, borderedA_of_pos, sedSign_8_1, Int.cast_one, Nat.reduceXor, one_mul,
      sedSign_9_1, Int.reduceNeg, Int.cast_neg, neg_mul, sedSign_10_1, sedSign_11_1, sedSign_12_1,
      sedSign_13_1, sedSign_14_1, Nat.lt_add_one, sedSign_15_1, borderedA_self, mul_zero, zero_mul,
      Nat.reduceEqDiff, sedSign_8_9, neg_neg, sedSign_8_10, sedSign_8_11, sedSign_8_12,
      sedSign_8_13, sedSign_8_14, sedSign_8_15, Nat.succ_ne_self, sedSign_9_8, neg_zero, add_zero,
      sedSign_9_10, sedSign_9_11, sedSign_9_12, sedSign_9_13, sedSign_9_14, sedSign_9_15,
      sedSign_10_8, sedSign_10_9, sedSign_10_11, sedSign_10_12, sedSign_10_13, sedSign_10_14,
      sedSign_10_15, sedSign_11_8, sedSign_11_9, sedSign_11_10, sedSign_11_12, sedSign_11_13,
      sedSign_11_14, sedSign_11_15, sedSign_12_8, sedSign_12_9, sedSign_12_10, sedSign_12_11,
      sedSign_12_13, sedSign_12_14, sedSign_12_15, sedSign_13_8, sedSign_13_9, sedSign_13_10,
      sedSign_13_11, sedSign_13_12, sedSign_13_14, sedSign_13_15, sedSign_14_8, sedSign_14_9,
      sedSign_14_10, sedSign_14_11, sedSign_14_12, sedSign_14_13, sedSign_14_15, sedSign_15_8,
      sedSign_15_9, sedSign_15_10, sedSign_15_11, sedSign_15_12, sedSign_15_13, sedSign_15_14]
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
  simp only [schurN, uv, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, zero_add,
      Nat.reduceAdd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, borderedA_zero_left, mul_neg,
      le_add_iff_nonneg_left, zero_le, Nat.add_eq_zero_iff, and_false, borderedA_zero_right,
      Nat.one_le_ofNat, Nat.reduceLT, Nat.reduceEqDiff, borderedA_of_pos, sedSign_8_2, Int.cast_one,
      Nat.reduceXor, one_mul, sedSign_9_2, sedSign_10_2, Int.reduceNeg, Int.cast_neg, neg_mul,
      sedSign_11_2, sedSign_12_2, sedSign_13_2, sedSign_14_2, Nat.lt_add_one, sedSign_15_2,
      borderedA_self, mul_zero, zero_mul, sedSign_8_9, sedSign_8_10, neg_neg, sedSign_8_11,
      sedSign_8_12, sedSign_8_13, sedSign_8_14, sedSign_8_15, Nat.succ_ne_self, sedSign_9_8,
      add_zero, sedSign_9_10, sedSign_9_11, sedSign_9_12, sedSign_9_13, sedSign_9_14, sedSign_9_15,
      sedSign_10_8, sedSign_10_9, neg_zero, sedSign_10_11, sedSign_10_12, sedSign_10_13,
      sedSign_10_14, sedSign_10_15, sedSign_11_8, sedSign_11_9, sedSign_11_10, sedSign_11_12,
      sedSign_11_13, sedSign_11_14, sedSign_11_15, sedSign_12_8, sedSign_12_9, sedSign_12_10,
      sedSign_12_11, sedSign_12_13, sedSign_12_14, sedSign_12_15, sedSign_13_8, sedSign_13_9,
      sedSign_13_10, sedSign_13_11, sedSign_13_12, sedSign_13_14, sedSign_13_15, sedSign_14_8,
      sedSign_14_9, sedSign_14_10, sedSign_14_11, sedSign_14_12, sedSign_14_13, sedSign_14_15,
      sedSign_15_8, sedSign_15_9, sedSign_15_10, sedSign_15_11, sedSign_15_12, sedSign_15_13,
      sedSign_15_14]
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
  simp only [schurN, uv, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, zero_add,
      Nat.reduceAdd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, borderedA_zero_left, mul_neg,
      le_add_iff_nonneg_left, zero_le, Nat.add_eq_zero_iff, and_false, borderedA_zero_right,
      Nat.one_le_ofNat, Nat.reduceLT, Nat.reduceEqDiff, borderedA_of_pos, sedSign_8_3, Int.cast_one,
      Nat.reduceXor, one_mul, sedSign_9_3, Int.reduceNeg, Int.cast_neg, neg_mul, sedSign_10_3,
      sedSign_11_3, sedSign_12_3, sedSign_13_3, sedSign_14_3, Nat.lt_add_one, sedSign_15_3,
      borderedA_self, mul_zero, zero_mul, sedSign_8_9, neg_neg, sedSign_8_10, sedSign_8_11,
      sedSign_8_12, sedSign_8_13, sedSign_8_14, sedSign_8_15, Nat.succ_ne_self, sedSign_9_8,
      neg_zero, add_zero, sedSign_9_10, sedSign_9_11, sedSign_9_12, sedSign_9_13, sedSign_9_14,
      sedSign_9_15, sedSign_10_8, sedSign_10_9, sedSign_10_11, sedSign_10_12, sedSign_10_13,
      sedSign_10_14, sedSign_10_15, sedSign_11_8, sedSign_11_9, sedSign_11_10, sedSign_11_12,
      sedSign_11_13, sedSign_11_14, sedSign_11_15, sedSign_12_8, sedSign_12_9, sedSign_12_10,
      sedSign_12_11, sedSign_12_13, sedSign_12_14, sedSign_12_15, sedSign_13_8, sedSign_13_9,
      sedSign_13_10, sedSign_13_11, sedSign_13_12, sedSign_13_14, sedSign_13_15, sedSign_14_8,
      sedSign_14_9, sedSign_14_10, sedSign_14_11, sedSign_14_12, sedSign_14_13, sedSign_14_15,
      sedSign_15_8, sedSign_15_9, sedSign_15_10, sedSign_15_11, sedSign_15_12, sedSign_15_13,
      sedSign_15_14]
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
  simp only [schurN, uv, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, zero_add,
      Nat.reduceAdd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, borderedA_zero_left, mul_neg,
      le_add_iff_nonneg_left, zero_le, Nat.add_eq_zero_iff, and_false, borderedA_zero_right,
      Nat.one_le_ofNat, Nat.reduceLT, Nat.reduceEqDiff, borderedA_of_pos, sedSign_8_4, Int.cast_one,
      Nat.reduceXor, one_mul, sedSign_9_4, sedSign_10_4, sedSign_11_4, sedSign_12_4, Int.reduceNeg,
      Int.cast_neg, neg_mul, sedSign_13_4, sedSign_14_4, Nat.lt_add_one, sedSign_15_4,
      borderedA_self, mul_zero, zero_mul, sedSign_8_9, sedSign_8_10, sedSign_8_11, sedSign_8_12,
      neg_neg, sedSign_8_13, sedSign_8_14, sedSign_8_15, Nat.succ_ne_self, sedSign_9_8, add_zero,
      sedSign_9_10, sedSign_9_11, sedSign_9_12, sedSign_9_13, sedSign_9_14, sedSign_9_15,
      sedSign_10_8, sedSign_10_9, sedSign_10_11, sedSign_10_12, sedSign_10_13, sedSign_10_14,
      sedSign_10_15, sedSign_11_8, sedSign_11_9, sedSign_11_10, sedSign_11_12, sedSign_11_13,
      sedSign_11_14, sedSign_11_15, sedSign_12_8, sedSign_12_9, sedSign_12_10, sedSign_12_11,
      neg_zero, sedSign_12_13, sedSign_12_14, sedSign_12_15, sedSign_13_8, sedSign_13_9,
      sedSign_13_10, sedSign_13_11, sedSign_13_12, sedSign_13_14, sedSign_13_15, sedSign_14_8,
      sedSign_14_9, sedSign_14_10, sedSign_14_11, sedSign_14_12, sedSign_14_13, sedSign_14_15,
      sedSign_15_8, sedSign_15_9, sedSign_15_10, sedSign_15_11, sedSign_15_12, sedSign_15_13,
      sedSign_15_14]
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
  simp only [schurN, uv, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, zero_add,
      Nat.reduceAdd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, borderedA_zero_left, mul_neg,
      le_add_iff_nonneg_left, zero_le, Nat.add_eq_zero_iff, and_false, borderedA_zero_right,
      Nat.one_le_ofNat, Nat.reduceLT, Nat.reduceEqDiff, borderedA_of_pos, sedSign_8_5, Int.cast_one,
      Nat.reduceXor, one_mul, sedSign_9_5, Int.reduceNeg, Int.cast_neg, neg_mul, sedSign_10_5,
      sedSign_11_5, sedSign_12_5, sedSign_13_5, sedSign_14_5, Nat.lt_add_one, sedSign_15_5,
      borderedA_self, mul_zero, zero_mul, sedSign_8_9, neg_neg, sedSign_8_10, sedSign_8_11,
      sedSign_8_12, sedSign_8_13, sedSign_8_14, sedSign_8_15, Nat.succ_ne_self, sedSign_9_8,
      neg_zero, add_zero, sedSign_9_10, sedSign_9_11, sedSign_9_12, sedSign_9_13, sedSign_9_14,
      sedSign_9_15, sedSign_10_8, sedSign_10_9, sedSign_10_11, sedSign_10_12, sedSign_10_13,
      sedSign_10_14, sedSign_10_15, sedSign_11_8, sedSign_11_9, sedSign_11_10, sedSign_11_12,
      sedSign_11_13, sedSign_11_14, sedSign_11_15, sedSign_12_8, sedSign_12_9, sedSign_12_10,
      sedSign_12_11, sedSign_12_13, sedSign_12_14, sedSign_12_15, sedSign_13_8, sedSign_13_9,
      sedSign_13_10, sedSign_13_11, sedSign_13_12, sedSign_13_14, sedSign_13_15, sedSign_14_8,
      sedSign_14_9, sedSign_14_10, sedSign_14_11, sedSign_14_12, sedSign_14_13, sedSign_14_15,
      sedSign_15_8, sedSign_15_9, sedSign_15_10, sedSign_15_11, sedSign_15_12, sedSign_15_13,
      sedSign_15_14]
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
  simp only [schurN, uv, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, zero_add,
      Nat.reduceAdd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, borderedA_zero_left, mul_neg,
      le_add_iff_nonneg_left, zero_le, Nat.add_eq_zero_iff, and_false, borderedA_zero_right,
      Nat.one_le_ofNat, Nat.reduceLT, Nat.reduceEqDiff, borderedA_of_pos, sedSign_8_6, Int.cast_one,
      Nat.reduceXor, one_mul, sedSign_9_6, Int.reduceNeg, Int.cast_neg, neg_mul, sedSign_10_6,
      sedSign_11_6, sedSign_12_6, sedSign_13_6, sedSign_14_6, Nat.lt_add_one, sedSign_15_6,
      borderedA_self, mul_zero, zero_mul, sedSign_8_9, neg_neg, sedSign_8_10, sedSign_8_11,
      sedSign_8_12, sedSign_8_13, sedSign_8_14, sedSign_8_15, Nat.succ_ne_self, sedSign_9_8,
      neg_zero, add_zero, sedSign_9_10, sedSign_9_11, sedSign_9_12, sedSign_9_13, sedSign_9_14,
      sedSign_9_15, sedSign_10_8, sedSign_10_9, sedSign_10_11, sedSign_10_12, sedSign_10_13,
      sedSign_10_14, sedSign_10_15, sedSign_11_8, sedSign_11_9, sedSign_11_10, sedSign_11_12,
      sedSign_11_13, sedSign_11_14, sedSign_11_15, sedSign_12_8, sedSign_12_9, sedSign_12_10,
      sedSign_12_11, sedSign_12_13, sedSign_12_14, sedSign_12_15, sedSign_13_8, sedSign_13_9,
      sedSign_13_10, sedSign_13_11, sedSign_13_12, sedSign_13_14, sedSign_13_15, sedSign_14_8,
      sedSign_14_9, sedSign_14_10, sedSign_14_11, sedSign_14_12, sedSign_14_13, sedSign_14_15,
      sedSign_15_8, sedSign_15_9, sedSign_15_10, sedSign_15_11, sedSign_15_12, sedSign_15_13,
      sedSign_15_14]
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
  simp only [schurN, uv, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, zero_add,
      Nat.reduceAdd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, borderedA_zero_left, mul_neg,
      le_add_iff_nonneg_left, zero_le, Nat.add_eq_zero_iff, and_false, borderedA_zero_right,
      Nat.one_le_ofNat, Nat.reduceLT, Nat.succ_ne_self, borderedA_of_pos, sedSign_8_7, Int.cast_one,
      Nat.reduceXor, one_mul, Nat.reduceEqDiff, sedSign_9_7, sedSign_10_7, Int.reduceNeg,
      Int.cast_neg, neg_mul, sedSign_11_7, sedSign_12_7, sedSign_13_7, sedSign_14_7, Nat.lt_add_one,
      sedSign_15_7, borderedA_self, mul_zero, zero_mul, sedSign_8_9, sedSign_8_10, neg_neg,
      sedSign_8_11, sedSign_8_12, sedSign_8_13, sedSign_8_14, sedSign_8_15, sedSign_9_8, add_zero,
      sedSign_9_10, sedSign_9_11, sedSign_9_12, sedSign_9_13, sedSign_9_14, sedSign_9_15,
      sedSign_10_8, sedSign_10_9, neg_zero, sedSign_10_11, sedSign_10_12, sedSign_10_13,
      sedSign_10_14, sedSign_10_15, sedSign_11_8, sedSign_11_9, sedSign_11_10, sedSign_11_12,
      sedSign_11_13, sedSign_11_14, sedSign_11_15, sedSign_12_8, sedSign_12_9, sedSign_12_10,
      sedSign_12_11, sedSign_12_13, sedSign_12_14, sedSign_12_15, sedSign_13_8, sedSign_13_9,
      sedSign_13_10, sedSign_13_11, sedSign_13_12, sedSign_13_14, sedSign_13_15, sedSign_14_8,
      sedSign_14_9, sedSign_14_10, sedSign_14_11, sedSign_14_12, sedSign_14_13, sedSign_14_15,
      sedSign_15_8, sedSign_15_9, sedSign_15_10, sedSign_15_11, sedSign_15_12, sedSign_15_13,
      sedSign_15_14]
  ring

/-- The border row of the Schur block against `u`: `∑ S'(0, f) z_f = -U (z.t)`. -/
theorem schurN_row (z t : ℕ → R) :
    schurN z t 0 1 * z 1 + schurN z t 0 2 * z 2 + schurN z t 0 3 * z 3 + schurN z t 0 4 * z 4 +
        schurN z t 0 5 * z 5 + schurN z t 0 6 * z 6 + schurN z t 0 7 * z 7 =
      -uv z * ∑ k ∈ Finset.range 15, z (k + 1) * t (k + 1) := by
  rw [row_1, row_2, row_3, row_4, row_5, row_6, row_7]
  simp only [neg_mul, uv, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, zero_add,
      Nat.reduceAdd, neg_add_rev]
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
    (Dm_transpose z t) (uv z) (-(Bm z t * Xm z t)) hBM (List.finRange 8) (by simp only [
        List.length_finRange, Nat.reduceMod])
  have hL : ((List.finRange 8).map Sum.inl ++ (List.finRange 8).map Sum.inr).map e16 =
      ([8, 9, 10, 11, 12, 13, 14, 15] ++ [0, 1, 2, 3, 4, 5, 6, 7] : List (Fin 16)) := by decide
  rw [fromBlocks_eq, Matrix.pfaffianAux_reindex (A16 z t) e16 16
    ((List.finRange 8).map Sum.inl ++ (List.finRange 8).map Sum.inr) (by simp only [
        List.length_append, List.length_map, List.length_finRange, Nat.reduceAdd]), hL,
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
    simp only [uv, Zp, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, zero_add,
        Nat.reduceAdd, map_add, map_mul, MvPolynomial.eval_X, mul_one, Int.reduceAdd, map_zero,
        OfNat.ofNat_ne_zero] at this
  exact mul_left_cancel₀ (pow_ne_zero 8 hU) (pow_mul_pfaffian h2 Zp Tp)

/-- The bordered matrix is natural under ring homomorphisms. -/
theorem map_borderedA {S : Type*} [CommRing S] (f : S →+* R) (z t : ℕ → S) (a b : ℕ) :
    f (borderedA z t a b) = borderedA (f ∘ z) (f ∘ t) a b := by
  unfold borderedA
  split_ifs <;> simp only [map_zero, map_neg, Function.comp_apply, BitVec.ofNat_xor, map_mul,
      map_intCast]

/-- The bordered matrix on `0, ..., 15` reads `z` only below `16`. -/
theorem borderedA_congr {z z' t t' : ℕ → R} (hz : ∀ k < 16, z' k = z k) (ht : ∀ k, t' k = t k)
    {a b : ℕ} (ha : a < 16) (hb : b < 16) : borderedA z' t' a b = borderedA z t a b := by
  have hx : a ^^^ b < 16 := Nat.xor_lt_two_pow (n := 4) (by omega) (by omega)
  unfold borderedA
  split_ifs <;> simp only [ht, BitVec.ofNat_xor, hz _ hx]

/-- The right-hand side is natural under ring homomorphisms. -/
theorem map_rhsv {S : Type*} [CommRing S] (f : S →+* R) (z t : ℕ → S) :
    f (rhsv z t) = rhsv (f ∘ z) (f ∘ t) := by
  simp only [rhsv, qv, gv, uv, vv, wv, map_neg, map_mul, map_sub, map_pow, map_sum, map_ofNat,
    Function.comp_apply]

/-- The right-hand side reads `z` only below `16`. -/
theorem rhsv_congr {z z' t t' : ℕ → R} (hz : ∀ k < 16, z' k = z k) (ht : ∀ k, t' k = t k) :
    rhsv z' t' = rhsv z t := by
  simp only [rhsv, ht, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, zero_add,
      Nat.one_lt_ofNat, hz, Nat.reduceAdd, Nat.reduceLT, Nat.lt_add_one, neg_add_rev, qv, gv, uv,
      vv, wv]

/-- The identity `Pf A(z, t) = -(z.t) Q G` over every commutative ring, by evaluation of the integer
polynomial identity. -/
theorem pfaffian_sixteen (z t : ℕ → R) :
    Matrix.pfaffian (Matrix.of fun a b : Fin 16 => borderedA z t a b) = rhsv z t := by
  let φ : MvPolynomial ℕ ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) fun n => if n < 16 then z n else t (n - 16)
  have hz : ∀ k < 16, (φ ∘ Zp) k = z k := by
    intro k hk
    simp only [MvPolynomial.coe_eval₂Hom, Function.comp_apply, Zp, MvPolynomial.eval₂_X, hk,
        ↓reduceIte, φ]
  have ht : ∀ k, (φ ∘ Tp) k = t k := by
    intro k
    simp only [MvPolynomial.coe_eval₂Hom, Function.comp_apply, Tp, MvPolynomial.eval₂_X,
        add_lt_iff_neg_right, not_lt_zero, ↓reduceIte, add_tsub_cancel_right, φ]
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
