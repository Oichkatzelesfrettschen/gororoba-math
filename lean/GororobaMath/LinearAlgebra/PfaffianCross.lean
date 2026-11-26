/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.LinearAlgebra.PfaffianBlock
public import GororobaMath.CayleyDickson.Tower

/-!
# The Pfaffian adjugate of the octonion cross-product matrix with a rank-two term

Convention: indices `1, ..., 7` name the imaginary units of the octonions, the level-3 tower
with the product of `GororobaMath.CayleyDickson.Tower`. `octSign a b` is the coefficient of
`e_a` in `e_(a xor b) * e_b`, which is `Tower.sign 3 (a ^^^ b) b` for nonzero `a ≠ b`
(`octSign_eq_sign`), and `0` on the diagonal. For `y : ℕ → R` read at `1, ..., 7`,
`crossMat y a b = octSign a b * y (a ^^^ b)` is the matrix of `x ↦ Im (y x)` on the imaginary
units, `cross y x a` its product with `x` (the cross product `y × x`), `dot7 y x` the bilinear
sum `y_1 x_1 + ... + y_7 x_7` with no conjugation, and `wedge x w a b = x a * w b - w a * x b`.
The Pfaffian adjugate of a skew matrix `C` on `1, ..., 7` is the vector whose entry `f` is
`(-1) ^ (f - 1)` times the Pfaffian of `C` on the six indices other than `f`.
`octSign_eq_sign` binds the literal table to `Tower.sign 3` by `decide +kernel`, one finite
evaluation for each of the 42 pairs `a ≠ b` in `1, ..., 7` (measured: 0.09 s of tactic and kernel
time for all 42, Lean 4.35.0); the adjugate identity itself is symbolic, proved by `ring` over
every commutative ring.

## Main results

* `PfaffianCross.octSign_eq_sign`: the table is the level-3 sign of the tower.
* `PfaffianCross.adjPf_crossMat_add_wedge`: for every commutative ring, the Pfaffian adjugate of
  `crossMat y + wedge x w` at `f` is
  `dot7 y y * y f - dot7 y x * cross y w f + dot7 y w * cross y x f - dot7 y (cross x w) * y f`;
  at `x = 0` it is `|y|² y`.
-/

@[expose] public section

namespace PfaffianCross

/-- The octonion sign table: the coefficient of `e_a` in `e_(a xor b) * e_b` for `a, b < 8`,
and `0` elsewhere. -/
def octSign : ℕ → ℕ → ℤ
  | 0, 0 => 0
  | 0, 1 => -1
  | 0, 2 => -1
  | 0, 3 => -1
  | 0, 4 => -1
  | 0, 5 => -1
  | 0, 6 => -1
  | 0, 7 => -1
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => -1
  | 1, 3 => 1
  | 1, 4 => -1
  | 1, 5 => 1
  | 1, 6 => 1
  | 1, 7 => -1
  | 2, 0 => 1
  | 2, 1 => 1
  | 2, 2 => 0
  | 2, 3 => -1
  | 2, 4 => -1
  | 2, 5 => -1
  | 2, 6 => 1
  | 2, 7 => 1
  | 3, 0 => 1
  | 3, 1 => -1
  | 3, 2 => 1
  | 3, 3 => 0
  | 3, 4 => -1
  | 3, 5 => 1
  | 3, 6 => -1
  | 3, 7 => 1
  | 4, 0 => 1
  | 4, 1 => 1
  | 4, 2 => 1
  | 4, 3 => 1
  | 4, 4 => 0
  | 4, 5 => -1
  | 4, 6 => -1
  | 4, 7 => -1
  | 5, 0 => 1
  | 5, 1 => -1
  | 5, 2 => 1
  | 5, 3 => -1
  | 5, 4 => 1
  | 5, 5 => 0
  | 5, 6 => 1
  | 5, 7 => -1
  | 6, 0 => 1
  | 6, 1 => -1
  | 6, 2 => -1
  | 6, 3 => 1
  | 6, 4 => 1
  | 6, 5 => -1
  | 6, 6 => 0
  | 6, 7 => 1
  | 7, 0 => 1
  | 7, 1 => 1
  | 7, 2 => -1
  | 7, 3 => -1
  | 7, 4 => 1
  | 7, 5 => 1
  | 7, 6 => -1
  | 7, 7 => 0
  | _, _ => 0

theorem octSign_1_1 : octSign 1 1 = 0 := rfl
theorem octSign_1_2 : octSign 1 2 = -1 := rfl
theorem octSign_1_3 : octSign 1 3 = 1 := rfl
theorem octSign_1_4 : octSign 1 4 = -1 := rfl
theorem octSign_1_5 : octSign 1 5 = 1 := rfl
theorem octSign_1_6 : octSign 1 6 = 1 := rfl
theorem octSign_1_7 : octSign 1 7 = -1 := rfl
theorem octSign_2_1 : octSign 2 1 = 1 := rfl
theorem octSign_2_2 : octSign 2 2 = 0 := rfl
theorem octSign_2_3 : octSign 2 3 = -1 := rfl
theorem octSign_2_4 : octSign 2 4 = -1 := rfl
theorem octSign_2_5 : octSign 2 5 = -1 := rfl
theorem octSign_2_6 : octSign 2 6 = 1 := rfl
theorem octSign_2_7 : octSign 2 7 = 1 := rfl
theorem octSign_3_1 : octSign 3 1 = -1 := rfl
theorem octSign_3_2 : octSign 3 2 = 1 := rfl
theorem octSign_3_3 : octSign 3 3 = 0 := rfl
theorem octSign_3_4 : octSign 3 4 = -1 := rfl
theorem octSign_3_5 : octSign 3 5 = 1 := rfl
theorem octSign_3_6 : octSign 3 6 = -1 := rfl
theorem octSign_3_7 : octSign 3 7 = 1 := rfl
theorem octSign_4_1 : octSign 4 1 = 1 := rfl
theorem octSign_4_2 : octSign 4 2 = 1 := rfl
theorem octSign_4_3 : octSign 4 3 = 1 := rfl
theorem octSign_4_4 : octSign 4 4 = 0 := rfl
theorem octSign_4_5 : octSign 4 5 = -1 := rfl
theorem octSign_4_6 : octSign 4 6 = -1 := rfl
theorem octSign_4_7 : octSign 4 7 = -1 := rfl
theorem octSign_5_1 : octSign 5 1 = -1 := rfl
theorem octSign_5_2 : octSign 5 2 = 1 := rfl
theorem octSign_5_3 : octSign 5 3 = -1 := rfl
theorem octSign_5_4 : octSign 5 4 = 1 := rfl
theorem octSign_5_5 : octSign 5 5 = 0 := rfl
theorem octSign_5_6 : octSign 5 6 = 1 := rfl
theorem octSign_5_7 : octSign 5 7 = -1 := rfl
theorem octSign_6_1 : octSign 6 1 = -1 := rfl
theorem octSign_6_2 : octSign 6 2 = -1 := rfl
theorem octSign_6_3 : octSign 6 3 = 1 := rfl
theorem octSign_6_4 : octSign 6 4 = 1 := rfl
theorem octSign_6_5 : octSign 6 5 = -1 := rfl
theorem octSign_6_6 : octSign 6 6 = 0 := rfl
theorem octSign_6_7 : octSign 6 7 = 1 := rfl
theorem octSign_7_1 : octSign 7 1 = 1 := rfl
theorem octSign_7_2 : octSign 7 2 = -1 := rfl
theorem octSign_7_3 : octSign 7 3 = -1 := rfl
theorem octSign_7_4 : octSign 7 4 = 1 := rfl
theorem octSign_7_5 : octSign 7 5 = 1 := rfl
theorem octSign_7_6 : octSign 7 6 = -1 := rfl
theorem octSign_7_7 : octSign 7 7 = 0 := rfl

/-- The table agrees with the level-3 sign of the tower off the diagonal. -/
theorem octSign_eq_sign {a b : ℕ} (ha : 1 ≤ a) (ha7 : a ≤ 7) (hb : 1 ≤ b) (hb7 : b ≤ 7)
    (hab : a ≠ b) :
    octSign a b = CayleyDickson.Tower.sign 3 (BitVec.ofNat 3 (a ^^^ b)) (BitVec.ofNat 3 b) := by
  interval_cases a <;> interval_cases b <;> first | exact absurd rfl hab | decide +kernel

variable {R : Type*} [CommRing R]

/-- The matrix of `x ↦ Im (y x)` on the imaginary units. -/
def crossMat (y : ℕ → R) (a b : ℕ) : R := (octSign a b : R) * y (a ^^^ b)

/-- The cross product `y × x`, the product of `crossMat y` with `x`. -/
def cross (y x : ℕ → R) (a : ℕ) : R := ∑ b ∈ Finset.range 7, crossMat y a (b + 1) * x (b + 1)

/-- The bilinear sum `y_1 x_1 + ... + y_7 x_7`. -/
def dot7 (y x : ℕ → R) : R := ∑ k ∈ Finset.range 7, y (k + 1) * x (k + 1)

/-- The skew matrix `x wᵀ - w xᵀ`. -/
def wedge (x w : ℕ → R) (a b : ℕ) : R := x a * w b - w a * x b

/-- The value of the Pfaffian adjugate of `crossMat y + wedge x w` at `f`. -/
def adjRhs (y x w : ℕ → R) (f : ℕ) : R :=
  dot7 y y * y f - dot7 y x * cross y w f + dot7 y w * cross y x f - dot7 y (cross x w) * y f

private theorem adjPf_1 (y x w : ℕ → R) :
    (-1) ^ (1 - 1) * Matrix.pfaffianAux (fun a b => crossMat y a b + wedge x w a b)
      ((List.range' 1 7).erase 1) = adjRhs y x w 1 := by
  rw [show (List.range' 1 7).erase 1 = [2, 3, 4, 5, 6, 7] from rfl,
    Matrix.pfaffianAux_six_indices]
  simp only [tsub_self, pow_zero, crossMat, octSign_2_3, Int.reduceNeg, Int.cast_neg, Int.cast_one,
      Nat.reduceXor, neg_mul, one_mul, wedge, octSign_4_5, octSign_6_7, octSign_4_6, octSign_5_7,
      octSign_4_7, octSign_5_6, octSign_2_4, octSign_3_5, octSign_3_6, octSign_3_7, octSign_2_5,
      octSign_3_4, octSign_2_6, octSign_2_7, adjRhs, dot7, Finset.sum_range_succ, Finset.range_one,
      Finset.sum_singleton, zero_add, Nat.reduceAdd, cross, octSign_1_1, Int.cast_zero,
      LawfulXor.xor_self, zero_mul, octSign_1_2, octSign_1_3, octSign_1_4, octSign_1_5, octSign_1_6,
      octSign_1_7, octSign_2_1, even_two, Nat.xor_one_of_even, octSign_2_2, add_zero, octSign_3_1,
      octSign_3_2, octSign_3_3, octSign_4_1, octSign_4_2, octSign_4_3, octSign_4_4, octSign_5_1,
      octSign_5_2, octSign_5_3, octSign_5_4, octSign_5_5, octSign_6_1, octSign_6_2, octSign_6_3,
      octSign_6_4, octSign_6_5, octSign_6_6, octSign_7_1, octSign_7_2, octSign_7_3, octSign_7_4,
      octSign_7_5, octSign_7_6, octSign_7_7]
  ring

private theorem adjPf_2 (y x w : ℕ → R) :
    (-1) ^ (2 - 1) * Matrix.pfaffianAux (fun a b => crossMat y a b + wedge x w a b)
      ((List.range' 1 7).erase 2) = adjRhs y x w 2 := by
  rw [show (List.range' 1 7).erase 2 = [1, 3, 4, 5, 6, 7] from rfl,
    Matrix.pfaffianAux_six_indices]
  simp only [Nat.add_one_sub_one, pow_one, crossMat, octSign_1_3, Int.cast_one, Nat.reduceXor,
      one_mul, wedge, octSign_4_5, Int.reduceNeg, Int.cast_neg, neg_mul, octSign_6_7, octSign_4_6,
      octSign_5_7, octSign_4_7, octSign_5_6, octSign_1_4, octSign_3_5, octSign_3_6, octSign_3_7,
      octSign_1_5, octSign_3_4, octSign_1_6, octSign_1_7, neg_add_rev, neg_sub, adjRhs, dot7,
      Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, zero_add, Nat.reduceAdd, cross,
      octSign_2_1, even_two, Nat.xor_one_of_even, octSign_2_2, Int.cast_zero, LawfulXor.xor_self,
      zero_mul, add_zero, octSign_2_3, octSign_2_4, octSign_2_5, octSign_2_6, octSign_2_7,
      octSign_1_1, octSign_1_2, octSign_3_1, octSign_3_2, octSign_3_3, octSign_4_1, octSign_4_2,
      octSign_4_3, octSign_4_4, octSign_5_1, octSign_5_2, octSign_5_3, octSign_5_4, octSign_5_5,
      octSign_6_1, octSign_6_2, octSign_6_3, octSign_6_4, octSign_6_5, octSign_6_6, octSign_7_1,
      octSign_7_2, octSign_7_3, octSign_7_4, octSign_7_5, octSign_7_6, octSign_7_7]
  ring

private theorem adjPf_3 (y x w : ℕ → R) :
    (-1) ^ (3 - 1) * Matrix.pfaffianAux (fun a b => crossMat y a b + wedge x w a b)
      ((List.range' 1 7).erase 3) = adjRhs y x w 3 := by
  rw [show (List.range' 1 7).erase 3 = [1, 2, 4, 5, 6, 7] from rfl,
    Matrix.pfaffianAux_six_indices]
  simp only [Nat.add_one_sub_one, even_two, Even.neg_pow, one_pow, crossMat, octSign_1_2,
      Int.reduceNeg, Int.cast_neg, Int.cast_one, Nat.reduceXor, neg_mul, one_mul, wedge,
      octSign_4_5, octSign_6_7, octSign_4_6, octSign_5_7, octSign_4_7, octSign_5_6, octSign_1_4,
      octSign_2_5, octSign_2_6, octSign_2_7, octSign_1_5, octSign_2_4, octSign_1_6, octSign_1_7,
      adjRhs, dot7, Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton, zero_add,
      Nat.reduceAdd, cross, octSign_3_1, octSign_3_2, octSign_3_3, Int.cast_zero,
      LawfulXor.xor_self, zero_mul, add_zero, octSign_3_4, octSign_3_5, octSign_3_6, octSign_3_7,
      octSign_1_1, octSign_1_3, octSign_2_1, Nat.xor_one_of_even, octSign_2_2, octSign_2_3,
      octSign_4_1, octSign_4_2, octSign_4_3, octSign_4_4, octSign_5_1, octSign_5_2, octSign_5_3,
      octSign_5_4, octSign_5_5, octSign_6_1, octSign_6_2, octSign_6_3, octSign_6_4, octSign_6_5,
      octSign_6_6, octSign_7_1, octSign_7_2, octSign_7_3, octSign_7_4, octSign_7_5, octSign_7_6,
      octSign_7_7]
  ring

private theorem adjPf_4 (y x w : ℕ → R) :
    (-1) ^ (4 - 1) * Matrix.pfaffianAux (fun a b => crossMat y a b + wedge x w a b)
      ((List.range' 1 7).erase 4) = adjRhs y x w 4 := by
  rw [show (List.range' 1 7).erase 4 = [1, 2, 3, 5, 6, 7] from rfl,
    Matrix.pfaffianAux_six_indices]
  simp only [Nat.add_one_sub_one, crossMat, octSign_1_2, Int.reduceNeg, Int.cast_neg, Int.cast_one,
      Nat.reduceXor, neg_mul, one_mul, wedge, octSign_3_5, octSign_6_7, octSign_3_6, octSign_5_7,
      octSign_3_7, octSign_5_6, octSign_1_3, octSign_2_5, octSign_2_6, octSign_2_7, octSign_1_5,
      octSign_2_3, octSign_1_6, octSign_1_7, adjRhs, dot7, Finset.sum_range_succ, Finset.range_one,
      Finset.sum_singleton, zero_add, Nat.reduceAdd, cross, octSign_4_1, octSign_4_2, octSign_4_3,
      octSign_4_4, Int.cast_zero, LawfulXor.xor_self, zero_mul, add_zero, octSign_4_5, octSign_4_6,
      octSign_4_7, octSign_1_1, octSign_1_4, octSign_2_1, even_two, Nat.xor_one_of_even,
      octSign_2_2, octSign_2_4, octSign_3_1, octSign_3_2, octSign_3_3, octSign_3_4, octSign_5_1,
      octSign_5_2, octSign_5_3, octSign_5_4, octSign_5_5, octSign_6_1, octSign_6_2, octSign_6_3,
      octSign_6_4, octSign_6_5, octSign_6_6, octSign_7_1, octSign_7_2, octSign_7_3, octSign_7_4,
      octSign_7_5, octSign_7_6, octSign_7_7]
  ring

private theorem adjPf_5 (y x w : ℕ → R) :
    (-1) ^ (5 - 1) * Matrix.pfaffianAux (fun a b => crossMat y a b + wedge x w a b)
      ((List.range' 1 7).erase 5) = adjRhs y x w 5 := by
  rw [show (List.range' 1 7).erase 5 = [1, 2, 3, 4, 6, 7] from rfl,
    Matrix.pfaffianAux_six_indices]
  simp only [Nat.add_one_sub_one, crossMat, octSign_1_2, Int.reduceNeg, Int.cast_neg, Int.cast_one,
      Nat.reduceXor, neg_mul, one_mul, wedge, octSign_3_4, octSign_6_7, octSign_3_6, octSign_4_7,
      octSign_3_7, octSign_4_6, octSign_1_3, octSign_2_4, octSign_2_6, octSign_2_7, octSign_1_4,
      octSign_2_3, octSign_1_6, octSign_1_7, adjRhs, dot7, Finset.sum_range_succ, Finset.range_one,
      Finset.sum_singleton, zero_add, Nat.reduceAdd, cross, octSign_5_1, octSign_5_2, octSign_5_3,
      octSign_5_4, octSign_5_5, Int.cast_zero, LawfulXor.xor_self, zero_mul, add_zero, octSign_5_6,
      octSign_5_7, octSign_1_1, octSign_1_5, octSign_2_1, even_two, Nat.xor_one_of_even,
      octSign_2_2, octSign_2_5, octSign_3_1, octSign_3_2, octSign_3_3, octSign_3_5, octSign_4_1,
      octSign_4_2, octSign_4_3, octSign_4_4, octSign_4_5, octSign_6_1, octSign_6_2, octSign_6_3,
      octSign_6_4, octSign_6_5, octSign_6_6, octSign_7_1, octSign_7_2, octSign_7_3, octSign_7_4,
      octSign_7_5, octSign_7_6, octSign_7_7]
  ring

private theorem adjPf_6 (y x w : ℕ → R) :
    (-1) ^ (6 - 1) * Matrix.pfaffianAux (fun a b => crossMat y a b + wedge x w a b)
      ((List.range' 1 7).erase 6) = adjRhs y x w 6 := by
  rw [show (List.range' 1 7).erase 6 = [1, 2, 3, 4, 5, 7] from rfl,
    Matrix.pfaffianAux_six_indices]
  simp only [Nat.add_one_sub_one, crossMat, octSign_1_2, Int.reduceNeg, Int.cast_neg, Int.cast_one,
      Nat.reduceXor, neg_mul, one_mul, wedge, octSign_3_4, octSign_5_7, octSign_3_5, octSign_4_7,
      octSign_3_7, octSign_4_5, octSign_1_3, octSign_2_4, octSign_2_5, octSign_2_7, octSign_1_4,
      octSign_2_3, octSign_1_5, octSign_1_7, adjRhs, dot7, Finset.sum_range_succ, Finset.range_one,
      Finset.sum_singleton, zero_add, Nat.reduceAdd, cross, octSign_6_1, octSign_6_2, octSign_6_3,
      octSign_6_4, octSign_6_5, octSign_6_6, Int.cast_zero, LawfulXor.xor_self, zero_mul, add_zero,
      octSign_6_7, octSign_1_1, octSign_1_6, octSign_2_1, even_two, Nat.xor_one_of_even,
      octSign_2_2, octSign_2_6, octSign_3_1, octSign_3_2, octSign_3_3, octSign_3_6, octSign_4_1,
      octSign_4_2, octSign_4_3, octSign_4_4, octSign_4_6, octSign_5_1, octSign_5_2, octSign_5_3,
      octSign_5_4, octSign_5_5, octSign_5_6, octSign_7_1, octSign_7_2, octSign_7_3, octSign_7_4,
      octSign_7_5, octSign_7_6, octSign_7_7]
  ring

private theorem adjPf_7 (y x w : ℕ → R) :
    (-1) ^ (7 - 1) * Matrix.pfaffianAux (fun a b => crossMat y a b + wedge x w a b)
      ((List.range' 1 7).erase 7) = adjRhs y x w 7 := by
  rw [show (List.range' 1 7).erase 7 = [1, 2, 3, 4, 5, 6] from rfl,
    Matrix.pfaffianAux_six_indices]
  simp only [Nat.add_one_sub_one, crossMat, octSign_1_2, Int.reduceNeg, Int.cast_neg, Int.cast_one,
      Nat.reduceXor, neg_mul, one_mul, wedge, octSign_3_4, octSign_5_6, octSign_3_5, octSign_4_6,
      octSign_3_6, octSign_4_5, octSign_1_3, octSign_2_4, octSign_2_5, octSign_2_6, octSign_1_4,
      octSign_2_3, octSign_1_5, octSign_1_6, adjRhs, dot7, Finset.sum_range_succ, Finset.range_one,
      Finset.sum_singleton, zero_add, Nat.reduceAdd, cross, octSign_7_1, octSign_7_2, octSign_7_3,
      octSign_7_4, octSign_7_5, octSign_7_6, octSign_7_7, Int.cast_zero, LawfulXor.xor_self,
      zero_mul, add_zero, octSign_1_1, octSign_1_7, octSign_2_1, even_two, Nat.xor_one_of_even,
      octSign_2_2, octSign_2_7, octSign_3_1, octSign_3_2, octSign_3_3, octSign_3_7, octSign_4_1,
      octSign_4_2, octSign_4_3, octSign_4_4, octSign_4_7, octSign_5_1, octSign_5_2, octSign_5_3,
      octSign_5_4, octSign_5_5, octSign_5_7, octSign_6_1, octSign_6_2, octSign_6_3, octSign_6_4,
      octSign_6_5, octSign_6_6, octSign_6_7]
  ring

/-- The Pfaffian adjugate of the cross-product matrix plus a rank-two term: each six-index
Pfaffian expands into the fifteen products of its matching, and the products that carry the
rank-two term twice cancel, leaving one cubic and one bilinear vector expression in `y`. -/
theorem adjPf_crossMat_add_wedge (y x w : ℕ → R) {f : ℕ} (h1 : 1 ≤ f) (h7 : f ≤ 7) :
    (-1) ^ (f - 1) * Matrix.pfaffianAux (fun a b => crossMat y a b + wedge x w a b)
      ((List.range' 1 7).erase f) = adjRhs y x w f := by
  interval_cases f
  · exact adjPf_1 y x w
  · exact adjPf_2 y x w
  · exact adjPf_3 y x w
  · exact adjPf_4 y x w
  · exact adjPf_5 y x w
  · exact adjPf_6 y x w
  · exact adjPf_7 y x w

end PfaffianCross
