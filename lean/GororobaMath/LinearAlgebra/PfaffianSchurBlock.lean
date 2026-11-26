/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.LinearAlgebra.PfaffianSchur

/-!
# The Schur block of the bordered sixteen-by-sixteen matrix and its Pfaffian adjugate

Convention: `borderedA z t` is the matrix of `GororobaMath.LinearAlgebra.PfaffianSixteen`, whose
entry `(a, b)` for nonzero `a ≠ b` is `Tower.sign 4 (a ^^^ b) b * z (a ^^^ b)`; `sedSign a b` is
that sign for `a, b < 16` (`sedSign_eq_sign`) and `0` on the diagonal. Rows and columns
`8, ..., 15` carry the block `B` of right multiplication by `u` on the second octonion half, and
`schurN z t f g = U * A f g - ∑ i, ∑ j, A (i + 8) f * A (i + 8) (j + 8) * A (j + 8) g` (`i, j < 8`)
is the Schur complement `U D - Xᵀ B X` of `B` on the indices `1, ..., 7`, with `U = uv z`.

## Main results

* `PfaffianSchurBlock.schurN_eq`: on `1, ..., 7` the Schur block is
  `crossMat (aV z) + wedge (xV z) (vV z)`.
* `PfaffianSchurBlock.adjPf_schurN`: `(-1) ^ (f - 1)` times the six-index Pfaffian of the Schur
  block without `f` is `U Q G z_f` for `f = 1, ..., 7`, over every commutative ring.
-/

@[expose] public section

namespace PfaffianSchurBlock

open PfaffianCross PfaffianSixteen PfaffianSchur

/-- The sedenion sign table: the coefficient of `e_a` in `e_(a xor b) * e_b` for `a ≠ b` below
`16`, and `0` elsewhere. -/
def sedSign : ℕ → ℕ → ℤ
  | 0, 0 => 0
  | 0, 1 => -1
  | 0, 2 => -1
  | 0, 3 => -1
  | 0, 4 => -1
  | 0, 5 => -1
  | 0, 6 => -1
  | 0, 7 => -1
  | 0, 8 => -1
  | 0, 9 => -1
  | 0, 10 => -1
  | 0, 11 => -1
  | 0, 12 => -1
  | 0, 13 => -1
  | 0, 14 => -1
  | 0, 15 => -1
  | 1, 0 => 1
  | 1, 1 => 0
  | 1, 2 => -1
  | 1, 3 => 1
  | 1, 4 => -1
  | 1, 5 => 1
  | 1, 6 => 1
  | 1, 7 => -1
  | 1, 8 => -1
  | 1, 9 => 1
  | 1, 10 => 1
  | 1, 11 => -1
  | 1, 12 => 1
  | 1, 13 => -1
  | 1, 14 => -1
  | 1, 15 => 1
  | 2, 0 => 1
  | 2, 1 => 1
  | 2, 2 => 0
  | 2, 3 => -1
  | 2, 4 => -1
  | 2, 5 => -1
  | 2, 6 => 1
  | 2, 7 => 1
  | 2, 8 => -1
  | 2, 9 => -1
  | 2, 10 => 1
  | 2, 11 => 1
  | 2, 12 => 1
  | 2, 13 => 1
  | 2, 14 => -1
  | 2, 15 => -1
  | 3, 0 => 1
  | 3, 1 => -1
  | 3, 2 => 1
  | 3, 3 => 0
  | 3, 4 => -1
  | 3, 5 => 1
  | 3, 6 => -1
  | 3, 7 => 1
  | 3, 8 => -1
  | 3, 9 => 1
  | 3, 10 => -1
  | 3, 11 => 1
  | 3, 12 => 1
  | 3, 13 => -1
  | 3, 14 => 1
  | 3, 15 => -1
  | 4, 0 => 1
  | 4, 1 => 1
  | 4, 2 => 1
  | 4, 3 => 1
  | 4, 4 => 0
  | 4, 5 => -1
  | 4, 6 => -1
  | 4, 7 => -1
  | 4, 8 => -1
  | 4, 9 => -1
  | 4, 10 => -1
  | 4, 11 => -1
  | 4, 12 => 1
  | 4, 13 => 1
  | 4, 14 => 1
  | 4, 15 => 1
  | 5, 0 => 1
  | 5, 1 => -1
  | 5, 2 => 1
  | 5, 3 => -1
  | 5, 4 => 1
  | 5, 5 => 0
  | 5, 6 => 1
  | 5, 7 => -1
  | 5, 8 => -1
  | 5, 9 => 1
  | 5, 10 => -1
  | 5, 11 => 1
  | 5, 12 => -1
  | 5, 13 => 1
  | 5, 14 => -1
  | 5, 15 => 1
  | 6, 0 => 1
  | 6, 1 => -1
  | 6, 2 => -1
  | 6, 3 => 1
  | 6, 4 => 1
  | 6, 5 => -1
  | 6, 6 => 0
  | 6, 7 => 1
  | 6, 8 => -1
  | 6, 9 => 1
  | 6, 10 => 1
  | 6, 11 => -1
  | 6, 12 => -1
  | 6, 13 => 1
  | 6, 14 => 1
  | 6, 15 => -1
  | 7, 0 => 1
  | 7, 1 => 1
  | 7, 2 => -1
  | 7, 3 => -1
  | 7, 4 => 1
  | 7, 5 => 1
  | 7, 6 => -1
  | 7, 7 => 0
  | 7, 8 => -1
  | 7, 9 => -1
  | 7, 10 => 1
  | 7, 11 => 1
  | 7, 12 => -1
  | 7, 13 => -1
  | 7, 14 => 1
  | 7, 15 => 1
  | 8, 0 => 1
  | 8, 1 => 1
  | 8, 2 => 1
  | 8, 3 => 1
  | 8, 4 => 1
  | 8, 5 => 1
  | 8, 6 => 1
  | 8, 7 => 1
  | 8, 8 => 0
  | 8, 9 => -1
  | 8, 10 => -1
  | 8, 11 => -1
  | 8, 12 => -1
  | 8, 13 => -1
  | 8, 14 => -1
  | 8, 15 => -1
  | 9, 0 => 1
  | 9, 1 => -1
  | 9, 2 => 1
  | 9, 3 => -1
  | 9, 4 => 1
  | 9, 5 => -1
  | 9, 6 => -1
  | 9, 7 => 1
  | 9, 8 => 1
  | 9, 9 => 0
  | 9, 10 => 1
  | 9, 11 => -1
  | 9, 12 => 1
  | 9, 13 => -1
  | 9, 14 => -1
  | 9, 15 => 1
  | 10, 0 => 1
  | 10, 1 => -1
  | 10, 2 => -1
  | 10, 3 => 1
  | 10, 4 => 1
  | 10, 5 => 1
  | 10, 6 => -1
  | 10, 7 => -1
  | 10, 8 => 1
  | 10, 9 => -1
  | 10, 10 => 0
  | 10, 11 => 1
  | 10, 12 => 1
  | 10, 13 => 1
  | 10, 14 => -1
  | 10, 15 => -1
  | 11, 0 => 1
  | 11, 1 => 1
  | 11, 2 => -1
  | 11, 3 => -1
  | 11, 4 => 1
  | 11, 5 => -1
  | 11, 6 => 1
  | 11, 7 => -1
  | 11, 8 => 1
  | 11, 9 => 1
  | 11, 10 => -1
  | 11, 11 => 0
  | 11, 12 => 1
  | 11, 13 => -1
  | 11, 14 => 1
  | 11, 15 => -1
  | 12, 0 => 1
  | 12, 1 => -1
  | 12, 2 => -1
  | 12, 3 => -1
  | 12, 4 => -1
  | 12, 5 => 1
  | 12, 6 => 1
  | 12, 7 => 1
  | 12, 8 => 1
  | 12, 9 => -1
  | 12, 10 => -1
  | 12, 11 => -1
  | 12, 12 => 0
  | 12, 13 => 1
  | 12, 14 => 1
  | 12, 15 => 1
  | 13, 0 => 1
  | 13, 1 => 1
  | 13, 2 => -1
  | 13, 3 => 1
  | 13, 4 => -1
  | 13, 5 => -1
  | 13, 6 => -1
  | 13, 7 => 1
  | 13, 8 => 1
  | 13, 9 => 1
  | 13, 10 => -1
  | 13, 11 => 1
  | 13, 12 => -1
  | 13, 13 => 0
  | 13, 14 => -1
  | 13, 15 => 1
  | 14, 0 => 1
  | 14, 1 => 1
  | 14, 2 => 1
  | 14, 3 => -1
  | 14, 4 => -1
  | 14, 5 => 1
  | 14, 6 => -1
  | 14, 7 => -1
  | 14, 8 => 1
  | 14, 9 => 1
  | 14, 10 => 1
  | 14, 11 => -1
  | 14, 12 => -1
  | 14, 13 => 1
  | 14, 14 => 0
  | 14, 15 => -1
  | 15, 0 => 1
  | 15, 1 => -1
  | 15, 2 => 1
  | 15, 3 => 1
  | 15, 4 => -1
  | 15, 5 => -1
  | 15, 6 => 1
  | 15, 7 => -1
  | 15, 8 => 1
  | 15, 9 => -1
  | 15, 10 => 1
  | 15, 11 => 1
  | 15, 12 => -1
  | 15, 13 => -1
  | 15, 14 => 1
  | 15, 15 => 0
  | _, _ => 0

theorem sedSign_1_1 : sedSign 1 1 = 0 := rfl
theorem sedSign_1_2 : sedSign 1 2 = -1 := rfl
theorem sedSign_1_3 : sedSign 1 3 = 1 := rfl
theorem sedSign_1_4 : sedSign 1 4 = -1 := rfl
theorem sedSign_1_5 : sedSign 1 5 = 1 := rfl
theorem sedSign_1_6 : sedSign 1 6 = 1 := rfl
theorem sedSign_1_7 : sedSign 1 7 = -1 := rfl
theorem sedSign_1_8 : sedSign 1 8 = -1 := rfl
theorem sedSign_1_9 : sedSign 1 9 = 1 := rfl
theorem sedSign_1_10 : sedSign 1 10 = 1 := rfl
theorem sedSign_1_11 : sedSign 1 11 = -1 := rfl
theorem sedSign_1_12 : sedSign 1 12 = 1 := rfl
theorem sedSign_1_13 : sedSign 1 13 = -1 := rfl
theorem sedSign_1_14 : sedSign 1 14 = -1 := rfl
theorem sedSign_1_15 : sedSign 1 15 = 1 := rfl
theorem sedSign_2_1 : sedSign 2 1 = 1 := rfl
theorem sedSign_2_2 : sedSign 2 2 = 0 := rfl
theorem sedSign_2_3 : sedSign 2 3 = -1 := rfl
theorem sedSign_2_4 : sedSign 2 4 = -1 := rfl
theorem sedSign_2_5 : sedSign 2 5 = -1 := rfl
theorem sedSign_2_6 : sedSign 2 6 = 1 := rfl
theorem sedSign_2_7 : sedSign 2 7 = 1 := rfl
theorem sedSign_2_8 : sedSign 2 8 = -1 := rfl
theorem sedSign_2_9 : sedSign 2 9 = -1 := rfl
theorem sedSign_2_10 : sedSign 2 10 = 1 := rfl
theorem sedSign_2_11 : sedSign 2 11 = 1 := rfl
theorem sedSign_2_12 : sedSign 2 12 = 1 := rfl
theorem sedSign_2_13 : sedSign 2 13 = 1 := rfl
theorem sedSign_2_14 : sedSign 2 14 = -1 := rfl
theorem sedSign_2_15 : sedSign 2 15 = -1 := rfl
theorem sedSign_3_1 : sedSign 3 1 = -1 := rfl
theorem sedSign_3_2 : sedSign 3 2 = 1 := rfl
theorem sedSign_3_3 : sedSign 3 3 = 0 := rfl
theorem sedSign_3_4 : sedSign 3 4 = -1 := rfl
theorem sedSign_3_5 : sedSign 3 5 = 1 := rfl
theorem sedSign_3_6 : sedSign 3 6 = -1 := rfl
theorem sedSign_3_7 : sedSign 3 7 = 1 := rfl
theorem sedSign_3_8 : sedSign 3 8 = -1 := rfl
theorem sedSign_3_9 : sedSign 3 9 = 1 := rfl
theorem sedSign_3_10 : sedSign 3 10 = -1 := rfl
theorem sedSign_3_11 : sedSign 3 11 = 1 := rfl
theorem sedSign_3_12 : sedSign 3 12 = 1 := rfl
theorem sedSign_3_13 : sedSign 3 13 = -1 := rfl
theorem sedSign_3_14 : sedSign 3 14 = 1 := rfl
theorem sedSign_3_15 : sedSign 3 15 = -1 := rfl
theorem sedSign_4_1 : sedSign 4 1 = 1 := rfl
theorem sedSign_4_2 : sedSign 4 2 = 1 := rfl
theorem sedSign_4_3 : sedSign 4 3 = 1 := rfl
theorem sedSign_4_4 : sedSign 4 4 = 0 := rfl
theorem sedSign_4_5 : sedSign 4 5 = -1 := rfl
theorem sedSign_4_6 : sedSign 4 6 = -1 := rfl
theorem sedSign_4_7 : sedSign 4 7 = -1 := rfl
theorem sedSign_4_8 : sedSign 4 8 = -1 := rfl
theorem sedSign_4_9 : sedSign 4 9 = -1 := rfl
theorem sedSign_4_10 : sedSign 4 10 = -1 := rfl
theorem sedSign_4_11 : sedSign 4 11 = -1 := rfl
theorem sedSign_4_12 : sedSign 4 12 = 1 := rfl
theorem sedSign_4_13 : sedSign 4 13 = 1 := rfl
theorem sedSign_4_14 : sedSign 4 14 = 1 := rfl
theorem sedSign_4_15 : sedSign 4 15 = 1 := rfl
theorem sedSign_5_1 : sedSign 5 1 = -1 := rfl
theorem sedSign_5_2 : sedSign 5 2 = 1 := rfl
theorem sedSign_5_3 : sedSign 5 3 = -1 := rfl
theorem sedSign_5_4 : sedSign 5 4 = 1 := rfl
theorem sedSign_5_5 : sedSign 5 5 = 0 := rfl
theorem sedSign_5_6 : sedSign 5 6 = 1 := rfl
theorem sedSign_5_7 : sedSign 5 7 = -1 := rfl
theorem sedSign_5_8 : sedSign 5 8 = -1 := rfl
theorem sedSign_5_9 : sedSign 5 9 = 1 := rfl
theorem sedSign_5_10 : sedSign 5 10 = -1 := rfl
theorem sedSign_5_11 : sedSign 5 11 = 1 := rfl
theorem sedSign_5_12 : sedSign 5 12 = -1 := rfl
theorem sedSign_5_13 : sedSign 5 13 = 1 := rfl
theorem sedSign_5_14 : sedSign 5 14 = -1 := rfl
theorem sedSign_5_15 : sedSign 5 15 = 1 := rfl
theorem sedSign_6_1 : sedSign 6 1 = -1 := rfl
theorem sedSign_6_2 : sedSign 6 2 = -1 := rfl
theorem sedSign_6_3 : sedSign 6 3 = 1 := rfl
theorem sedSign_6_4 : sedSign 6 4 = 1 := rfl
theorem sedSign_6_5 : sedSign 6 5 = -1 := rfl
theorem sedSign_6_6 : sedSign 6 6 = 0 := rfl
theorem sedSign_6_7 : sedSign 6 7 = 1 := rfl
theorem sedSign_6_8 : sedSign 6 8 = -1 := rfl
theorem sedSign_6_9 : sedSign 6 9 = 1 := rfl
theorem sedSign_6_10 : sedSign 6 10 = 1 := rfl
theorem sedSign_6_11 : sedSign 6 11 = -1 := rfl
theorem sedSign_6_12 : sedSign 6 12 = -1 := rfl
theorem sedSign_6_13 : sedSign 6 13 = 1 := rfl
theorem sedSign_6_14 : sedSign 6 14 = 1 := rfl
theorem sedSign_6_15 : sedSign 6 15 = -1 := rfl
theorem sedSign_7_1 : sedSign 7 1 = 1 := rfl
theorem sedSign_7_2 : sedSign 7 2 = -1 := rfl
theorem sedSign_7_3 : sedSign 7 3 = -1 := rfl
theorem sedSign_7_4 : sedSign 7 4 = 1 := rfl
theorem sedSign_7_5 : sedSign 7 5 = 1 := rfl
theorem sedSign_7_6 : sedSign 7 6 = -1 := rfl
theorem sedSign_7_7 : sedSign 7 7 = 0 := rfl
theorem sedSign_7_8 : sedSign 7 8 = -1 := rfl
theorem sedSign_7_9 : sedSign 7 9 = -1 := rfl
theorem sedSign_7_10 : sedSign 7 10 = 1 := rfl
theorem sedSign_7_11 : sedSign 7 11 = 1 := rfl
theorem sedSign_7_12 : sedSign 7 12 = -1 := rfl
theorem sedSign_7_13 : sedSign 7 13 = -1 := rfl
theorem sedSign_7_14 : sedSign 7 14 = 1 := rfl
theorem sedSign_7_15 : sedSign 7 15 = 1 := rfl
theorem sedSign_8_1 : sedSign 8 1 = 1 := rfl
theorem sedSign_8_2 : sedSign 8 2 = 1 := rfl
theorem sedSign_8_3 : sedSign 8 3 = 1 := rfl
theorem sedSign_8_4 : sedSign 8 4 = 1 := rfl
theorem sedSign_8_5 : sedSign 8 5 = 1 := rfl
theorem sedSign_8_6 : sedSign 8 6 = 1 := rfl
theorem sedSign_8_7 : sedSign 8 7 = 1 := rfl
theorem sedSign_8_8 : sedSign 8 8 = 0 := rfl
theorem sedSign_8_9 : sedSign 8 9 = -1 := rfl
theorem sedSign_8_10 : sedSign 8 10 = -1 := rfl
theorem sedSign_8_11 : sedSign 8 11 = -1 := rfl
theorem sedSign_8_12 : sedSign 8 12 = -1 := rfl
theorem sedSign_8_13 : sedSign 8 13 = -1 := rfl
theorem sedSign_8_14 : sedSign 8 14 = -1 := rfl
theorem sedSign_8_15 : sedSign 8 15 = -1 := rfl
theorem sedSign_9_1 : sedSign 9 1 = -1 := rfl
theorem sedSign_9_2 : sedSign 9 2 = 1 := rfl
theorem sedSign_9_3 : sedSign 9 3 = -1 := rfl
theorem sedSign_9_4 : sedSign 9 4 = 1 := rfl
theorem sedSign_9_5 : sedSign 9 5 = -1 := rfl
theorem sedSign_9_6 : sedSign 9 6 = -1 := rfl
theorem sedSign_9_7 : sedSign 9 7 = 1 := rfl
theorem sedSign_9_8 : sedSign 9 8 = 1 := rfl
theorem sedSign_9_9 : sedSign 9 9 = 0 := rfl
theorem sedSign_9_10 : sedSign 9 10 = 1 := rfl
theorem sedSign_9_11 : sedSign 9 11 = -1 := rfl
theorem sedSign_9_12 : sedSign 9 12 = 1 := rfl
theorem sedSign_9_13 : sedSign 9 13 = -1 := rfl
theorem sedSign_9_14 : sedSign 9 14 = -1 := rfl
theorem sedSign_9_15 : sedSign 9 15 = 1 := rfl
theorem sedSign_10_1 : sedSign 10 1 = -1 := rfl
theorem sedSign_10_2 : sedSign 10 2 = -1 := rfl
theorem sedSign_10_3 : sedSign 10 3 = 1 := rfl
theorem sedSign_10_4 : sedSign 10 4 = 1 := rfl
theorem sedSign_10_5 : sedSign 10 5 = 1 := rfl
theorem sedSign_10_6 : sedSign 10 6 = -1 := rfl
theorem sedSign_10_7 : sedSign 10 7 = -1 := rfl
theorem sedSign_10_8 : sedSign 10 8 = 1 := rfl
theorem sedSign_10_9 : sedSign 10 9 = -1 := rfl
theorem sedSign_10_10 : sedSign 10 10 = 0 := rfl
theorem sedSign_10_11 : sedSign 10 11 = 1 := rfl
theorem sedSign_10_12 : sedSign 10 12 = 1 := rfl
theorem sedSign_10_13 : sedSign 10 13 = 1 := rfl
theorem sedSign_10_14 : sedSign 10 14 = -1 := rfl
theorem sedSign_10_15 : sedSign 10 15 = -1 := rfl
theorem sedSign_11_1 : sedSign 11 1 = 1 := rfl
theorem sedSign_11_2 : sedSign 11 2 = -1 := rfl
theorem sedSign_11_3 : sedSign 11 3 = -1 := rfl
theorem sedSign_11_4 : sedSign 11 4 = 1 := rfl
theorem sedSign_11_5 : sedSign 11 5 = -1 := rfl
theorem sedSign_11_6 : sedSign 11 6 = 1 := rfl
theorem sedSign_11_7 : sedSign 11 7 = -1 := rfl
theorem sedSign_11_8 : sedSign 11 8 = 1 := rfl
theorem sedSign_11_9 : sedSign 11 9 = 1 := rfl
theorem sedSign_11_10 : sedSign 11 10 = -1 := rfl
theorem sedSign_11_11 : sedSign 11 11 = 0 := rfl
theorem sedSign_11_12 : sedSign 11 12 = 1 := rfl
theorem sedSign_11_13 : sedSign 11 13 = -1 := rfl
theorem sedSign_11_14 : sedSign 11 14 = 1 := rfl
theorem sedSign_11_15 : sedSign 11 15 = -1 := rfl
theorem sedSign_12_1 : sedSign 12 1 = -1 := rfl
theorem sedSign_12_2 : sedSign 12 2 = -1 := rfl
theorem sedSign_12_3 : sedSign 12 3 = -1 := rfl
theorem sedSign_12_4 : sedSign 12 4 = -1 := rfl
theorem sedSign_12_5 : sedSign 12 5 = 1 := rfl
theorem sedSign_12_6 : sedSign 12 6 = 1 := rfl
theorem sedSign_12_7 : sedSign 12 7 = 1 := rfl
theorem sedSign_12_8 : sedSign 12 8 = 1 := rfl
theorem sedSign_12_9 : sedSign 12 9 = -1 := rfl
theorem sedSign_12_10 : sedSign 12 10 = -1 := rfl
theorem sedSign_12_11 : sedSign 12 11 = -1 := rfl
theorem sedSign_12_12 : sedSign 12 12 = 0 := rfl
theorem sedSign_12_13 : sedSign 12 13 = 1 := rfl
theorem sedSign_12_14 : sedSign 12 14 = 1 := rfl
theorem sedSign_12_15 : sedSign 12 15 = 1 := rfl
theorem sedSign_13_1 : sedSign 13 1 = 1 := rfl
theorem sedSign_13_2 : sedSign 13 2 = -1 := rfl
theorem sedSign_13_3 : sedSign 13 3 = 1 := rfl
theorem sedSign_13_4 : sedSign 13 4 = -1 := rfl
theorem sedSign_13_5 : sedSign 13 5 = -1 := rfl
theorem sedSign_13_6 : sedSign 13 6 = -1 := rfl
theorem sedSign_13_7 : sedSign 13 7 = 1 := rfl
theorem sedSign_13_8 : sedSign 13 8 = 1 := rfl
theorem sedSign_13_9 : sedSign 13 9 = 1 := rfl
theorem sedSign_13_10 : sedSign 13 10 = -1 := rfl
theorem sedSign_13_11 : sedSign 13 11 = 1 := rfl
theorem sedSign_13_12 : sedSign 13 12 = -1 := rfl
theorem sedSign_13_13 : sedSign 13 13 = 0 := rfl
theorem sedSign_13_14 : sedSign 13 14 = -1 := rfl
theorem sedSign_13_15 : sedSign 13 15 = 1 := rfl
theorem sedSign_14_1 : sedSign 14 1 = 1 := rfl
theorem sedSign_14_2 : sedSign 14 2 = 1 := rfl
theorem sedSign_14_3 : sedSign 14 3 = -1 := rfl
theorem sedSign_14_4 : sedSign 14 4 = -1 := rfl
theorem sedSign_14_5 : sedSign 14 5 = 1 := rfl
theorem sedSign_14_6 : sedSign 14 6 = -1 := rfl
theorem sedSign_14_7 : sedSign 14 7 = -1 := rfl
theorem sedSign_14_8 : sedSign 14 8 = 1 := rfl
theorem sedSign_14_9 : sedSign 14 9 = 1 := rfl
theorem sedSign_14_10 : sedSign 14 10 = 1 := rfl
theorem sedSign_14_11 : sedSign 14 11 = -1 := rfl
theorem sedSign_14_12 : sedSign 14 12 = -1 := rfl
theorem sedSign_14_13 : sedSign 14 13 = 1 := rfl
theorem sedSign_14_14 : sedSign 14 14 = 0 := rfl
theorem sedSign_14_15 : sedSign 14 15 = -1 := rfl
theorem sedSign_15_1 : sedSign 15 1 = -1 := rfl
theorem sedSign_15_2 : sedSign 15 2 = 1 := rfl
theorem sedSign_15_3 : sedSign 15 3 = 1 := rfl
theorem sedSign_15_4 : sedSign 15 4 = -1 := rfl
theorem sedSign_15_5 : sedSign 15 5 = -1 := rfl
theorem sedSign_15_6 : sedSign 15 6 = 1 := rfl
theorem sedSign_15_7 : sedSign 15 7 = -1 := rfl
theorem sedSign_15_8 : sedSign 15 8 = 1 := rfl
theorem sedSign_15_9 : sedSign 15 9 = -1 := rfl
theorem sedSign_15_10 : sedSign 15 10 = 1 := rfl
theorem sedSign_15_11 : sedSign 15 11 = 1 := rfl
theorem sedSign_15_12 : sedSign 15 12 = -1 := rfl
theorem sedSign_15_13 : sedSign 15 13 = -1 := rfl
theorem sedSign_15_14 : sedSign 15 14 = 1 := rfl
theorem sedSign_15_15 : sedSign 15 15 = 0 := rfl

/-- The table agrees with the level-4 sign of the tower off the diagonal. -/
theorem sedSign_eq_sign {a b : ℕ} (ha : 1 ≤ a) (ha16 : a < 16) (hb : 1 ≤ b) (hb16 : b < 16)
    (hab : a ≠ b) :
    sedSign a b = CayleyDickson.Tower.sign 4 (BitVec.ofNat 4 (a ^^^ b)) (BitVec.ofNat 4 b) := by
  interval_cases a <;> interval_cases b <;> first | exact absurd rfl hab | decide +kernel

variable {R : Type*} [CommRing R]

/-- The diagonal of the bordered matrix is `0`. -/
theorem borderedA_self (z t : ℕ → R) (a : ℕ) : borderedA z t a a = 0 := by
  simp [borderedA]

/-- Off the diagonal and away from the border the entry is the table sign times `z (a ^^^ b)`. -/
theorem borderedA_of_pos (z t : ℕ → R) {a b : ℕ} (ha : 1 ≤ a) (ha16 : a < 16) (hb : 1 ≤ b)
    (hb16 : b < 16) (hab : a ≠ b) : borderedA z t a b = (sedSign a b : R) * z (a ^^^ b) := by
  rw [sedSign_eq_sign ha ha16 hb hb16 hab]
  simp [borderedA, hab, show a ≠ 0 by omega, show b ≠ 0 by omega]

/-- The Schur complement `U D - Xᵀ B X` of the block on `8, ..., 15`. -/
def schurN (z t : ℕ → R) (f g : ℕ) : R :=
  uv z * borderedA z t f g - ∑ i ∈ Finset.range 8, ∑ j ∈ Finset.range 8,
    borderedA z t (i + 8) f * borderedA z t (i + 8) (j + 8) * borderedA z t (j + 8) g

attribute [local simp]
  sedSign_1_1 sedSign_1_2 sedSign_1_3 sedSign_1_4
  sedSign_1_5 sedSign_1_6 sedSign_1_7 sedSign_1_8
  sedSign_1_9 sedSign_1_10 sedSign_1_11 sedSign_1_12
  sedSign_1_13 sedSign_1_14 sedSign_1_15 sedSign_2_1
  sedSign_2_2 sedSign_2_3 sedSign_2_4 sedSign_2_5
  sedSign_2_6 sedSign_2_7 sedSign_2_8 sedSign_2_9
  sedSign_2_10 sedSign_2_11 sedSign_2_12 sedSign_2_13
  sedSign_2_14 sedSign_2_15 sedSign_3_1 sedSign_3_2
  sedSign_3_3 sedSign_3_4 sedSign_3_5 sedSign_3_6
  sedSign_3_7 sedSign_3_8 sedSign_3_9 sedSign_3_10
  sedSign_3_11 sedSign_3_12 sedSign_3_13 sedSign_3_14
  sedSign_3_15 sedSign_4_1 sedSign_4_2 sedSign_4_3
  sedSign_4_4 sedSign_4_5 sedSign_4_6 sedSign_4_7
  sedSign_4_8 sedSign_4_9 sedSign_4_10 sedSign_4_11
  sedSign_4_12 sedSign_4_13 sedSign_4_14 sedSign_4_15
  sedSign_5_1 sedSign_5_2 sedSign_5_3 sedSign_5_4
  sedSign_5_5 sedSign_5_6 sedSign_5_7 sedSign_5_8
  sedSign_5_9 sedSign_5_10 sedSign_5_11 sedSign_5_12
  sedSign_5_13 sedSign_5_14 sedSign_5_15 sedSign_6_1
  sedSign_6_2 sedSign_6_3 sedSign_6_4 sedSign_6_5
  sedSign_6_6 sedSign_6_7 sedSign_6_8 sedSign_6_9
  sedSign_6_10 sedSign_6_11 sedSign_6_12 sedSign_6_13
  sedSign_6_14 sedSign_6_15 sedSign_7_1 sedSign_7_2
  sedSign_7_3 sedSign_7_4 sedSign_7_5 sedSign_7_6
  sedSign_7_7 sedSign_7_8 sedSign_7_9 sedSign_7_10
  sedSign_7_11 sedSign_7_12 sedSign_7_13 sedSign_7_14
  sedSign_7_15 sedSign_8_1 sedSign_8_2 sedSign_8_3
  sedSign_8_4 sedSign_8_5 sedSign_8_6 sedSign_8_7
  sedSign_8_8 sedSign_8_9 sedSign_8_10 sedSign_8_11
  sedSign_8_12 sedSign_8_13 sedSign_8_14 sedSign_8_15
  sedSign_9_1 sedSign_9_2 sedSign_9_3 sedSign_9_4
  sedSign_9_5 sedSign_9_6 sedSign_9_7 sedSign_9_8
  sedSign_9_9 sedSign_9_10 sedSign_9_11 sedSign_9_12
  sedSign_9_13 sedSign_9_14 sedSign_9_15 sedSign_10_1
  sedSign_10_2 sedSign_10_3 sedSign_10_4 sedSign_10_5
  sedSign_10_6 sedSign_10_7 sedSign_10_8 sedSign_10_9
  sedSign_10_10 sedSign_10_11 sedSign_10_12 sedSign_10_13
  sedSign_10_14 sedSign_10_15 sedSign_11_1 sedSign_11_2
  sedSign_11_3 sedSign_11_4 sedSign_11_5 sedSign_11_6
  sedSign_11_7 sedSign_11_8 sedSign_11_9 sedSign_11_10
  sedSign_11_11 sedSign_11_12 sedSign_11_13 sedSign_11_14
  sedSign_11_15 sedSign_12_1 sedSign_12_2 sedSign_12_3
  sedSign_12_4 sedSign_12_5 sedSign_12_6 sedSign_12_7
  sedSign_12_8 sedSign_12_9 sedSign_12_10 sedSign_12_11
  sedSign_12_12 sedSign_12_13 sedSign_12_14 sedSign_12_15
  sedSign_13_1 sedSign_13_2 sedSign_13_3 sedSign_13_4
  sedSign_13_5 sedSign_13_6 sedSign_13_7 sedSign_13_8
  sedSign_13_9 sedSign_13_10 sedSign_13_11 sedSign_13_12
  sedSign_13_13 sedSign_13_14 sedSign_13_15 sedSign_14_1
  sedSign_14_2 sedSign_14_3 sedSign_14_4 sedSign_14_5
  sedSign_14_6 sedSign_14_7 sedSign_14_8 sedSign_14_9
  sedSign_14_10 sedSign_14_11 sedSign_14_12 sedSign_14_13
  sedSign_14_14 sedSign_14_15 sedSign_15_1 sedSign_15_2
  sedSign_15_3 sedSign_15_4 sedSign_15_5 sedSign_15_6
  sedSign_15_7 sedSign_15_8 sedSign_15_9 sedSign_15_10
  sedSign_15_11 sedSign_15_12 sedSign_15_13 sedSign_15_14
  sedSign_15_15
  PfaffianCross.octSign_1_1 PfaffianCross.octSign_1_2 PfaffianCross.octSign_1_3
  PfaffianCross.octSign_1_4 PfaffianCross.octSign_1_5 PfaffianCross.octSign_1_6
  PfaffianCross.octSign_1_7 PfaffianCross.octSign_2_1 PfaffianCross.octSign_2_2
  PfaffianCross.octSign_2_3 PfaffianCross.octSign_2_4 PfaffianCross.octSign_2_5
  PfaffianCross.octSign_2_6 PfaffianCross.octSign_2_7 PfaffianCross.octSign_3_1
  PfaffianCross.octSign_3_2 PfaffianCross.octSign_3_3 PfaffianCross.octSign_3_4
  PfaffianCross.octSign_3_5 PfaffianCross.octSign_3_6 PfaffianCross.octSign_3_7
  PfaffianCross.octSign_4_1 PfaffianCross.octSign_4_2 PfaffianCross.octSign_4_3
  PfaffianCross.octSign_4_4 PfaffianCross.octSign_4_5 PfaffianCross.octSign_4_6
  PfaffianCross.octSign_4_7 PfaffianCross.octSign_5_1 PfaffianCross.octSign_5_2
  PfaffianCross.octSign_5_3 PfaffianCross.octSign_5_4 PfaffianCross.octSign_5_5
  PfaffianCross.octSign_5_6 PfaffianCross.octSign_5_7 PfaffianCross.octSign_6_1
  PfaffianCross.octSign_6_2 PfaffianCross.octSign_6_3 PfaffianCross.octSign_6_4
  PfaffianCross.octSign_6_5 PfaffianCross.octSign_6_6 PfaffianCross.octSign_6_7
  PfaffianCross.octSign_7_1 PfaffianCross.octSign_7_2 PfaffianCross.octSign_7_3
  PfaffianCross.octSign_7_4 PfaffianCross.octSign_7_5 PfaffianCross.octSign_7_6
  PfaffianCross.octSign_7_7

private theorem schurN_1_1 (z t : ℕ → R) :
    schurN z t 1 1 = crossMat (aV z) 1 1 + wedge (xV z) (vV z) 1 1 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_1_2 (z t : ℕ → R) :
    schurN z t 1 2 = crossMat (aV z) 1 2 + wedge (xV z) (vV z) 1 2 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_1_3 (z t : ℕ → R) :
    schurN z t 1 3 = crossMat (aV z) 1 3 + wedge (xV z) (vV z) 1 3 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_1_4 (z t : ℕ → R) :
    schurN z t 1 4 = crossMat (aV z) 1 4 + wedge (xV z) (vV z) 1 4 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_1_5 (z t : ℕ → R) :
    schurN z t 1 5 = crossMat (aV z) 1 5 + wedge (xV z) (vV z) 1 5 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_1_6 (z t : ℕ → R) :
    schurN z t 1 6 = crossMat (aV z) 1 6 + wedge (xV z) (vV z) 1 6 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_1_7 (z t : ℕ → R) :
    schurN z t 1 7 = crossMat (aV z) 1 7 + wedge (xV z) (vV z) 1 7 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_2_1 (z t : ℕ → R) :
    schurN z t 2 1 = crossMat (aV z) 2 1 + wedge (xV z) (vV z) 2 1 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_2_2 (z t : ℕ → R) :
    schurN z t 2 2 = crossMat (aV z) 2 2 + wedge (xV z) (vV z) 2 2 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_2_3 (z t : ℕ → R) :
    schurN z t 2 3 = crossMat (aV z) 2 3 + wedge (xV z) (vV z) 2 3 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_2_4 (z t : ℕ → R) :
    schurN z t 2 4 = crossMat (aV z) 2 4 + wedge (xV z) (vV z) 2 4 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_2_5 (z t : ℕ → R) :
    schurN z t 2 5 = crossMat (aV z) 2 5 + wedge (xV z) (vV z) 2 5 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_2_6 (z t : ℕ → R) :
    schurN z t 2 6 = crossMat (aV z) 2 6 + wedge (xV z) (vV z) 2 6 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_2_7 (z t : ℕ → R) :
    schurN z t 2 7 = crossMat (aV z) 2 7 + wedge (xV z) (vV z) 2 7 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_3_1 (z t : ℕ → R) :
    schurN z t 3 1 = crossMat (aV z) 3 1 + wedge (xV z) (vV z) 3 1 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_3_2 (z t : ℕ → R) :
    schurN z t 3 2 = crossMat (aV z) 3 2 + wedge (xV z) (vV z) 3 2 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_3_3 (z t : ℕ → R) :
    schurN z t 3 3 = crossMat (aV z) 3 3 + wedge (xV z) (vV z) 3 3 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_3_4 (z t : ℕ → R) :
    schurN z t 3 4 = crossMat (aV z) 3 4 + wedge (xV z) (vV z) 3 4 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_3_5 (z t : ℕ → R) :
    schurN z t 3 5 = crossMat (aV z) 3 5 + wedge (xV z) (vV z) 3 5 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_3_6 (z t : ℕ → R) :
    schurN z t 3 6 = crossMat (aV z) 3 6 + wedge (xV z) (vV z) 3 6 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_3_7 (z t : ℕ → R) :
    schurN z t 3 7 = crossMat (aV z) 3 7 + wedge (xV z) (vV z) 3 7 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_4_1 (z t : ℕ → R) :
    schurN z t 4 1 = crossMat (aV z) 4 1 + wedge (xV z) (vV z) 4 1 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_4_2 (z t : ℕ → R) :
    schurN z t 4 2 = crossMat (aV z) 4 2 + wedge (xV z) (vV z) 4 2 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_4_3 (z t : ℕ → R) :
    schurN z t 4 3 = crossMat (aV z) 4 3 + wedge (xV z) (vV z) 4 3 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_4_4 (z t : ℕ → R) :
    schurN z t 4 4 = crossMat (aV z) 4 4 + wedge (xV z) (vV z) 4 4 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_4_5 (z t : ℕ → R) :
    schurN z t 4 5 = crossMat (aV z) 4 5 + wedge (xV z) (vV z) 4 5 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_4_6 (z t : ℕ → R) :
    schurN z t 4 6 = crossMat (aV z) 4 6 + wedge (xV z) (vV z) 4 6 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_4_7 (z t : ℕ → R) :
    schurN z t 4 7 = crossMat (aV z) 4 7 + wedge (xV z) (vV z) 4 7 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_5_1 (z t : ℕ → R) :
    schurN z t 5 1 = crossMat (aV z) 5 1 + wedge (xV z) (vV z) 5 1 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_5_2 (z t : ℕ → R) :
    schurN z t 5 2 = crossMat (aV z) 5 2 + wedge (xV z) (vV z) 5 2 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_5_3 (z t : ℕ → R) :
    schurN z t 5 3 = crossMat (aV z) 5 3 + wedge (xV z) (vV z) 5 3 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_5_4 (z t : ℕ → R) :
    schurN z t 5 4 = crossMat (aV z) 5 4 + wedge (xV z) (vV z) 5 4 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_5_5 (z t : ℕ → R) :
    schurN z t 5 5 = crossMat (aV z) 5 5 + wedge (xV z) (vV z) 5 5 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_5_6 (z t : ℕ → R) :
    schurN z t 5 6 = crossMat (aV z) 5 6 + wedge (xV z) (vV z) 5 6 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_5_7 (z t : ℕ → R) :
    schurN z t 5 7 = crossMat (aV z) 5 7 + wedge (xV z) (vV z) 5 7 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_6_1 (z t : ℕ → R) :
    schurN z t 6 1 = crossMat (aV z) 6 1 + wedge (xV z) (vV z) 6 1 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_6_2 (z t : ℕ → R) :
    schurN z t 6 2 = crossMat (aV z) 6 2 + wedge (xV z) (vV z) 6 2 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_6_3 (z t : ℕ → R) :
    schurN z t 6 3 = crossMat (aV z) 6 3 + wedge (xV z) (vV z) 6 3 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_6_4 (z t : ℕ → R) :
    schurN z t 6 4 = crossMat (aV z) 6 4 + wedge (xV z) (vV z) 6 4 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_6_5 (z t : ℕ → R) :
    schurN z t 6 5 = crossMat (aV z) 6 5 + wedge (xV z) (vV z) 6 5 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_6_6 (z t : ℕ → R) :
    schurN z t 6 6 = crossMat (aV z) 6 6 + wedge (xV z) (vV z) 6 6 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_6_7 (z t : ℕ → R) :
    schurN z t 6 7 = crossMat (aV z) 6 7 + wedge (xV z) (vV z) 6 7 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_7_1 (z t : ℕ → R) :
    schurN z t 7 1 = crossMat (aV z) 7 1 + wedge (xV z) (vV z) 7 1 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_7_2 (z t : ℕ → R) :
    schurN z t 7 2 = crossMat (aV z) 7 2 + wedge (xV z) (vV z) 7 2 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_7_3 (z t : ℕ → R) :
    schurN z t 7 3 = crossMat (aV z) 7 3 + wedge (xV z) (vV z) 7 3 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_7_4 (z t : ℕ → R) :
    schurN z t 7 4 = crossMat (aV z) 7 4 + wedge (xV z) (vV z) 7 4 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_7_5 (z t : ℕ → R) :
    schurN z t 7 5 = crossMat (aV z) 7 5 + wedge (xV z) (vV z) 7 5 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_7_6 (z t : ℕ → R) :
    schurN z t 7 6 = crossMat (aV z) 7 6 + wedge (xV z) (vV z) 7 6 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

private theorem schurN_7_7 (z t : ℕ → R) :
    schurN z t 7 7 = crossMat (aV z) 7 7 + wedge (xV z) (vV z) 7 7 := by
  simp [schurN, Finset.sum_range_succ, borderedA_self, borderedA_of_pos, crossMat, wedge, aV, xV,
    mV, vV, cross, uv, vv, wv]
  ring

/-- On `1, ..., 7` the Schur block is `crossMat a + wedge x v`, entry by entry. -/
theorem schurN_eq (z t : ℕ → R) {f g : ℕ} (hf : 1 ≤ f) (hf7 : f ≤ 7) (hg : 1 ≤ g) (hg7 : g ≤ 7) :
    schurN z t f g = crossMat (aV z) f g + wedge (xV z) (vV z) f g := by
  interval_cases f
  · interval_cases g
    · exact schurN_1_1 z t
    · exact schurN_1_2 z t
    · exact schurN_1_3 z t
    · exact schurN_1_4 z t
    · exact schurN_1_5 z t
    · exact schurN_1_6 z t
    · exact schurN_1_7 z t
  · interval_cases g
    · exact schurN_2_1 z t
    · exact schurN_2_2 z t
    · exact schurN_2_3 z t
    · exact schurN_2_4 z t
    · exact schurN_2_5 z t
    · exact schurN_2_6 z t
    · exact schurN_2_7 z t
  · interval_cases g
    · exact schurN_3_1 z t
    · exact schurN_3_2 z t
    · exact schurN_3_3 z t
    · exact schurN_3_4 z t
    · exact schurN_3_5 z t
    · exact schurN_3_6 z t
    · exact schurN_3_7 z t
  · interval_cases g
    · exact schurN_4_1 z t
    · exact schurN_4_2 z t
    · exact schurN_4_3 z t
    · exact schurN_4_4 z t
    · exact schurN_4_5 z t
    · exact schurN_4_6 z t
    · exact schurN_4_7 z t
  · interval_cases g
    · exact schurN_5_1 z t
    · exact schurN_5_2 z t
    · exact schurN_5_3 z t
    · exact schurN_5_4 z t
    · exact schurN_5_5 z t
    · exact schurN_5_6 z t
    · exact schurN_5_7 z t
  · interval_cases g
    · exact schurN_6_1 z t
    · exact schurN_6_2 z t
    · exact schurN_6_3 z t
    · exact schurN_6_4 z t
    · exact schurN_6_5 z t
    · exact schurN_6_6 z t
    · exact schurN_6_7 z t
  · interval_cases g
    · exact schurN_7_1 z t
    · exact schurN_7_2 z t
    · exact schurN_7_3 z t
    · exact schurN_7_4 z t
    · exact schurN_7_5 z t
    · exact schurN_7_6 z t
    · exact schurN_7_7 z t

/-- The Pfaffian adjugate of the Schur block of the bordered matrix: `(-1) ^ (f - 1)` times its
six-index Pfaffian without `f` is `U Q G z_f`. -/
theorem adjPf_schurN (z t : ℕ → R) {f : ℕ} (h1 : 1 ≤ f) (h7 : f ≤ 7) :
    (-1) ^ (f - 1) * Matrix.pfaffianAux (schurN z t) ((List.range' 1 7).erase f) =
      uv z * qv z * gv z * z f := by
  rw [Matrix.pfaffianAux_congr (schurN z t)
    (fun a b => crossMat (aV z) a b + wedge (xV z) (vV z) a b) _ _ rfl ?_]
  · exact adjPf_schur z h1 h7
  · intro a ha b hb
    have ha' := List.mem_range'_1.mp (List.mem_of_mem_erase ha)
    have hb' := List.mem_range'_1.mp (List.mem_of_mem_erase hb)
    exact schurN_eq z t (by omega) (by omega) (by omega) (by omega)

end PfaffianSchurBlock
