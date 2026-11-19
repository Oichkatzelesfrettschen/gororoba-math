/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# The Radon-Hurwitz number of the tower dimensions

Convention: the Radon-Hurwitz number of `n = 2 ^ b * m` with `m` odd is
`2 ^ (b % 4) + 8 * (b / 4)`, the exponent `b` being the multiplicity of `2` in `n`
(`Nat.factorization n 2`). The tower `Tower R k` of `GororobaMath.CayleyDickson.Tower` has
dimension `2 ^ k`.

The number is at most `2 ^ b` for `b ≤ 3`, which are the dimensions `1, 2, 4, 8` of the
normed division algebras, and it is strictly below `2 ^ b` from `b = 4` on: with `b = 4 q + r`,
`q ≥ 1`, the bound `15 q + 1 ≤ 16 ^ q` gives `2 ^ r + 8 q < 2 ^ r * 16 ^ q`.

## Main results

* `Tower.hurwitzRadon_lt`: the Rocq original is `hurwitz_cd_tower_non_square_dimensions` of
  `rocq/open/theories/HurwitzTheorem.v`, which covers `2 ^ k` for `k` from 4 to 8 by a table.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

/-- The Radon-Hurwitz number `2 ^ (b % 4) + 8 * (b / 4)` of `n = 2 ^ b * m`, `m` odd. The Rocq
`hurwitz_radon` of `rocq/open/theories/HurwitzTheorem.v` is its values on `1, 2, 4, ..., 256`. -/
def hurwitzRadon (n : ℕ) : ℕ := 2 ^ (n.factorization 2 % 4) + 8 * (n.factorization 2 / 4)

theorem hurwitzRadon_two_pow (k : ℕ) : hurwitzRadon (2 ^ k) = 2 ^ (k % 4) + 8 * (k / 4) := by
  rw [hurwitzRadon, Nat.Prime.factorization_pow Nat.prime_two]
  simp

theorem fifteen_mul_add_one_le_pow (q : ℕ) : 15 * q + 1 ≤ 16 ^ q := by
  induction q with
  | zero => simp
  | succ q ih => rw [pow_succ]; omega

/-- At every tower dimension `2 ^ k` with `k ≥ 4` the Radon-Hurwitz number is below the dimension.
The Rocq original is `hurwitz_cd_tower_non_square_dimensions` of
`rocq/open/theories/HurwitzTheorem.v`, which covers `k` from 4 to 8 by a table. -/
theorem hurwitzRadon_lt {k : ℕ} (hk : 4 ≤ k) : hurwitzRadon (2 ^ k) < 2 ^ k := by
  rw [hurwitzRadon_two_pow]
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℕ, r < 4 ∧ k = 4 * q + r :=
    ⟨k / 4, k % 4, Nat.mod_lt _ (by omega), by omega⟩
  have hq : 1 ≤ q := by omega
  have h16 := fifteen_mul_add_one_le_pow q
  have h2r : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  have hmod : (4 * q + r) % 4 = r := by omega
  have hdiv : (4 * q + r) / 4 = q := by omega
  rw [hmod, hdiv, pow_add, pow_mul]
  have h4 : (2 : ℕ) ^ 4 = 16 := by norm_num
  rw [h4]
  nlinarith [Nat.mul_le_mul_right (2 ^ r) h16, Nat.mul_le_mul_left q h2r]

end Tower

end CayleyDickson
