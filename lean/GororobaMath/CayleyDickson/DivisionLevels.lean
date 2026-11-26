/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AlternativeIdentities
public import GororobaMath.CayleyDickson.NonAssociative
public import GororobaMath.CayleyDickson.ZeroDivisors

/-!
# Associativity, alternativity and division at the levels of the real division algebras

Convention: `Tower R k` is the tower of `GororobaMath.CayleyDickson.Tower` over a commutative
ring `R` whose star is the identity, with the product
`(a, b) (c, d) = (a c - star d b, d a + b star c)`.
Levels 0, 1, 2 and 3 are `R`, the complex pairs, the quaternions and the octonions, of dimension
1, 2, 4 and 8. An ordered coefficient ring carries the hypothesis `hsq : ∀ x : R, 0 ≤ x * x`, and
`Tower.dot k x x` is the sum of the squares of the coordinates of `x`
(`GororobaMath.CayleyDickson.AnnihilatorSymmetry`).

The product is associative exactly up to level 2 and alternative up to level 3 (the existing
theorems `Tower.associator_eq_zero_of_le_two`, `Tower.left_alternative_of_le_three` and
`Tower.right_alternative_of_le_three`), and the trace form multiplies up to level 3
(`Tower.dot_mul_self_of_le_three`), so a product of nonzero elements is nonzero on those levels.
From level 4 on, `Tower.exists_zero_divisor` gives a zero-divisor pair.

## Main results

* `Tower.mul_assoc_of_le_two`: `x * y * z = x * (y * z)` at levels 0 to 2.
* `Tower.exists_mul_assoc_ne_iff`: over a ring with `2 ≠ 0`, some triple fails associativity
  exactly at the levels `k ≥ 3`.
* `Tower.mul_eq_zero_of_le_three`: over an ordered domain, `x * y = 0` forces `x = 0` or
  `y = 0` at levels 0 to 3.
* `Tower.mul_eq_zero_iff_of_le_three`: the same as an equivalence.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] {k : ℕ}

/-- The product is associative at levels 0 to 2, since the associator vanishes there. -/
theorem mul_assoc_of_le_two (hk : k ≤ 2) (x y z : Tower R k) : x * y * z = x * (y * z) :=
  sub_eq_zero.mp (associator_eq_zero_of_le_two hk x y z)

/-- Over a ring with `2 ≠ 0`, an associativity-violating triple exists exactly from level 3 on. -/
theorem exists_mul_assoc_ne_iff (h2 : (2 : R) ≠ 0) :
    (∃ x y z : Tower R k, x * y * z ≠ x * (y * z)) ↔ 3 ≤ k := by
  refine ⟨fun ⟨x, y, z, h⟩ => ?_, fun hk => exists_mul_assoc_ne h2 k hk⟩
  by_contra hk
  exact h (mul_assoc_of_le_two (by omega) x y z)

section Ordered

variable [PartialOrder R] [IsOrderedAddMonoid R] [NoZeroDivisors R]

/-- A product vanishes only with a factor at levels 0 to 3: the trace form multiplies there and
is nonzero on a nonzero element. -/
theorem mul_eq_zero_of_le_three (hsq : ∀ x : R, 0 ≤ x * x) (hk : k ≤ 3) {x y : Tower R k}
    (h : x * y = 0) : x = 0 ∨ y = 0 := by
  by_contra hne
  rw [not_or] at hne
  have hd := dot_mul_self_of_le_three hk x y
  rw [h, dot_zero_left] at hd
  exact mul_ne_zero (dot_self_ne_zero hsq hne.1) (dot_self_ne_zero hsq hne.2) hd.symm

/-- A product vanishes exactly when a factor does, at levels 0 to 3. -/
theorem mul_eq_zero_iff_of_le_three (hsq : ∀ x : R, 0 ≤ x * x) (hk : k ≤ 3) {x y : Tower R k} :
    x * y = 0 ↔ x = 0 ∨ y = 0 :=
  ⟨mul_eq_zero_of_le_three hsq hk, fun h => h.elim (fun hx => by rw [hx, zero_mul])
    (fun hy => by rw [hy, mul_zero])⟩

end Ordered

end Tower

end CayleyDickson
