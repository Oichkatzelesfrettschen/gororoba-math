/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TowerModule

/-!
# Challenge: left and right annihilators coincide at every level of the tower

This file restates, with `sorry` as each proof, the headline theorems that
`GororobaMath.CayleyDickson.AnnihilatorSymmetry` proves and that the "Lean library" table of `README.md`
names, together with the definition `Tower.re` that the purity statement uses, copied from the solution
module. This file imports the library module that the solution module itself imports, so `Tower` and its
product are the library's own.
`lake comparator --config` with the JSON file beside this one checks that each named theorem of the
solution module has the statement written here and depends only on `propext`, `Classical.choice` and
`Quot.sound`. No library module imports this file, and the admission gate does not build it.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R]

/-- The coordinate of `1`. -/
def re : (k : ℕ) → Tower R k → R
  | 0, x => x
  | k + 1, ⟨a, _⟩ => re k a

variable [TrivialStar R] [PartialOrder R] [StarOrderedRing R] [NoZeroDivisors R]

/-- When `a * z = 0` with `a` and `z` nonzero, both are pure. -/
theorem re_eq_zero_of_mul_eq_zero {k : ℕ} {a z : Tower R k} (h : a * z = 0) (ha : a ≠ 0)
    (hz : z ≠ 0) : re k a = 0 ∧ re k z = 0 := by
  sorry

/-- The left and right annihilators of every element coincide, at every
level. -/
theorem mul_eq_zero_iff_rev {k : ℕ} (a z : Tower R k) : a * z = 0 ↔ z * a = 0 := by
  sorry

/-- A right inverse is a left inverse, at every level. -/
theorem mul_eq_one_rev {k : ℕ} {a b : Tower R k} (h : a * b = 1) : b * a = 1 := by
  sorry

end Tower

end CayleyDickson
