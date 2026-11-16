/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TowerModule

/-!
# Challenge: left and right annihilators coincide at every level of the tower

This file restates, with `sorry` as each proof, the headline theorems that
`GororobaMath.CayleyDickson.AnnihilatorSymmetry` proves and that the "Lean library" table of `README.md`
names. Their statements use no definition of the solution module, and this file imports the library module
that the solution module itself imports, so `Tower` and its product are the library's own.
`lake comparator --config` with the JSON file beside this one checks that each named theorem of the
solution module has the statement written here and depends only on `propext`, `Classical.choice` and
`Quot.sound`. No library module imports this file, and the admission gate does not build it.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] [LinearOrder R]
  [IsStrictOrderedRing R]

/-- The left and right annihilators of every element coincide, at every
level. -/
theorem mul_eq_zero_iff_rev {k : ℕ} (a z : Tower R k) : a * z = 0 ↔ z * a = 0 := by
  sorry

/-- A right inverse is a left inverse, at every level. -/
theorem mul_eq_one_rev {k : ℕ} {a b : Tower R k} (h : a * b = 1) : b * a = 1 := by
  sorry

end Tower

end CayleyDickson
