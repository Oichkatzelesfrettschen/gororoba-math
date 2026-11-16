/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Tower

/-!
# Challenge: non-associativity at every level of the tower

This file restates, with `sorry` as each proof, the headline theorems that
`GororobaMath.CayleyDickson.NonAssociative` proves and that the "Lean library" table of `README.md` names.
The solution module introduces no definition, and this file imports the library module that the solution
module itself imports, so `Tower`, `e` and `mk` are the library's own. `lake comparator --config`
with the JSON file beside this one checks that each named theorem of the solution module has the
statement written here and depends only on `propext`, `Classical.choice` and `Quot.sound`. No library
module imports this file, and the admission gate does not build it.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [NonAssocRing R] [StarRing R]

/-- Over a ring in which `2 ≠ 0`, no basis element equals its negative. -/
theorem e_ne_neg_e (h2 : (2 : R) ≠ 0) : ∀ (k : ℕ) (p : BitVec k), e R k p ≠ -e R k p := by
  sorry

/-- In the octonions over a ring in which `2 ≠ 0`, `(e 1 * e 2) * e 4` and
`e 1 * (e 2 * e 4)` differ. -/
theorem octonion_e1_e2_e4_mul_assoc_ne (h2 : (2 : R) ≠ 0) :
    e R 3 1#3 * e R 3 2#3 * e R 3 4#3 ≠ e R 3 1#3 * (e R 3 2#3 * e R 3 4#3) := by
  sorry

/-- At every level `k ≥ 3` of the tower over a ring with a star in which
`2 ≠ 0`, some triple violates associativity. -/
theorem exists_mul_assoc_ne (h2 : (2 : R) ≠ 0) :
    ∀ k : ℕ, 3 ≤ k → ∃ a b c : Tower R k, a * b * c ≠ a * (b * c) := by
  sorry

/-- The 128-dimensional algebra, level `7`, is not associative. -/
theorem exists_mul_assoc_ne_level_seven (h2 : (2 : R) ≠ 0) :
    ∃ a b c : Tower R 7, a * b * c ≠ a * (b * c) := by
  sorry

end Tower

end CayleyDickson
