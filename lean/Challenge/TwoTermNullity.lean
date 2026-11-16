/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TowerModule
public import GororobaMath.CayleyDickson.TwoTerm

/-!
# Challenge: the nullity of left multiplication by a two-term operand

This file restates, with `sorry` as each proof, the headline theorems that
`GororobaMath.CayleyDickson.TwoTermNullity` proves and that the "Lean library" table of `README.md` names.
The solution module introduces no definition that these statements use.
This file imports the library modules that the solution module itself imports, so `Tower`, `mulLeft`,
`e` and `alignedPairCount` are the library's own.
`lake comparator --config` with the JSON file beside this one checks that each named theorem of the
solution module has the statement written here and depends only on `propext`, `Classical.choice` and
`Quot.sound`. No library module imports this file, and the admission gate does not build it.
-/

@[expose] public section

namespace CayleyDickson

open Module

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

/-- The kernel of left multiplication by `e i + e j` is a free module when
`2` is a non-zero-divisor. -/
theorem free_ker_mulLeft_e_add_e (h2 : IsLeftRegular (2 : R)) (k : ℕ) (i j : BitVec k) :
    Module.Free R (LinearMap.ker (mulLeft R k (e R k i + e R k j))) := by
  sorry

/-- The nullity of left multiplication by `e i + e j` is the number of
aligned pairs, at every level `k` and for all indices `i` and `j`, over
every nontrivial commutative ring with the identity as star in which `2` is
a non-zero-divisor. For `i = j` both sides are `0`. -/
theorem finrank_ker_mulLeft_e_add_e [Nontrivial R] (h2 : IsLeftRegular (2 : R)) (k : ℕ)
    (i j : BitVec k) :
    finrank R (LinearMap.ker (mulLeft R k (e R k i + e R k j))) = alignedPairCount k i j := by
  sorry

end Tower

end CayleyDickson
