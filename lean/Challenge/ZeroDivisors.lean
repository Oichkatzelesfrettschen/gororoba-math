/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TwoTerm
public import GororobaMath.CayleyDickson.NonAssociative
public import GororobaMath.CayleyDickson.AnnihilatorSymmetry

/-!
# Challenge: failure of the multiplicativity of the norm

This file restates, with `sorry` as each proof, the headline theorems that the solution
module proves and that the "Lean library" table of `README.md` names, with the
definitions those statements use. It imports the library modules that the solution
module imports. `lake comparator --config` with the JSON file beside this one checks
that each named theorem of the solution module has the statement written here and
depends only on `propext`, `Classical.choice` and `Quot.sound`. No library module
imports this file, and the admission gate does not build it.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

section Ring

variable {R : Type u} [NonAssocRing R] [StarRing R] [Nontrivial R]

end Ring

section Ordered

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] [PartialOrder R]
  [IsOrderedAddMonoid R] [NoZeroDivisors R] [Nontrivial R]

omit [TrivialStar R] in
/-- The trace form of the product is not the product of the trace forms at any level `k ≥ 4` over a
nontrivial ordered domain: a zero-divisor pair has `dot (x * y) (x * y) = 0` while
`dot x x * dot y y ≠ 0`. The Rocq original is `hurwitz_fails_implies_zd_persistent` of
`rocq/open/verified/C957_VoudonZD.v`, which states the sedenion norm over the reals. -/
theorem exists_dot_mul_self_ne (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ} (hk : 4 ≤ k) :
    ∃ x y : Tower R k, dot k (x * y) (x * y) ≠ dot k x x * dot k y y := by
  sorry

end Ordered

end Tower

end CayleyDickson
