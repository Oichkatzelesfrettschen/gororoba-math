/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Basic

/-!
# Challenge: scalar actions on a Cayley-Dickson double

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

variable {A : Type*} [NonAssocRing A] [StarRing A]
  {S : Type*} [CommRing S] [StarRing S] [TrivialStar S] [Module S A] [IsScalarTower S A A]
  [SMulCommClass S A A] [StarModule S A]

omit [StarRing S] [TrivialStar S] [StarModule S A] in
/-- Scalars pass through the product of the double on the left. -/
theorem smul_mul_assoc (r : S) (x y : CayleyDickson A) : (r • x) * y = r • (x * y) := by
  sorry

/-- Scalars pass through the product of the double on the right. -/
theorem mul_smul_comm (r : S) (x y : CayleyDickson A) : x * (r • y) = r • (x * y) := by
  sorry

end CayleyDickson
