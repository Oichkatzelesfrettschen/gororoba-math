/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AssociatorSpace

/-!
# Challenge: maps determined by their values on the basis

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

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

/-- A linear map of `Tower R k` that preserves the products of all pairs of basis
elements preserves every product. The Rocq original is `multiplicative_by_basis` of
the functor `RingTowerBasis` in `rocq/quantum/CdTowerRingBasis.v`. -/
theorem map_mul_of_map_e_mul_e {k : ℕ} (f : Tower R k →ₗ[R] Tower R k)
    (h : ∀ i j, f (e R k i * e R k j) = f (e R k i) * f (e R k j)) (x y : Tower R k) :
    f (x * y) = f x * f y := by
  sorry

/-- A linear map of `Tower R k` that satisfies the Leibniz rule on all pairs of basis elements
satisfies it on every pair. The Rocq original is `derivation_by_basis` of the functor
`RingTowerBasis` in `rocq/quantum/CdTowerRingBasis.v`. -/
theorem leibniz_of_leibniz_e {k : ℕ} (f : Tower R k →ₗ[R] Tower R k)
    (h : ∀ i j, f (e R k i * e R k j) = f (e R k i) * e R k j + e R k i * f (e R k j))
    (x y : Tower R k) : f (x * y) = f x * y + x * f y := by
  sorry

end Tower

end CayleyDickson
