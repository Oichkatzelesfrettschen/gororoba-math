/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Map
public import GororobaMath.CayleyDickson.BasisExt

/-!
# Challenge: transport of a basis-defined map along a ring homomorphism

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

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [StarRing R] [TrivialStar R]
  [CommRing S] [StarRing S] [TrivialStar S]

/-- The coordinatewise image of an element of `Tower R k` under `φ`. -/
def map (φ : R →+* S) : (k : ℕ) → Tower R k → Tower S k
  | 0, x => φ x
  | k + 1, x => mk (map φ k x.re) (map φ k x.im)

/-- The transport of a linear map of `Tower R k` along `φ`. -/
noncomputable def baseChange (φ : R →+* S) {k : ℕ} (F : Tower R k →ₗ[R] Tower R k) :
    Tower S k →ₗ[S] Tower S k :=
  (basis S k).constr S fun i => map φ k (F (e R k i))

/-- A scaled multiplicativity of `F` on the basis pairs over `R` transports to every pair over
`S`. The Rocq original is `scaled_multiplicative_transport` of the functor `BaseChange` in
`rocq/quantum/CdTowerRingBaseChange.v`. -/
theorem baseChange_mul (φ : R →+* S) {k : ℕ} (F : Tower R k →ₗ[R] Tower R k) (c : R)
    (h : ∀ i j, F (e R k i) * F (e R k j) = c • F (e R k i * e R k j)) (x y : Tower S k) :
    baseChange φ F x * baseChange φ F y = φ c • baseChange φ F (x * y) := by
  sorry

/-- The Leibniz rule of `F` on the basis pairs over `R` transports to every pair over `S`. The
Rocq original is `derivation_transport` of the functor `BaseChange` in
`rocq/quantum/CdTowerRingBaseChange.v`. -/
theorem baseChange_leibniz (φ : R →+* S) {k : ℕ} (F : Tower R k →ₗ[R] Tower R k)
    (h : ∀ i j, F (e R k i * e R k j) = F (e R k i) * e R k j + e R k i * F (e R k j))
    (x y : Tower S k) :
    baseChange φ F (x * y) = baseChange φ F x * y + x * baseChange φ F y := by
  sorry

end Tower

end CayleyDickson
