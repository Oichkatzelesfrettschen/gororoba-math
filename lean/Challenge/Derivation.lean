/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Map
public import GororobaMath.CayleyDickson.TowerModule

/-!
# Challenge: the dimension of the derivations from a certificate

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

variable {K : Type u} [Field K] [StarRing K] [TrivialStar K]

/-- The `K`-linear maps of `Tower K k` that satisfy the Leibniz rule. -/
def leibnizSubmodule (K : Type u) [Field K] [StarRing K] [TrivialStar K] (k : ℕ) :
    Submodule K (Tower K k →ₗ[K] Tower K k) where
  carrier := {F | ∀ x y, F (x * y) = F x * y + x * F y}
  add_mem' := fun {F G} hF hG x y => by
    simp only [LinearMap.add_apply, hF x y, hG x y, mul_add, add_mul]
    abel
  zero_mem' := fun x y => by simp only [LinearMap.zero_apply, mul_zero, zero_mul, add_zero]
  smul_mem' := fun c F hF x y => by
    simp only [LinearMap.smul_apply, hF x y, smul_add, smul_mul_assoc', mul_smul_comm']

/-- Given `n` independent derivations of `Tower K k` and a nonzero scalar `d` with `d • F` in
their span for every derivation `F`, the derivations form a space of dimension `n`. -/
theorem finrank_leibniz_of_certificate {k n : ℕ} (T : Fin n → Tower K k →ₗ[K] Tower K k)
    (hT : ∀ t x y, T t (x * y) = T t x * y + x * T t y) (hind : LinearIndependent K T) (d : K)
    (hd : d ≠ 0)
    (hspan : ∀ F : Tower K k →ₗ[K] Tower K k, (∀ x y, F (x * y) = F x * y + x * F y) →
      d • F ∈ Submodule.span K (Set.range T)) :
    Module.finrank K (leibnizSubmodule K k) = n := by
  sorry

end Tower

end CayleyDickson
