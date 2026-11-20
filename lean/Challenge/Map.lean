/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.NonAssociative

/-!
# Challenge: maps of a Cayley-Dickson double and the iterated embedding

This file restates, with `sorry` as each proof, the headline theorems that
`GororobaMath.CayleyDickson.Map` proves and that the "Lean library" table of `README.md` names,
with the definitions those statements use. It imports the library modules that the
solution module imports. `lake comparator --config` with the JSON file beside this one
checks that each named theorem of the solution module has the statement written here
and depends only on `propext`, `Classical.choice` and `Quot.sound`. No library module
imports this file, and the admission gate does not build it.
-/

@[expose] public section

namespace CayleyDickson

variable {A B : Type*}

/-- `f` applied to both halves: `(a, b) ↦ (f a, f b)`. -/
def map (f : A → B) (x : CayleyDickson A) : CayleyDickson B := ⟨f x.re, f x.im⟩

section Additive

variable [NonAssocRing A] [NonAssocRing B]

end Additive

section Ring

variable [NonAssocRing A] [StarRing A] [NonAssocRing B] [StarRing B]

/-- A non-unital ring homomorphism that commutes with the star extends to a
map of the doubles that preserves products. -/
protected theorem map_mul (f : A →ₙ+* B) (hf : ∀ x, f (star x) = star (f x))
    (x y : CayleyDickson A) : map f (x * y) = map f x * map f y := by
  sorry

end Ring

namespace Tower

universe u

variable {R : Type u} [NonAssocRing R] [StarRing R]

/-- The iterated embedding `x ↦ (x, 0)` of level `j` into level `j + k`. -/
def lift (j : ℕ) : (k : ℕ) → Tower R j → Tower R (j + k)
  | 0, x => x
  | k + 1, x => mk (lift j k x) 0

/-- The iterated embedding preserves products. The Rocq original is `lift_mul` of the functor
`RingTower` in `rocq/quantum/CdTowerRing.v`. -/
theorem lift_mul (j k : ℕ) (x y : Tower R j) :
    lift j k (x * y) = lift j k x * lift j k y := by
  sorry

/-- The iterated embedding is injective. The Rocq original is `lift_injective` of the functor
`RingTower` in `rocq/quantum/CdTowerRing.v`. -/
theorem lift_injective (j k : ℕ) : Function.Injective (lift (R := R) j k) := by
  sorry

end Tower

end CayleyDickson
