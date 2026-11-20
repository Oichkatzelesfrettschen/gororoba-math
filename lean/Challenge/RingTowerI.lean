/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TraceForm
public import GororobaMath.CayleyDickson.NonAssociative

/-!
# Challenge: the kernel swap over a ring with a square root of -1

This file restates, with `sorry` as each proof, the headline theorems that
`GororobaMath.CayleyDickson.RingTowerI` proves and that the "Lean library" table of `README.md` names,
with the definitions those statements use. It imports the library modules that the
solution module imports. `lake comparator --config` with the JSON file beside this one
checks that each named theorem of the solution module has the statement written here
and depends only on `propext`, `Classical.choice` and `Quot.sound`. No library module
imports this file, and the admission gate does not build it.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R]

/-- The level-1 element `(a, b)` with coordinates `a b : R`. -/
def ofPair (a b : R) : Tower R 1 := mk (show Tower R 0 from a) (show Tower R 0 from b)

/-- The embedding `x ↦ (x, 0)` of level `2` into level `k + 2`. -/
def liftTwo : (k : ℕ) → Tower R 2 → Tower R (k + 2)
  | 0, x => x
  | k + 1, x => mk (liftTwo k x) 0

section Trivial

variable [TrivialStar R]

variable (i : R)

/-- The pure nilpotent `e₁ + i e₂` of level 2. -/
def nilpotent2 : Tower R 2 := mk (ofPair 0 1) (ofPair i 0)

variable {i}

/-- Over a commutative ring with `i * i = -1`, if the kernel swap holds for every pure element at
level `k + 2`, then `2 = 0`. The Rocq original is `pure_kernel_swap_two_zero` of the functor
`RingTowerI` in `rocq/quantum/CdTowerRing.v`. -/
theorem pure_kernel_swap_two_eq_zero (hi : i * i = -1) (k : ℕ)
    (h : ∀ a z : Tower R (k + 2), star a = -a → a * z = 0 → z * a = 0) : (2 : R) = 0 := by
  sorry

/-- Over a commutative ring with `i * i = -1`, the kernel swap holds at level `k + 2` exactly when
`2 = 0`. The Rocq original is `kernel_swap_iff_two_zero` of the functor `RingTowerI` in
`rocq/quantum/CdTowerRing.v`. -/
theorem kernel_swap_iff_two_eq_zero (hi : i * i = -1) (k : ℕ) :
    (∀ a z : Tower R (k + 2), a * z = 0 → z * a = 0) ↔ (2 : R) = 0 := by
  sorry

end Trivial

section ZMod5

/-- The identity as star on `ZMod 5`: `starRingOfComm`, Mathlib's star on a commutative ring that
is the identity, so `star a = a` for every `a : ZMod 5` and the tower below has the star of the
Rocq functor, not a complex conjugation. -/
local instance : StarRing (ZMod 5) := starRingOfComm

local instance : TrivialStar (ZMod 5) := ⟨fun _ => rfl⟩

/-- Over `ZMod 5` with `i = 2` the kernel swap fails for pure elements at every level `k + 2`. The
Rocq original is `mod5_kernel_swap_fails` of `rocq/quantum/CdTowerRing.v`; the star of `ZMod 5` is
`starRingOfComm` (the identity, declared as `TrivialStar`), so this is the tower of the Rocq
functor and not of a Gaussian conjugation. -/
theorem zmod5_not_pure_kernel_swap (k : ℕ) :
    ¬ ∀ a z : Tower (ZMod 5) (k + 2), star a = -a → a * z = 0 → z * a = 0 := by
  sorry

end ZMod5

end Tower

end CayleyDickson
