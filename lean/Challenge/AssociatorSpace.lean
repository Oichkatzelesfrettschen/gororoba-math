/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TwoTermRecursion

/-!
# Challenge: the associator space of two basis elements

This file restates, with `sorry` as each proof, the headline theorems that
`GororobaMath.CayleyDickson.AssociatorSpace` proves and that the "Lean library" table of `README.md` names, together
with the definitions that `GororobaMath.CayleyDickson.AssociatorSpace` introduces and those statements use.
It imports the library modules that the solution module itself imports, so the
earlier definitions (`Tower`, `negSign`, `alignedPairCount`, ...) are the
library's own; a restated definition copies the solution's text and must
elaborate to the same constant. `lake comparator --config` with the JSON file
beside this one checks that each named theorem of the solution module has the
statement written here and depends only on `propext`, `Classical.choice` and
`Quot.sound`. No library module imports this file, and the admission gate does
not build it.
-/

@[expose] public section

namespace CayleyDickson

open Module

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

variable (R) in
/-- Right multiplication by `x` as an `R`-linear map. -/
def mulRight (k : ℕ) (x : Tower R k) : Tower R k →ₗ[R] Tower R k where
  toFun y := y * x
  map_add' a b := add_mul a b x
  map_smul' r y := smul_mul_assoc' r y x

variable (R) in
/-- The associator `x ↦ (a * x) * b - a * (x * b)` as an `R`-linear map of
`x`. -/
def associatorMap (k : ℕ) (a b : Tower R k) : Tower R k →ₗ[R] Tower R k :=
  mulRight R k b ∘ₗ mulLeft R k a - mulLeft R k a ∘ₗ mulRight R k b

variable (R) in
/-- The associator space `Ass a b = {x | (a * x) * b = a * (x * b)}`, the
kernel of `associatorMap`. -/
def assocSpace (k : ℕ) (a b : Tower R k) : Submodule R (Tower R k) :=
  LinearMap.ker (associatorMap R k a b)

/-- The associator space of `e a` and `e b` is a free module when `2` is a
non-zero-divisor. -/
theorem free_assocSpace_e (h2 : IsLeftRegular (2 : R)) {k : ℕ} (a b : BitVec k) :
    Module.Free R (assocSpace R k (e R k a) (e R k b)) := by
  sorry

/-- **Associator dimension.** For nonzero distinct indices `a` and `b`, the
associator space of `e a` and `e b` has rank
`2 * alignedPairCount k a b + 4`, over every nontrivial commutative ring
with the identity as star in which `2` is a non-zero-divisor. -/
theorem finrank_assocSpace_e [Nontrivial R] (h2 : IsLeftRegular (2 : R)) {k : ℕ}
    {a b : BitVec k} (ha : a ≠ 0#k) (hb : b ≠ 0#k) (hab : a ≠ b) :
    finrank R (assocSpace R k (e R k a) (e R k b)) = 2 * alignedPairCount k a b + 4 := by
  sorry

end Tower

end CayleyDickson
