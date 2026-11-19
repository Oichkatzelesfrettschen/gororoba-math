/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Map

/-!
# Derivations extend to the Cayley-Dickson double

Convention: `CayleyDickson A` is the double of `GororobaMath.CayleyDickson.Basic`, pairs
`(re, im)` with `(a, b) * (c, d) = (a * c - star d * b, d * a + b * star c)` and
`star (a, b) = (star a, -b)`. `CayleyDickson.mapAdd D` applies an additive map `D` of `A` to both
halves, `(a, b) ↦ (D a, D b)`.

A derivation `D` of `A` (an additive map with `D (x * y) = D x * y + x * D y`) that commutes
with the star extends to a derivation of the double. The hypotheses are those of Schafer 1954,
Theorem 2, stated over every nonassociative star ring `A`; over an `R`-module `A` with `D`
linear, `CayleyDickson.map_smul` gives the `R`-linear form.

## Main results

* `CayleyDickson.mapAdd_leibniz`: `mapAdd D (x * y) = mapAdd D x * y + x * mapAdd D y`, the Rocq
  `schafer1954_theorem2_extension_map` of `rocq/open/theories/Schafer1954.v`.
-/

@[expose] public section

namespace CayleyDickson

variable {A : Type*} [NonAssocRing A] [StarRing A]

/-- The additive map `(a, b) ↦ (D a, D b)` of the double of `A` induced by an additive map `D`. -/
def mapAdd (D : A →+ A) : CayleyDickson A →+ CayleyDickson A where
  toFun := map D
  map_zero' := by ext <;> simp
  map_add' := CayleyDickson.map_add D

@[simp] theorem mapAdd_re (D : A →+ A) (x : CayleyDickson A) : (mapAdd D x).re = D x.re := rfl

@[simp] theorem mapAdd_im (D : A →+ A) (x : CayleyDickson A) : (mapAdd D x).im = D x.im := rfl

/-- A derivation of `A` that commutes with the star extends componentwise to a derivation of the
double. The Rocq original is `schafer1954_theorem2_extension_map` of
`rocq/open/theories/Schafer1954.v`. -/
theorem mapAdd_leibniz (D : A →+ A) (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (hs : ∀ x, D (star x) = star (D x)) (x y : CayleyDickson A) :
    mapAdd D (x * y) = mapAdd D x * y + x * mapAdd D y := by
  ext
  · simp only [mapAdd_re, mul_re, add_re, map_sub, hD, hs]
    simp only [mapAdd_im]
    abel
  · simp only [mapAdd_im, mul_im, add_im, map_add, hD, hs]
    simp only [mapAdd_re]
    abel

end CayleyDickson
