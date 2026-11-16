/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib

/-!
# Challenge: the product of the Cayley-Dickson double

This file restates, with `sorry` as each proof, the headline theorems that
`GororobaMath.CayleyDickson.Basic` proves and that the "Lean library" table of `README.md` names, together with the structure `CayleyDickson` and the product and star
instances that the statement uses, copied from the solution module.
The solution module imports only Mathlib, so this file restates the definitions its theorem
mentions; each copies the solution's text and elaborates to the same constant.
`lake comparator --config` with the JSON file beside this one checks that each named theorem of the
solution module has the statement written here and depends only on `propext`, `Classical.choice` and
`Quot.sound`. No library module imports this file, and the admission gate does not build it.
-/

@[expose] public section

/-- The Cayley-Dickson double of `A`: pairs `(re, im)`. -/
structure CayleyDickson (A : Type*) where
  /-- The first half, the copy of `A` that contains `1`. -/
  re : A
  /-- The second half, the multiples of the new imaginary unit. -/
  im : A

namespace CayleyDickson

variable {A : Type*}

section Ring

variable [NonAssocRing A] [StarRing A]

instance : Mul (CayleyDickson A) :=
  ⟨fun x y => ⟨x.re * y.re - star y.im * x.im, y.im * x.re + x.im * star y.re⟩⟩

instance : Star (CayleyDickson A) := ⟨fun x => ⟨star x.re, -x.im⟩⟩

/-- `x * star x` lies in the first half. -/
theorem mul_star_self (x : CayleyDickson A) :
    x * star x = ⟨x.re * star x.re + star x.im * x.im, 0⟩ := by
  sorry

end Ring

end CayleyDickson
