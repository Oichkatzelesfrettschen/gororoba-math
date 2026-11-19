/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Alternative

/-!
# A polynomial identity of the octonions with coefficients in a commutative ring

Convention: the product of `Tower R 3` is the Cayley-Dickson product
`(a, b) (c, d) = (a c - star d b, d a + b star c)` of `GororobaMath.CayleyDickson.Basic`, over a
commutative ring `R` with the identity as star, and the associator is
`associator a b c = (a * b) * c - a * (b * c)`.

## Main results

* `Tower.associator_commutator_mul_three`:
  `A(a b - b a, x, y) + A(a, b, x y) = A(a, b, x) y + x A(a, b, y)`, the identity that makes
  `D(a, b)(x) = [[a, b], x] - 3 A(a, b, x)` a derivation of the octonions. It is a polynomial
  identity of degree 4 in 32 coordinates; the proof expands both sides into the eight coordinates
  of the result and closes each by `ring`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

set_option maxHeartbeats 1600000 in
-- the eight coordinate goals are polynomial identities of degree 4 in 32 variables; the default
-- limit of 200000 heartbeats stops the first of them
/-- The identity behind the Leibniz rule of the inner derivation at level 3:
`A(a b - b a, x, y) + A(a, b, x y) = A(a, b, x) y + x A(a, b, y)`, a polynomial identity of degree 4
in 32 coordinates that `ring` closes. -/
theorem associator_commutator_mul_three (a b x y : Tower R 3) :
    associator (a * b - b * a) x y + associator a b (x * y) =
      associator a b x * y + x * associator a b y := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, rfl⟩ := exists_coordinates_three a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ := exists_coordinates_three b
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, rfl⟩ := exists_coordinates_three x
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, rfl⟩ := exists_coordinates_three y
  simp only [associator, mk_mul_mk, star_mk, ofPair_star, ofPair_mul, mk_sub_mk,
    mk_add_mk, ofPair_sub, ofPair_add, ofPair_neg, mk_inj, ofPair_inj]
  repeat' apply And.intro
  all_goals ring

end Tower

end CayleyDickson
