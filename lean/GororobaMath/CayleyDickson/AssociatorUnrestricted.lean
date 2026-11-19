/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.FlexibleLaw
public import GororobaMath.CayleyDickson.Associator

/-!
# The associator identities with no hypothesis on 2

Convention: `associator a b c = (a * b) * c - a * (b * c)` and the product of
`GororobaMath.CayleyDickson.Tower`, over a commutative ring with the identity as star
(`TrivialStar R`), as in `GororobaMath.CayleyDickson.Associator`.

The flexible law `Tower.mul_mul_self_eq'` holds with no hypothesis on `2`, so the associator
`A(x, y, x)` vanishes, and linearizing it at `x = a + c` gives `A(a, y, c) + A(c, y, a) = 0`
(`Tower.associator_add_associator_rev'`). The identities of `Associator.lean` that carry the
hypothesis `IsLeftRegular (2 : R)` follow with none.

## Main results

* `Tower.associator_self_right_eq_zero`: `A(x, y, x) = 0`.
* `Tower.associator_add_associator_rev'`: `A(a, b, c) = -A(c, b, a)` at every level over every
  commutative ring with the identity as star, in characteristic `2` included.
* `Tower.associator_star'`: `star A(a, b, c) = A(star a, star b, star c)` at every level over every
  such ring.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

/-- The associator `A(x, y, x)` vanishes: the flexible law without a hypothesis on `2`. -/
theorem associator_self_right_eq_zero {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]
    {k : ℕ} (x y : Tower R k) : associator x y x = 0 :=
  sub_eq_zero.2 (mul_mul_self_eq' x y)

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] {k : ℕ}

/-- The (1,3)-swap antisymmetry `A(a, b, c) = -A(c, b, a)`, written as a vanishing sum, at every
level with no hypothesis on `2`: the linearization of `A(x, b, x) = 0` at `x = a + c`. -/
theorem associator_add_associator_rev' (a b c : Tower R k) :
    associator a b c + associator c b a = 0 := by
  have h := associator_self_right_eq_zero (a + c) b
  rw [associator_add_left, associator_add_right, associator_add_right,
    associator_self_right_eq_zero, associator_self_right_eq_zero, zero_add, add_zero] at h
  exact h

theorem associator_eq_neg_associator_rev (a b c : Tower R k) :
    associator a b c = -associator c b a :=
  eq_neg_of_add_eq_zero_left (associator_add_associator_rev' a b c)

/-- Conjugation fixes the associator's arguments' order, at every level over every commutative ring
with the identity as star: `star A(a, b, c) = A(star a, star b, star c)`. -/
theorem associator_star' (a b c : Tower R k) :
    star (associator a b c) = associator (star a) (star b) (star c) := by
  rw [star_associator]
  exact neg_eq_of_add_eq_zero_right (associator_add_associator_rev' _ _ _)

end Tower

end CayleyDickson
