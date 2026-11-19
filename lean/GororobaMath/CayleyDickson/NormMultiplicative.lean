/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Quaternion

/-!
# The trace form is multiplicative up to level 3

Convention: `Tower R k` is the tower of `GororobaMath.CayleyDickson.Tower` over a commutative
ring `R` whose star is the identity, with the product
`(a, b) (c, d) = (a c - star d b, d a + b star c)`, and `Tower.dot k x x` is the sum of the squares
of the `2 ^ k` coordinates of `x` (`GororobaMath.CayleyDickson.AnnihilatorSymmetry`). A level-1
element is `Tower.ofPair a b`, a level-2 element a pair of those, and a level-3 element a pair
of level-2 elements, so levels 1, 2 and 3 are the complex pairs, the quaternions and the octonions
with coefficients in `R`.

## Main results

* `Tower.dot_mul_self_of_le_three`: `dot (x * y) (x * y) = dot x x * dot y y` at levels 0 to 3,
  the one-, two-, four- and eight-square identities (level 3 is a polynomial identity of degree 4
  in 16 variables that `ring` closes). The Rocq originals are `d1921_eq4` of
  `rocq/open/theories/Dickson1921.v` (the surface there assumes a multiplicative norm) and
  `quat_norm_mul` of the module `QuatOps` in `rocq/open/theories/FloatQuaternion.v` (level 2).
  The statement fails from level 4 on, where the tower has zero divisors.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

omit [TrivialStar R] in
theorem sub_mk {k : ℕ} (a b c d : Tower R k) :
    mk a b - mk c d = mk (a - c) (b - d) := rfl

omit [StarRing R] [TrivialStar R] in
theorem dot_ofPair (a b c d : R) : dot 1 (ofPair a b) (ofPair c d) = a * c + b * d := rfl

/-- The trace form is multiplicative at levels 0 to 3. The Rocq originals are `d1921_eq4` of
`rocq/open/theories/Dickson1921.v` and `quat_norm_mul` of the module `QuatOps` in
`rocq/open/theories/FloatQuaternion.v`. -/
theorem dot_mul_self_of_le_three {k : ℕ} (hk : k ≤ 3) (x y : Tower R k) :
    dot k (x * y) (x * y) = dot k x x * dot k y y := by
  interval_cases k
  · exact (by intro a b; ring : ∀ a b : R, a * b * (a * b) = a * a * (b * b))
      (show R from x) (show R from y)
  · obtain ⟨a0, a1, rfl⟩ := exists_ofPair x
    obtain ⟨b0, b1, rfl⟩ := exists_ofPair y
    simp only [ofPair_mul, dot_ofPair]
    ring
  · obtain ⟨p, q⟩ := x
    obtain ⟨p', q'⟩ := y
    obtain ⟨a0, a1, rfl⟩ := exists_ofPair p
    obtain ⟨a2, a3, rfl⟩ := exists_ofPair q
    obtain ⟨b0, b1, rfl⟩ := exists_ofPair p'
    obtain ⟨b2, b3, rfl⟩ := exists_ofPair q'
    change dot 2 (Tower.mk _ _ * Tower.mk _ _) (Tower.mk _ _ * Tower.mk _ _) =
      dot 2 (Tower.mk _ _) (Tower.mk _ _) * dot 2 (Tower.mk _ _) (Tower.mk _ _)
    simp only [mk_mul_mk, ofPair_star, ofPair_mul, ofPair_sub, ofPair_add, dot_mk, dot_ofPair]
    ring
  · obtain ⟨P, Q⟩ := x
    obtain ⟨P', Q'⟩ := y
    obtain ⟨p, q⟩ := P
    obtain ⟨p', q'⟩ := Q
    obtain ⟨r, s⟩ := P'
    obtain ⟨r', s'⟩ := Q'
    obtain ⟨a0, a1, rfl⟩ := exists_ofPair p
    obtain ⟨a2, a3, rfl⟩ := exists_ofPair q
    obtain ⟨a4, a5, rfl⟩ := exists_ofPair p'
    obtain ⟨a6, a7, rfl⟩ := exists_ofPair q'
    obtain ⟨b0, b1, rfl⟩ := exists_ofPair r
    obtain ⟨b2, b3, rfl⟩ := exists_ofPair s
    obtain ⟨b4, b5, rfl⟩ := exists_ofPair r'
    obtain ⟨b6, b7, rfl⟩ := exists_ofPair s'
    change dot 3 (Tower.mk (Tower.mk _ _) (Tower.mk _ _) * Tower.mk (Tower.mk _ _) (Tower.mk _ _))
      (Tower.mk (Tower.mk _ _) (Tower.mk _ _) * Tower.mk (Tower.mk _ _) (Tower.mk _ _)) =
      dot 3 (Tower.mk (Tower.mk _ _) (Tower.mk _ _)) (Tower.mk (Tower.mk _ _) (Tower.mk _ _)) *
      dot 3 (Tower.mk (Tower.mk _ _) (Tower.mk _ _)) (Tower.mk (Tower.mk _ _) (Tower.mk _ _))
    simp only [mk_mul_mk, star_mk, ofPair_star, ofPair_mul, ofPair_sub, ofPair_add, ofPair_neg,
      add_mk, sub_mk, dot_mk, dot_ofPair]
    ring

end Tower

end CayleyDickson
