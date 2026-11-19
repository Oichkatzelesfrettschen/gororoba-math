/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.RingTowerI

/-!
# The quaternions are associative

Convention: `Tower R k` is the tower of `GororobaMath.CayleyDickson.Tower` over a commutative
ring `R` whose star is the identity, with the product
`(a, b) (c, d) = (a c - star d b, d a + b star c)`. Level 2 is the algebra of quaternions with
coefficients in `R`, an element being `((a₀, a₁), (a₂, a₃))` with the level-1 pairs
`Tower.ofPair a₀ a₁` of `GororobaMath.CayleyDickson.RingTowerI`.

## Main results

* `Tower.mul_assoc_two`: the product of level 2 is associative over every commutative ring with
  the identity as star. The Rocq originals are `dickson_quat_associative` of
  `rocq/open/theories/DicksonCDProcess.v` (the real quaternion record) and `quat_mul_assoc` of
  the module `QuatOps` in `rocq/open/theories/FloatQuaternion.v` (an arbitrary field under
  `FLOAT_OPS`, a signature that every commutative ring with the identity as star meets).
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

omit [CommRing R] [StarRing R] [TrivialStar R] in
theorem exists_ofPair (x : Tower R 1) : ∃ a b : R, x = ofPair a b := by
  obtain ⟨a, b⟩ := x
  exact ⟨a, b, rfl⟩

/-- The quaternion product is associative over every commutative ring with the identity as star.
The Rocq originals are `dickson_quat_associative` of `rocq/open/theories/DicksonCDProcess.v` and
`quat_mul_assoc` of the module `QuatOps` in `rocq/open/theories/FloatQuaternion.v`. -/
theorem mul_assoc_two (x y z : Tower R 2) : x * y * z = x * (y * z) := by
  obtain ⟨p, q⟩ := x
  obtain ⟨p', q'⟩ := y
  obtain ⟨p'', q''⟩ := z
  change mk p q * mk p' q' * mk p'' q'' = mk p q * (mk p' q' * mk p'' q'')
  obtain ⟨a0, a1, rfl⟩ := exists_ofPair p
  obtain ⟨a2, a3, rfl⟩ := exists_ofPair q
  obtain ⟨b0, b1, rfl⟩ := exists_ofPair p'
  obtain ⟨b2, b3, rfl⟩ := exists_ofPair q'
  obtain ⟨c0, c1, rfl⟩ := exists_ofPair p''
  obtain ⟨c2, c3, rfl⟩ := exists_ofPair q''
  simp only [mk_mul_mk, ofPair_star, ofPair_mul, ofPair_sub, ofPair_add, mk_inj, ofPair_inj]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

end Tower

end CayleyDickson
