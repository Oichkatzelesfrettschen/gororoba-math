/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Associator
public import GororobaMath.CayleyDickson.AssociatorPhase

/-!
# The associator sum of an anticommuting pair

Convention: the associator is `associator a b c = (a * b) * c - a * (b * c)`
(`Associator.lean`), and `Tower.e R k p` is the basis element of index `p : BitVec k`
(`GororobaMath.CayleyDickson.Tower`).

For `u`, `v` with `u * v + v * u = 0` the two products `(u * v) * y` and `(v * u) * y` cancel, so
`[u, v, y] + [v, u, y] = -(u * (v * y) + v * (u * y))` in every nonassociative ring. With
`K = -(L_u L_v + L_v L_u) / 2` this is `2 K = [u, v, ·] + [v, u, ·]`, stated here without the
division. Two distinct imaginary basis units anticommute (`Tower.commPhase_eq`), so the identity
holds for every such pair at every level of the tower over every nonassociative ring with a star,
the first identity of gororoba-quantum's findings row A5-622, whose source states the levels of
dimension 16, 32 and 64.

## Main results

* `CayleyDickson.associator_add_associator_swap_of_anticomm`: the identity for an anticommuting
  pair of a nonassociative ring.
* `Tower.e_mul_e_add_e_mul_e_of_commPhase`: basis elements with `commPhase p q` anticommute.
* `Tower.associator_e_add_associator_e_swap`: the identity for two distinct imaginary basis
  units.
-/

@[expose] public section

namespace CayleyDickson

/-- For an anticommuting pair, `[u, v, y] + [v, u, y] = -(u * (v * y) + v * (u * y))`. -/
theorem associator_add_associator_swap_of_anticomm {A : Type*} [NonAssocRing A] {u v : A}
    (h : u * v + v * u = 0) (y : A) :
    associator u v y + associator v u y = -(u * (v * y) + v * (u * y)) := by
  have h' : u * v * y + v * u * y = 0 := by rw [← add_mul, h, zero_mul]
  unfold associator
  calc u * v * y - u * (v * y) + (v * u * y - v * (u * y))
      = (u * v * y + v * u * y) - (u * (v * y) + v * (u * y)) := by abel
    _ = -(u * (v * y) + v * (u * y)) := by rw [h', zero_sub]

namespace Tower

universe u

variable {R : Type u} [NonAssocRing R] [StarRing R]

/-- Basis elements whose commutation phase holds anticommute. -/
theorem e_mul_e_add_e_mul_e_of_commPhase {k : ℕ} {p q : BitVec k} (h : commPhase p q = true) :
    e R k p * e R k q + e R k q * e R k p = 0 := by
  unfold commPhase at h
  rw [e_mul_e k p q, e_mul_e k q p, BitVec.xor_comm q p]
  revert h
  cases negSign k p q <;> cases negSign k q p <;> simp

/-- For distinct imaginary basis units `e p`, `e q` and every `y`,
`[e p, e q, y] + [e q, e p, y] = -(e p * (e q * y) + e q * (e p * y))`. -/
theorem associator_e_add_associator_e_swap {k : ℕ} {p q : BitVec k} (hp : p ≠ 0#k)
    (hq : q ≠ 0#k) (hpq : p ≠ q) (y : Tower R k) :
    associator (e R k p) (e R k q) y + associator (e R k q) (e R k p) y =
      -(e R k p * (e R k q * y) + e R k q * (e R k p * y)) :=
  associator_add_associator_swap_of_anticomm
    (e_mul_e_add_e_mul_e_of_commPhase (by rw [commPhase_eq]; simp [hp, hq, hpq])) y

end Tower

end CayleyDickson
