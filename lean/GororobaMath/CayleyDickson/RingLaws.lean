/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Tower

/-!
# Kernel laws of the tower over a nonassociative star ring

Convention: the product of `Tower R k` is the Cayley-Dickson product of
`GororobaMath.CayleyDickson.Tower`, `(a, b) (c, d) = (a c - star d b, d a + b star c)`,
with `star (a, b) = (star a, -b)`, over a `NonAssocRing R` with a `StarRing R`
structure. No law here needs commutativity, associativity or a trivial star
on `R`: each is a consequence of `star (x * y) = star y * star x` and of the
additive involution `star`. An element `a` is pure when `star a = -a`.

## Main results

* `Tower.mul_eq_zero_iff_star_mul_star`: `a * z = 0 ↔ star z * star a = 0`, the Rocq
  `kernel_conj` of the functor `RingTower` in `rocq/quantum/CdTowerRing.v`.
* `Tower.mul_eq_zero_iff_star_mul_of_star_eq_neg`: the same for pure `a`, `pure_kernel_conj`.
* `Tower.mul_eq_zero_iff_mul_star_of_star_eq_neg`: `v * a = 0 ↔ a * star v = 0` for pure `a`,
  `pure_right_left_kernel` of `rocq/open/theories/CDPureDoublingKernel.v`.
* `Tower.mk_mul_mk_eq_zero_iff_of_star_eq_neg`: `(a, 0) (c, d) = 0` for pure `a` splits as
  `a c = 0` and `a star d = 0`, `pure_doubling_kernel_decomposition` of the same file.
* `Tower.mul_eq_zero_iff_reflect_mul_reflect`: the reflection `(a, b) ↦ (a, -b)` carries the
  annihilator of `x` onto that of its image, `reflect_kernel` of `rocq/quantum/CdTowerRing.v`.
* `Tower.mul_eq_one_iff_mul_sub_eq_zero`: right inverses form a coset of the kernel,
  `tower_right_inverse_coset` of `rocq/open/theories/CDTowerZeroDivisors.v`.
-/

@[expose] public section

namespace CayleyDickson

universe u

namespace Tower

variable {R : Type u} [NonAssocRing R] [StarRing R]

/-- `a * z = 0` exactly when `star z * star a = 0`, at every level, because `star` reverses
products and is injective. The Rocq original is `kernel_conj` of the functor `RingTower` in
`rocq/quantum/CdTowerRing.v`. -/
theorem mul_eq_zero_iff_star_mul_star {k : ℕ} (a z : Tower R k) :
    a * z = 0 ↔ star z * star a = 0 := by
  rw [← star_mul, star_eq_zero]

/-- For pure `a`, `a * z = 0` exactly when `star z * a = 0`. The Rocq original is
`pure_kernel_conj` of the functor `RingTower` in `rocq/quantum/CdTowerRing.v`. -/
theorem mul_eq_zero_iff_star_mul_of_star_eq_neg {k : ℕ} {a : Tower R k} (ha : star a = -a)
    (z : Tower R k) : a * z = 0 ↔ star z * a = 0 := by
  rw [mul_eq_zero_iff_star_mul_star, ha, mul_neg, neg_eq_zero]

/-- For pure `a`, `v * a = 0` exactly when `a * star v = 0`. The Rocq original is
`pure_right_left_kernel` of `rocq/open/theories/CDPureDoublingKernel.v`. -/
theorem mul_eq_zero_iff_mul_star_of_star_eq_neg {k : ℕ} {a : Tower R k} (ha : star a = -a)
    (v : Tower R k) : v * a = 0 ↔ a * star v = 0 := by
  rw [mul_eq_zero_iff_star_mul_star, ha, neg_mul, neg_eq_zero]

/-- For pure `a`, `(a, 0) * (c, d) = 0` exactly when `a * c = 0` and `a * star d = 0`. The Rocq
original is `pure_doubling_kernel_decomposition` of
`rocq/open/theories/CDPureDoublingKernel.v`. -/
theorem mk_mul_mk_eq_zero_iff_of_star_eq_neg {k : ℕ} {a : Tower R k} (ha : star a = -a)
    (c d : Tower R k) : mk a 0 * mk c d = 0 ↔ a * c = 0 ∧ a * star d = 0 := by
  have h : mk a 0 * mk c d = mk (a * c) (d * a) := by
    rw [mk_mul_mk]
    simp
  rw [h, zero_eq_mk, mk_inj, mul_eq_zero_iff_mul_star_of_star_eq_neg ha d]

end Tower

/-- The reflection `(a, b) ↦ (a, -b)` carries `x * z = 0` to `reflect x * reflect z = 0` and
back. -/
theorem mul_eq_zero_iff_reflect_mul_reflect {A : Type*} [NonAssocRing A] [StarRing A]
    (x z : CayleyDickson A) : x * z = 0 ↔ reflect x * reflect z = 0 := by
  rw [← reflect_mul]
  constructor
  · intro h
    rw [h]
    ext <;> simp
  · intro h
    have := congrArg reflect h
    rwa [reflect_reflect, show reflect (0 : CayleyDickson A) = 0 by ext <;> simp] at this

namespace Tower

variable {R : Type u} [NonAssocRing R] [StarRing R]

/-- The reflection `(a, b) ↦ (a, -b)` carries the annihilator of `x` onto that of its image at
every level `k + 1`. The Rocq original is `reflect_kernel` of the functor `RingTower` in
`rocq/quantum/CdTowerRing.v`. -/
theorem mul_eq_zero_iff_reflect_mul_reflect {k : ℕ} (x z : Tower R (k + 1)) :
    x * z = 0 ↔ CayleyDickson.reflect x * CayleyDickson.reflect z = 0 :=
  CayleyDickson.mul_eq_zero_iff_reflect_mul_reflect x z

/-- Given `a * b = 1`, `a * b₂ = 1` exactly when `a * (b₂ - b) = 0`: right inverses form a coset
of the kernel of left multiplication. The Rocq original is `tower_right_inverse_coset` of
`rocq/open/theories/CDTowerZeroDivisors.v`. -/
theorem mul_eq_one_iff_mul_sub_eq_zero {k : ℕ} {a b b₂ : Tower R k} (h : a * b = 1) :
    a * b₂ = 1 ↔ a * (b₂ - b) = 0 := by
  rw [mul_sub, h, sub_eq_zero]

end Tower

end CayleyDickson
