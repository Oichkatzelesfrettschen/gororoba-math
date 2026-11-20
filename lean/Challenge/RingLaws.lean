/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Tower

/-!
# Challenge: kernel laws of the tower over a nonassociative star ring

This file restates, with `sorry` as each proof, the headline theorems that
`GororobaMath.CayleyDickson.RingLaws` proves and that the "Lean library" table of `README.md` names,
with the definitions those statements use. It imports the library modules that the
solution module imports. `lake comparator --config` with the JSON file beside this one
checks that each named theorem of the solution module has the statement written here
and depends only on `propext`, `Classical.choice` and `Quot.sound`. No library module
imports this file, and the admission gate does not build it.
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
  sorry

/-- For pure `a`, `a * z = 0` exactly when `star z * a = 0`. The Rocq original is
`pure_kernel_conj` of the functor `RingTower` in `rocq/quantum/CdTowerRing.v`. -/
theorem mul_eq_zero_iff_star_mul_of_star_eq_neg {k : ℕ} {a : Tower R k} (ha : star a = -a)
    (z : Tower R k) : a * z = 0 ↔ star z * a = 0 := by
  sorry

/-- For pure `a`, `v * a = 0` exactly when `a * star v = 0`. The Rocq original is
`pure_right_left_kernel` of `rocq/open/theories/CDPureDoublingKernel.v`. -/
theorem mul_eq_zero_iff_mul_star_of_star_eq_neg {k : ℕ} {a : Tower R k} (ha : star a = -a)
    (v : Tower R k) : v * a = 0 ↔ a * star v = 0 := by
  sorry

/-- For pure `a`, `(a, 0) * (c, d) = 0` exactly when `a * c = 0` and `a * star d = 0`. The Rocq
original is `pure_doubling_kernel_decomposition` of
`rocq/open/theories/CDPureDoublingKernel.v`. -/
theorem mk_mul_mk_eq_zero_iff_of_star_eq_neg {k : ℕ} {a : Tower R k} (ha : star a = -a)
    (c d : Tower R k) : mk a 0 * mk c d = 0 ↔ a * c = 0 ∧ a * star d = 0 := by
  sorry

end Tower

namespace Tower

variable {R : Type u} [NonAssocRing R] [StarRing R]

/-- The reflection `(a, b) ↦ (a, -b)` carries the annihilator of `x` onto that of its image at
every level `k + 1`. The Rocq original is `reflect_kernel` of the functor `RingTower` in
`rocq/quantum/CdTowerRing.v`. -/
theorem mul_eq_zero_iff_reflect_mul_reflect {k : ℕ} (x z : Tower R (k + 1)) :
    x * z = 0 ↔ CayleyDickson.reflect x * CayleyDickson.reflect z = 0 := by
  sorry

end Tower

end CayleyDickson
