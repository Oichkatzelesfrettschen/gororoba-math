/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.BaseChange
public import GororobaMath.CayleyDickson.AnnihilatorSymmetry
public import GororobaMath.CayleyDickson.TraceForm

/-!
# Challenge: the order-three map of level 4

This file restates, with `sorry` as each proof, the headline theorems that
`GororobaMath.CayleyDickson.OrderThree` proves and that the "Lean library" table of `README.md` names,
with the definitions those statements use. It imports the library modules that the
solution module imports. `lake comparator --config` with the JSON file beside this one
checks that each named theorem of the solution module has the statement written here
and depends only on `propext`, `Classical.choice` and `Quot.sound`. No library module
imports this file, and the admission gate does not build it.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

/-- Twice the order-three map:
`(A, B) ↦ ((3 re A) • 1 - A + r3 • im B, (3 re B) • 1 - B - r3 • im A)` with `im y = y - re y • 1`.
It is `OrderThreeMap.psi2` of `rocq/quantum/CdTowerOrderThreeMap.v`. -/
def orderThree (r3 : R) {k : ℕ} : Tower R (k + 1) → Tower R (k + 1)
  | ⟨A, B⟩ =>
    mk ((3 * re k A) • (1 : Tower R k) - A + r3 • B - (r3 * re k B) • (1 : Tower R k))
      ((3 * re k B) • (1 : Tower R k) - B - r3 • A + (r3 * re k A) • (1 : Tower R k))

/-- The doubled order-three map commutes with the star at every level. The Rocq original is
`OrderThreeMap.psi2_conj` of `rocq/quantum/CdTowerOrderThreeMap.v`. -/
theorem orderThree_star (r3 : R) {k : ℕ} (x : Tower R (k + 1)) :
    orderThree r3 (star x) = star (orderThree r3 x) := by
  sorry

/-- The doubled order-three map is multiplicative up to the factor `2` on the sedenions over
every commutative ring with a square root of `3`: `psi2 x * psi2 y = 2 psi2 (x * y)`. The
proof splits both factors into their 16 coordinates and closes each of the 16 coordinate
identities by `grind` from `r3 * r3 = 3`. The Rocq original is `OrderThreeMap.psi2_mul` of
`rocq/quantum/CdTowerOrderThreeMap.v`, which transports the 256 basis checks over `ℤ[√3]`. -/
theorem orderThree_mul (r3 : R) (h3 : r3 * r3 = 3) (x y : Tower R 4) :
    orderThree r3 x * orderThree r3 y = (2 : R) • orderThree r3 (x * y) := by
  sorry

end Tower

end CayleyDickson
