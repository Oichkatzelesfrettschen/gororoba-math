/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Tower

/-!
# Challenge: involution and recursion laws of the sign

This file restates, with `sorry` as each proof, the headline theorems that the solution
module proves and that the "Lean library" table of `README.md` names, with the
definitions those statements use. It imports the library modules that the solution
module imports. `lake comparator --config` with the JSON file beside this one checks
that each named theorem of the solution module has the statement written here and
depends only on `propext`, `Classical.choice` and `Quot.sound`. No library module
imports this file, and the admission gate does not build it.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

/-- For `b ≠ 0`, the signs of `e a * e b` and `e (a ^^^ b) * e b` differ: right multiplication by
`e b` twice negates every basis unit. The Rocq original is `sigma_right_involution` of
`rocq/quantum/CdTowerBasisSign.v`. -/
theorem negSign_xor_left_right {k : ℕ} (a b : BitVec k) (hb : b ≠ 0#k) :
    (negSign k a b ^^ negSign k (a ^^^ b) b) = true := by
  sorry

/-- The cochain recursion of Albuquerque and Majid, by the top bit of each index. -/
def amExponent : (k : ℕ) → BitVec k → BitVec k → Bool
  | 0, _, _ => false
  | k + 1, x, y =>
    xor (if x.msb then amExponent k (y.setWidth k) (x.setWidth k)
        else amExponent k (x.setWidth k) (y.setWidth k))
      (xor (y.msb && amExponent k (x.setWidth k) (x.setWidth k)) (x.msb && y.msb))

/-- The recursion of Albuquerque and Majid (Corollary 4.3) gives `negSign k b a`. The Rocq original
is `am_sign` of `rocq/quantum/CdTowerBasisSign.v`, whose `am_exponent k a b` is
`amExponent k a b`. -/
theorem amExponent_eq : ∀ (k : ℕ) (a b : BitVec k), amExponent k a b = negSign k b a := by
  sorry

end Tower

end CayleyDickson
