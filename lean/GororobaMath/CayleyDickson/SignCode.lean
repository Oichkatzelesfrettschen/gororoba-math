/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Tower

/-!
# The Schreier exponent as a coboundary of the sign cochain

Convention: `Tower.negSign k p q` (`GororobaMath.CayleyDickson.Tower`) is the Boolean sign of
`e p * e q = ± e (p ^^^ q)` with indices `p q : BitVec k`, `true` meaning `-1`; the indices form
the group `BitVec k` under `^^^`. `Tower.schreier l r x` is the exponent that the three products
`e l * (e r * e x)`, `(e l * e r) * e x` share beyond the sign of `e l * e r`: the sum of
`negSign r x`, `negSign l (r ^^^ x)` and `negSign (l ^^^ r) x`.

## Main results

* `Tower.schreier_xor_schreier_zero`: the exponent normalized at `x = 0` is the group coboundary
  `negSign r x + negSign l (r ^^^ x) + negSign (l ^^^ r) x + negSign l r` of the sign cochain
  over the XOR group. The Rocq original is `normalized_schreier_is_coboundary` of
  `rocq/open/theories/BooleanCochainFiltration.v`, which proves it in a section over any group
  and any cochain normalized at the identity; Lean states the instance of the tower cochain on
  `BitVec k`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

/-- The Schreier exponent of the triple `(l, r, x)`. -/
def schreier {k : ℕ} (l r x : BitVec k) : Bool :=
  negSign k r x ^^ negSign k l (r ^^^ x) ^^ negSign k (l ^^^ r) x

/-- The Schreier exponent normalized at `x = 0` is the coboundary of the sign cochain. The Rocq
original is `normalized_schreier_is_coboundary` of
`rocq/open/theories/BooleanCochainFiltration.v`. -/
theorem schreier_xor_schreier_zero {k : ℕ} (l r x : BitVec k) :
    (schreier l r x ^^ schreier l r 0#k) =
      (negSign k r x ^^ negSign k l (r ^^^ x) ^^ negSign k (l ^^^ r) x ^^ negSign k l r) := by
  unfold schreier
  rw [BitVec.xor_zero, negSign_zero_right, negSign_zero_right, Bool.xor_false, Bool.false_xor]

end Tower

end CayleyDickson
