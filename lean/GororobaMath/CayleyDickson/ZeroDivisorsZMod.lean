/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.ZeroDivisors
public import Mathlib.Data.ZMod.Basic

/-!
# Zero divisors over the prime fields

Convention: `Tower (ZMod p) k` is the tower of `GororobaMath.CayleyDickson.Tower` over the prime
field `ZMod p` with the identity as star, `starRingOfComm` (so `star a = a` for every
`a : ZMod p`), with the product `(a, b) (c, d) = (a c - star d b, d a + b star c)`.

`Tower.exists_zero_divisor` holds over every nontrivial ring with a star; the prime field
`ZMod p` is one, for every prime `p`, with the star instance `starRingOfComm`.

## Main results

* `Tower.exists_zero_divisor_zmod`: at every level `k ≥ 4`, over `ZMod p` for every prime `p`, two
  nonzero elements have product zero.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

/-- The identity as star on `ZMod p`: `starRingOfComm`, Mathlib's star on a commutative ring that
is the identity. -/
local instance instStarRingZMod (p : ℕ) : StarRing (ZMod p) := starRingOfComm

/-- At every level `k ≥ 4` the tower over `ZMod p`, with the identity as star, holds two nonzero
elements with zero product, for every prime `p`. -/
theorem exists_zero_divisor_zmod (p : ℕ) [Fact p.Prime] {k : ℕ} (hk : 4 ≤ k) :
    ∃ a b : Tower (ZMod p) k, a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 :=
  exists_zero_divisor hk

end Tower

end CayleyDickson
