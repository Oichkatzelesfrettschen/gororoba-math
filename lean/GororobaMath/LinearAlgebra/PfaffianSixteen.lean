/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.LinearAlgebra.PfaffianForm
public import GororobaMath.CayleyDickson.Tower

/-!
# The bordered sixteen-by-sixteen matrix and the right-hand side of its Pfaffian

Convention: `borderedA z t` is the matrix of the level-4 left multiplication by a pure element
bordered by a vector: row and column `0` carry `-t b` and `t a`, and for `a ≠ b` both nonzero the
entry is `Tower.sign 4 (a ^^^ b) b * z (a ^^^ b)`, the `e_(a xor b) * e_b` coefficient times the
coordinate of `z` at `a ^^^ b`, which is `cd_sign(16, a xor b, b) * z_(a xor b)`. The vectors `z`
and `t` are functions `ℕ → R` read at `1, ..., 15`. With `Q = z.z`, `U = u.u`, `V = v.v`,
`W = u.v` for `u = (z_1, ..., z_7)` and `v = (z_9, ..., z_15)`, `Δ = U V - W²` and `G = Q² - 4 Δ`,
the Pfaffian of `borderedA z t` on the indices `0, ..., 15` is `-(z.t) Q G`
(`PfaffianSixteenSchur.pfaffian_sixteen`).

The Rocq partners are `Amat` and `rhs` of `rocq/quantum/StiefelA5Certificate.v`, and
`pf_A_eval` of `rocq/quantum/StiefelA5Pfaffian.v` states the identity there.

## Main definitions

* `PfaffianSixteen.borderedA`, `PfaffianSixteen.rhsv` and the sums `qv`, `uv`, `vv`, `wv`, `gv`.
-/

@[expose] public section

namespace PfaffianSixteen

variable {R : Type*} [CommRing R]

/-- The bordered matrix over `R`. -/
def borderedA (z t : ℕ → R) (a b : ℕ) : R :=
  if a = b then 0 else if a = 0 then -t b else if b = 0 then t a
  else (CayleyDickson.Tower.sign 4 (BitVec.ofNat 4 (a ^^^ b)) (BitVec.ofNat 4 b) : R) * z (a ^^^ b)

/-- `Q = z.z` over `R`. -/
def qv (z : ℕ → R) : R := ∑ k ∈ Finset.range 15, z (k + 1) * z (k + 1)
/-- `U = u.u` over `R`. -/
def uv (z : ℕ → R) : R := ∑ k ∈ Finset.range 7, z (k + 1) * z (k + 1)
/-- `V = v.v` over `R`. -/
def vv (z : ℕ → R) : R := ∑ k ∈ Finset.range 7, z (k + 9) * z (k + 9)
/-- `W = u.v` over `R`. -/
def wv (z : ℕ → R) : R := ∑ k ∈ Finset.range 7, z (k + 1) * z (k + 9)
/-- `G = Q² - 4 (U V - W²)` over `R`. -/
def gv (z : ℕ → R) : R := qv z ^ 2 - 4 * (uv z * vv z - wv z ^ 2)
/-- The right-hand side `-(z.t) Q G` over `R`. -/
def rhsv (z t : ℕ → R) : R := -(∑ k ∈ Finset.range 15, z (k + 1) * t (k + 1)) * qv z * gv z

end PfaffianSixteen
