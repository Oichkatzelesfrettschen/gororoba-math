/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TraceForm
public import GororobaMath.CayleyDickson.BaseChange

/-!
# The flexible law over every commutative ring

Convention: `Tower R k` is the `k`-fold Cayley-Dickson double of a commutative ring `R` whose
star is the identity (`TrivialStar R`), with the product
`(a, b) (c, d) = (a c - star d b, d a + b star c)` of `GororobaMath.CayleyDickson.Tower`, and
`Tower.map φ k` of `GororobaMath.CayleyDickson.BaseChange` applies a ring homomorphism `φ` to every
coordinate. `Tower.generic k v` is the element `∑ p, v p • e R k p` with coordinates `v`.

## Main results

* `Tower.mul_mul_self_eq'`: `(x * y) * x = x * (y * x)` at every level over every commutative
  ring with the identity as star, with no hypothesis on `2`. `Tower.mul_mul_self_eq` of
  `GororobaMath.CayleyDickson.TraceForm` proves it when `2` is left regular; here the identity over
  the polynomial ring on the coordinates of `x` and `y`, in which `2` is regular, maps to the
  given ring through `Tower.map`. The Rocq original is `flexible` of the functor `CdTower` in
  `rocq/quantum/CdTowerDomain.v`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

noncomputable section Universal

universe v

/-- The element of `Tower R k` with coordinates `v`: `∑ p, v p • e R k p`. -/
def generic (k : ℕ) (v : BitVec k → R) : Tower R k := ∑ p, v p • e R k p

omit [TrivialStar R] in
theorem repr_generic {k : ℕ} (x : Tower R k) : generic k (fun p => (basis R k).repr x p) = x := by
  have h := (basis R k).sum_repr x
  simp only [basis_apply] at h
  exact h

omit [TrivialStar R] in
theorem map_generic {S : Type v} [CommRing S] [StarRing S] [TrivialStar S] (φ : R →+* S) {k : ℕ}
    (v : BitVec k → R) : map φ k (generic k v) = generic k (fun p => φ (v p)) := by
  let f : Tower R k →+ Tower S k := AddMonoidHom.mk' (map φ k) (map_add φ k)
  have h : map φ k (generic k v) = f (generic k v) := rfl
  rw [h, generic, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  change map φ k (v p • e R k p) = _
  rw [map_smul, map_e]

/-- The coordinates of the integer polynomial ring in the coordinates of two elements of
`Tower R k`, with the identity as star. -/
local instance instStarUniversal {σ : Type} : StarRing (MvPolynomial σ ℤ) := starRingOfComm

local instance instTrivialStarUniversal {σ : Type} : TrivialStar (MvPolynomial σ ℤ) :=
  ⟨fun _ => rfl⟩

/-- The flexible law `(x * y) * x = x * (y * x)` at every level over every commutative ring whose
star is the identity, with no hypothesis on `2`. Both sides are polynomial in the coordinates of
`x` and `y`, so the identity of `mul_mul_self_eq` over the polynomial ring `ℤ[X_p, Y_p]`, in which
`2` is regular, transports along the evaluation at the coordinates of `x` and `y` (`Tower.map`
is multiplicative). The Rocq original is `flexible` of the functor `CdTower` in
`rocq/quantum/CdTowerDomain.v`, stated there over an ordered domain; characteristic `2` is covered
here. -/
theorem mul_mul_self_eq' {k : ℕ} (x y : Tower R k) : x * y * x = x * (y * x) := by
  let φ : MvPolynomial (BitVec k ⊕ BitVec k) ℤ →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R)
      (Sum.elim (fun p => (basis R k).repr x p) (fun p => (basis R k).repr y p))
  let X : Tower (MvPolynomial (BitVec k ⊕ BitVec k) ℤ) k :=
    generic k fun p => MvPolynomial.X (Sum.inl p)
  let Y : Tower (MvPolynomial (BitVec k ⊕ BitVec k) ℤ) k :=
    generic k fun p => MvPolynomial.X (Sum.inr p)
  have hX : map φ k X = x := by
    rw [map_generic]
    simpa [φ] using repr_generic x
  have hY : map φ k Y = y := by
    rw [map_generic]
    simpa [φ] using repr_generic y
  have h := mul_mul_self_eq (mul_right_injective₀ two_ne_zero) X Y
  have h' := congrArg (map φ k) h
  rwa [map_mul, map_mul, map_mul, map_mul, hX, hY] at h'

end Universal

end Tower

end CayleyDickson
