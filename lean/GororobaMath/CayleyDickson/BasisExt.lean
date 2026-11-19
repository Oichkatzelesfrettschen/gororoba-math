/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AssociatorSpace

/-!
# Multiplicative maps are decided on the basis

Convention: `Tower R k` is the tower of `GororobaMath.CayleyDickson.Tower` over a
commutative ring `R` whose star is the identity, with the product
`(a, b) (c, d) = (a c - star d b, d a + b star c)` and the basis `Tower.e R k p`,
`p : BitVec k`, of `GororobaMath.CayleyDickson.TowerModule` (`Tower.basis`), top
bit outermost. Left and right multiplication are `R`-linear (`Tower.mulLeft`,
`Tower.mulRight`).

The product is `R`-bilinear, so an `R`-linear map `f` with
`f (e i * e j) = f (e i) * f (e j)` for all basis indices preserves every product:
for fixed `i` both sides of `f (e i * y) = f (e i) * f y` are linear in `y` and
agree on the basis, and then both sides of `f (x * y) = f x * f y` are linear in `x`.

## Main results

* `Tower.map_mul_of_map_e_mul_e`: the Rocq original is `multiplicative_by_basis`
  of the functor `RingTowerBasis` in `rocq/quantum/CdTowerRingBasis.v`, whose
  index `i < 2 ^ k` is `p.toNat` here.
* `Tower.leibniz_of_leibniz_e`: the same argument for the Leibniz rule
  `f (x * y) = f x * y + x * f y`, the Rocq `derivation_by_basis` of the same functor.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

/-- A linear map of `Tower R k` that preserves the products of all pairs of basis
elements preserves every product. The Rocq original is `multiplicative_by_basis` of
the functor `RingTowerBasis` in `rocq/quantum/CdTowerRingBasis.v`. -/
theorem map_mul_of_map_e_mul_e {k : ℕ} (f : Tower R k →ₗ[R] Tower R k)
    (h : ∀ i j, f (e R k i * e R k j) = f (e R k i) * f (e R k j)) (x y : Tower R k) :
    f (x * y) = f x * f y := by
  have hrow : ∀ i z, f (e R k i * z) = f (e R k i) * f z := by
    intro i
    have hl : f ∘ₗ mulLeft R k (e R k i) = mulLeft R k (f (e R k i)) ∘ₗ f :=
      (basis R k).ext fun j => by
        simp only [LinearMap.comp_apply, mulLeft_apply, basis_apply, h]
    exact fun z => LinearMap.congr_fun hl z
  have hr : f ∘ₗ mulRight R k y = mulRight R k (f y) ∘ₗ f :=
    (basis R k).ext fun i => by
      simp only [LinearMap.comp_apply, mulRight_apply, basis_apply, hrow]
  exact LinearMap.congr_fun hr x

/-- A linear map of `Tower R k` that satisfies the Leibniz rule on all pairs of basis elements
satisfies it on every pair. The Rocq original is `derivation_by_basis` of the functor
`RingTowerBasis` in `rocq/quantum/CdTowerRingBasis.v`. -/
theorem leibniz_of_leibniz_e {k : ℕ} (f : Tower R k →ₗ[R] Tower R k)
    (h : ∀ i j, f (e R k i * e R k j) = f (e R k i) * e R k j + e R k i * f (e R k j))
    (x y : Tower R k) : f (x * y) = f x * y + x * f y := by
  have hrow : ∀ i z, f (e R k i * z) = f (e R k i) * z + e R k i * f z := by
    intro i
    have hl : f ∘ₗ mulLeft R k (e R k i) =
        mulLeft R k (f (e R k i)) + mulLeft R k (e R k i) ∘ₗ f :=
      (basis R k).ext fun j => by
        simp only [LinearMap.comp_apply, LinearMap.add_apply, mulLeft_apply, basis_apply, h]
    exact fun z => LinearMap.congr_fun hl z
  have hr : f ∘ₗ mulRight R k y = mulRight R k y ∘ₗ f + mulRight R k (f y) :=
    (basis R k).ext fun i => by
      simp only [LinearMap.comp_apply, LinearMap.add_apply, mulRight_apply, basis_apply, hrow]
  exact LinearMap.congr_fun hr x

/-- The identity map meets the hypothesis, at level 5 over the rationals. -/
example (x y : Tower ℚ 5) :
    (LinearMap.id : Tower ℚ 5 →ₗ[ℚ] Tower ℚ 5) (x * y) =
      (LinearMap.id : Tower ℚ 5 →ₗ[ℚ] Tower ℚ 5) x * (LinearMap.id : Tower ℚ 5 →ₗ[ℚ] Tower ℚ 5) y :=
  map_mul_of_map_e_mul_e LinearMap.id (fun _ _ => rfl) x y

end Tower

end CayleyDickson
