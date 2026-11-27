/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.StiefelZeroDivisor
public import GororobaMath.CayleyDickson.BaseChange
public import Mathlib.Analysis.Complex.Basic

/-!
# Every real A_5 Stiefel element is a zero divisor

Convention: `Tower R k` is the Cayley-Dickson tower of `GororobaMath.CayleyDickson.Tower` over a
commutative ring `R` whose star is the identity, with the basis `Tower.e R k p`, `p : BitVec k`;
`dot k` is its trace form, `re k` the coordinate of `1`, and `Tower.map φ k` the coordinatewise
image under a ring homomorphism `φ`. `TrivStarComplex` is the field of complex numbers with the
identity as its star, the field of `Tower.stiefel_zero_divisor` that contains a square root `I`
of `-1`; Mathlib's own star on `ℂ` is conjugation, which has no `TrivialStar` instance.

The proof base-changes the real Stiefel element along `ofReal : ℝ →+* TrivStarComplex`, whose
`map` preserves `re`, `dot` and the product, applies `Tower.stiefel_zero_divisor`, and descends the
complex annihilator `x`. Its real and imaginary coordinate vectors `xr`, `xi` satisfy
`x = map xr + I • map xi`, and the coordinates of `map (y * xr) + I • map (y * xi)` are `0`, so both
`y * xr` and `y * xi` vanish, and one of `xr`, `xi` is nonzero.

## Main results

* `Tower.repr_map`: `map φ k` commutes with the coordinates, `repr (map φ k z) b = φ (repr z b)`.
* `Tower.stiefel_zero_divisor_real`: for pure `p`, `q` of `Tower ℝ 4` with `dot 4 p p = dot 4 q q`
  and `dot 4 p q = 0`, some `x ≠ 0` of `Tower ℝ 5` has `mk p q * x = 0`. The Rocq partner is
  `real_stiefel_zero_divisor` of `rocq/quantum/StiefelA5Real.v`.
-/

@[expose] public section

namespace CayleyDickson

/-- The complex numbers with the identity as star, so that `TrivialStar` holds. -/
def TrivStarComplex : Type := ℂ

namespace TrivStarComplex

noncomputable instance : Field TrivStarComplex := inferInstanceAs (Field ℂ)

instance : Star TrivStarComplex := ⟨id⟩

instance : TrivialStar TrivStarComplex := ⟨fun _ => rfl⟩

noncomputable instance : StarRing TrivStarComplex where
  star_involutive _ := rfl
  star_mul a b := mul_comm a b
  star_add _ _ := rfl

/-- The inclusion of the real numbers. -/
noncomputable def ofReal : ℝ →+* TrivStarComplex := Complex.ofRealHom

/-- The square root of `-1`. -/
noncomputable def I : TrivStarComplex := Complex.I

theorem I_mul_I : I * I = -1 := Complex.I_mul_I

theorem two_ne_zero' : (2 : TrivStarComplex) ≠ 0 := fun h => by
  have h' : (2 : ℂ) = 0 := h
  norm_num at h'

/-- The real part of a coordinate. -/
noncomputable def reC (z : TrivStarComplex) : ℝ := Complex.re z

/-- The imaginary part of a coordinate. -/
noncomputable def imC (z : TrivStarComplex) : ℝ := Complex.im z

theorem ext_parts {z w : TrivStarComplex} (h1 : reC z = reC w) (h2 : imC z = imC w) : z = w :=
  Complex.ext h1 h2

theorem reC_ofReal (r : ℝ) : reC (ofReal r) = r := Complex.ofReal_re r

theorem imC_ofReal (r : ℝ) : imC (ofReal r) = 0 := Complex.ofReal_im r

theorem reC_zero : reC 0 = 0 := Complex.zero_re

theorem imC_zero : imC 0 = 0 := Complex.zero_im

theorem reC_add_I_mul (a b : ℝ) : reC (ofReal a + I * ofReal b) = a := by
  change (↑a + Complex.I * ↑b : ℂ).re = a
  simp

theorem imC_add_I_mul (a b : ℝ) : imC (ofReal a + I * ofReal b) = b := by
  change (↑a + Complex.I * ↑b : ℂ).im = b
  simp

theorem eq_ofReal_add_I_mul (z : TrivStarComplex) : z = ofReal (reC z) + I * ofReal (imC z) := by
  change z = ((Complex.re z : ℝ) : ℂ) + Complex.I * ((Complex.im z : ℝ) : ℂ)
  exact (Complex.re_add_im z).symm.trans (by ring)

end TrivStarComplex

namespace Tower

universe u v

section Coordinates

variable {R : Type u} {S : Type v} [CommRing R] [StarRing R] [TrivialStar R]
  [CommRing S] [StarRing S] [TrivialStar S]

/-- The coordinatewise image as an additive homomorphism. -/
def mapAddHom (φ : R →+* S) (k : ℕ) : Tower R k →+ Tower S k :=
  AddMonoidHom.mk' (map φ k) (map_add φ k)

omit [TrivialStar R] [TrivialStar S] in
/-- The coordinates of `map φ k z` are the images of those of `z`. -/
theorem repr_map (φ : R →+* S) {k : ℕ} (z : Tower R k) (b : BitVec k) :
    (basis S k).repr (map φ k z) b = φ ((basis R k).repr z b) := by
  conv_lhs => rw [← (basis R k).sum_repr z]
  have h := map_sum (mapAddHom φ k) (fun c => (basis R k).repr z c • basis R k c) Finset.univ
  change map φ k (∑ c, (basis R k).repr z c • basis R k c) =
    ∑ c, map φ k ((basis R k).repr z c • basis R k c) at h
  rw [h]
  have he : ∀ x, (basis S k).repr (e S k x) b = if x = b then 1 else 0 := fun x => by
    rw [← basis_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [map_smul, basis_apply, map_e, map_sum]
  simp [he]

omit [TrivialStar R] [TrivialStar S] in
theorem re_map (φ : R →+* S) {k : ℕ} (z : Tower R k) : re k (map φ k z) = φ (re k z) := by
  rw [re_eq_repr_zero, re_eq_repr_zero, repr_map]

omit [TrivialStar R] [TrivialStar S] in
theorem dot_map (φ : R →+* S) {k : ℕ} (x y : Tower R k) :
    dot k (map φ k x) (map φ k y) = φ (dot k x y) := by
  rw [dot_eq_sum_repr, dot_eq_sum_repr, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [repr_map, repr_map, _root_.map_mul]

end Coordinates

open TrivStarComplex in
/-- Over the real numbers, a Stiefel element `mk p q` of `Tower ℝ 5` (pure halves of equal norm and
zero dot product) has a nonzero right annihilator: the complex annihilator of its base change has
real and imaginary coordinate vectors that annihilate it separately. -/
theorem stiefel_zero_divisor_real {p q : Tower ℝ 4} (hp : re 4 p = 0) (hq : re 4 q = 0)
    (hpp : dot 4 p p = dot 4 q q) (hpq : dot 4 p q = 0) :
    ∃ x : Tower ℝ 5, x ≠ 0 ∧ mk p q * x = 0 := by
  obtain ⟨x, hx0, hx⟩ := stiefel_zero_divisor (K := TrivStarComplex) two_ne_zero' I I_mul_I
    (p := map ofReal 4 p) (q := map ofReal 4 q)
    (by rw [re_map, hp, _root_.map_zero]) (by rw [re_map, hq, _root_.map_zero])
    (by rw [dot_map, dot_map, hpp]) (by rw [dot_map, hpq, _root_.map_zero])
  let fr : BitVec 5 → ℝ := fun b => reC ((basis TrivStarComplex 5).repr x b)
  let fi : BitVec 5 → ℝ := fun b => imC ((basis TrivStarComplex 5).repr x b)
  let xr : Tower ℝ 5 := (basis ℝ 5).repr.symm (Finsupp.equivFunOnFinite.symm fr)
  let xi : Tower ℝ 5 := (basis ℝ 5).repr.symm (Finsupp.equivFunOnFinite.symm fi)
  have hxr : ∀ b, (basis ℝ 5).repr xr b = fr b := fun b => by simp [xr]
  have hxi : ∀ b, (basis ℝ 5).repr xi b = fi b := fun b => by simp [xi]
  have hdec : x = map ofReal 5 xr + I • map ofReal 5 xi := by
    refine (basis TrivStarComplex 5).ext_elem fun b => ?_
    rw [_root_.map_add, _root_.map_smul, Finsupp.add_apply, Finsupp.smul_apply, repr_map,
      repr_map, hxr, hxi, smul_eq_mul]
    exact eq_ofReal_add_I_mul _
  have hy : map ofReal 5 (mk p q) = mk (map ofReal 4 p) (map ofReal 4 q) := rfl
  have hsum : map ofReal 5 (mk p q * xr) + I • map ofReal 5 (mk p q * xi) = 0 := by
    have h1 := hx
    rw [← hy, hdec, ← mulLeft_apply, _root_.map_add, _root_.map_smul, mulLeft_apply,
      mulLeft_apply, ← map_mul, ← map_mul] at h1
    exact h1
  have hcoord : ∀ b, ofReal ((basis ℝ 5).repr (mk p q * xr) b) +
      I * ofReal ((basis ℝ 5).repr (mk p q * xi) b) = 0 := fun b => by
    have := congrArg (fun z => (basis TrivStarComplex 5).repr z b) hsum
    simpa only [_root_.map_add, _root_.map_smul, Finsupp.add_apply, Finsupp.smul_apply, repr_map,
      smul_eq_mul, _root_.map_zero, Finsupp.zero_apply] using this
  have hzr : mk p q * xr = 0 := by
    refine (basis ℝ 5).ext_elem fun b => ?_
    have := congrArg reC (hcoord b)
    rw [reC_add_I_mul, reC_zero] at this
    simpa using this
  have hzi : mk p q * xi = 0 := by
    refine (basis ℝ 5).ext_elem fun b => ?_
    have := congrArg imC (hcoord b)
    rw [imC_add_I_mul, imC_zero] at this
    simpa using this
  by_cases hr : xr = 0
  · refine ⟨xi, fun hi => hx0 ?_, hzi⟩
    rw [hdec, hr, hi, map_zero, smul_zero, add_zero]
  · exact ⟨xr, hr, hzr⟩

end Tower

end CayleyDickson
