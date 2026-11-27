/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.FiberCone.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# The Hilbert function of the fiber cone

Convention: `R` is a commutative local ring with maximal ideal `m` and residue field
`k = R ⧸ m`; `I` is an ideal with generators `f : Fin s → R`, and `fiberMap` of
`GororobaMath.FiberCone.Basic` is the surjection `k[y₁, …, yₛ] → F(I)`, `yᵢ ↦ fᵢ t`. The degree-`n`
piece of `F(I) = R[It] / m R[It]` is `FiberCone.piece I n = I ^ n ⧸ m • ⊤`, a `k`-module through
Mathlib's quotient-module instance. `FiberCone.fiberHilbert I n` is its `k`-dimension
(`Module.finrank`, which is `0` on an infinite-dimensional module; finiteness is
`FiberCone.finite_piece`).

The coefficient of `t ^ n` of the Rees image of a polynomial defines a `k`-linear map
`FiberCone.phi n : k[y] → piece I n` (on monomials `yᵈ ↦ [f ^ d]` in degree `n` and `0`
elsewhere), and an element of `k[y]` lies in the kernel of `fiberMap` exactly when every
`phi n` kills it: the extension `m R[It]` is the set of Rees elements whose `t ^ n`
coefficient lies in `m I ^ n` for every `n`.

## Main results

* `FiberCone.mem_map_maximalIdeal_iff`: the extension `m R[It]` is cut out by the coefficient
  conditions `coeff n ∈ m * I ^ n`.
* `FiberCone.fiberMap_eq_zero_iff`: `fiberMap q = 0` exactly when `phi n q = 0` for all `n`.
* `FiberCone.homogeneousComponent_mem_ker`: the kernel of `fiberMap` is a homogeneous ideal
  (no hypothesis beyond the statement).
* `FiberCone.pieceEquivRange`: `I ^ n / m I ^ n` is `k`-isomorphic to the image of the
  degree-`n` homogeneous polynomials under `fiberMap` (the map is graded).
* `FiberCone.fiberHilbert_eq_finrank_quotient`: `h_F(n)` is the dimension of the degree-`n`
  part of `k[y] / K` with `K = ker fiberMap`, the bridge from a presentation `F(I) = S / K` to
  the Hilbert function.
* `FiberCone.finite_piece`: each piece is finite over `k` when `I` is finitely generated.

## Open

The multiplicity of `F(I)` (the leading coefficient of the Hilbert polynomial) and the
rationality of the Hilbert series `∑ h_F(n) zⁿ` are not stated here; they wait on the Hilbert
polynomial of a quotient of a polynomial ring by a homogeneous ideal.
-/

@[expose] public section

open IsLocalRing

namespace FiberCone

variable {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)

/-- The degree-`n` piece `I ^ n / m I ^ n` of the fiber cone. -/
abbrev piece (n : ℕ) : Type _ :=
  ↥(I ^ n) ⧸ (maximalIdeal R • (⊤ : Submodule R ↥(I ^ n)))

/-- The fiber Hilbert function `h_F(n) = dim_k I ^ n / m I ^ n`. -/
noncomputable def fiberHilbert (n : ℕ) : ℕ :=
  Module.finrank (R ⧸ maximalIdeal R) (piece I n)

/-- The extension `m R[It]` is the set of Rees elements with `coeff n ∈ m I ^ n` for all `n`. -/
theorem mem_map_maximalIdeal_iff (x : reesAlgebra I) :
    x ∈ (maximalIdeal R).map (algebraMap R (reesAlgebra I)) ↔
      ∀ n, x.1.coeff n ∈ maximalIdeal R * I ^ n := by
  refine ⟨fun h n => ?_, fun h => ?_⟩
  · rw [← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map] at h
    induction h using Submodule.smul_induction_on' with
    | smul r hr m hm =>
      simpa using Ideal.mul_mem_mul hr ((mem_reesAlgebra_iff I _).mp m.2 n)
    | add x hx y hy memx memy => simpa using add_mem memx memy
  · rw [reesAlgebra.as_sum_support x]
    apply sum_mem (fun i hi => ?_)
    have {r : R} (h' : r ∈ maximalIdeal R * I ^ i) :
        (⟨Polynomial.monomial i r, reesAlgebra.monomial_mem.mpr (Ideal.mul_le_right h')⟩ :
          reesAlgebra I) ∈ (maximalIdeal R).map (algebraMap R (reesAlgebra I)) := by
      induction h' using Submodule.mul_induction_on' with
      | mem_mul_mem s hs t ht =>
        simp_rw [← smul_eq_mul s t, ← Polynomial.smul_monomial,
          ← SetLike.mk_smul_mk (hx := reesAlgebra.monomial_mem.mpr ht), Algebra.smul_def]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hs)
      | add s1 hs1 s2 hs2 mem1 mem2 => simpa using add_mem mem1 mem2
    exact this (h i)

variable {I} {s : ℕ} (f : Fin s → R) (hf : ∀ i, f i ∈ I)

omit [IsLocalRing R] in
theorem prod_polynomial_monomial {ι : Type*} (t : Finset ι) (e : ι → ℕ) (a : ι → R) :
    ∏ i ∈ t, Polynomial.monomial (e i) (a i) =
      Polynomial.monomial (∑ i ∈ t, e i) (∏ i ∈ t, a i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj, ih,
      Polynomial.monomial_mul_monomial]

omit [IsLocalRing R] in
/-- The Rees image of a monomial is a monomial in `t` of the same degree. -/
theorem reesMap_monomial_val (d : Fin s →₀ ℕ) (c : R) :
    (reesMap f hf (MvPolynomial.monomial d c)).1 =
      Polynomial.monomial d.degree (c * d.prod fun i e => f i ^ e) := by
  have h : (reesMap f hf (MvPolynomial.monomial d c)).1 =
      (reesAlgebra I).val (algebraMap R (reesAlgebra I) c *
        d.prod fun i e => gen f hf i ^ e) := by
    rw [reesMap, MvPolynomial.aeval_monomial]; rfl
  rw [h, map_mul, Finsupp.prod, map_prod]
  have h2 : ∀ i, (reesAlgebra I).val (gen f hf i ^ d i) =
      Polynomial.monomial (d i) (f i ^ d i) := fun i => by
    rw [map_pow]
    simp [gen, Polynomial.monomial_pow]
  simp_rw [h2]
  rw [prod_polynomial_monomial, Finsupp.degree_apply, ← Finsupp.prod]
  simp [Polynomial.C_mul_monomial]

omit [IsLocalRing R] in
theorem coeff_reesMap_monomial (d : Fin s →₀ ℕ) (c : R) (m : ℕ) :
    ((reesMap f hf (MvPolynomial.monomial d c)).1).coeff m =
      if d.degree = m then c * d.prod (fun i e => f i ^ e) else 0 := by
  rw [reesMap_monomial_val, Polynomial.coeff_monomial]

variable (I) in
/-- The coefficient of `t ^ m` of a Rees element, in `I ^ m`. -/
noncomputable def coefLin (m : ℕ) : reesAlgebra I →ₗ[R] ↥(I ^ m) where
  toFun x := ⟨x.1.coeff m, (mem_reesAlgebra_iff I _).mp x.2 m⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' r x := Subtype.ext (by simp)

/-- The `t ^ m` coefficient of the Rees image of an `R`-polynomial, modulo `m I ^ m`. -/
noncomputable def psi (m : ℕ) : MvPolynomial (Fin s) R →ₗ[R] piece I m :=
  Submodule.mkQ _ ∘ₗ coefLin I m ∘ₗ (reesMap f hf).toLinearMap

theorem psi_apply (m : ℕ) (p : MvPolynomial (Fin s) R) :
    psi f hf m p = Submodule.Quotient.mk (coefLin I m (reesMap f hf p)) :=
  rfl

theorem psi_monomial_of_degree_ne {d : Fin s →₀ ℕ} {c : R} {m : ℕ} (h : d.degree ≠ m) :
    psi f hf m (MvPolynomial.monomial d c) = 0 := by
  have : coefLin I m (reesMap f hf (MvPolynomial.monomial d c)) = 0 :=
    Subtype.ext (by simp [coefLin, coeff_reesMap_monomial, h])
  rw [psi_apply, this]
  simp

/-- The `k`-linear degree-`n` coefficient map `k[y] → I ^ n / m I ^ n`: `yᵈ` goes to
the class of `f ^ d` in degree `n` and to `0` in every other degree. -/
noncomputable def phi (m : ℕ) :
    MvPolynomial (Fin s) (R ⧸ maximalIdeal R) →ₗ[R ⧸ maximalIdeal R] piece I m :=
  (MvPolynomial.basisMonomials (Fin s) (R ⧸ maximalIdeal R)).constr (R ⧸ maximalIdeal R)
    (fun d => psi f hf m (MvPolynomial.monomial d 1))

theorem phi_monomial (m : ℕ) (d : Fin s →₀ ℕ) (c : R ⧸ maximalIdeal R) :
    phi f hf m (MvPolynomial.monomial d c) = c • psi f hf m (MvPolynomial.monomial d 1) := by
  have h : MvPolynomial.monomial d c = c • MvPolynomial.monomial d (1 : R ⧸ maximalIdeal R) := by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hb : phi f hf m (MvPolynomial.monomial d 1) = psi f hf m (MvPolynomial.monomial d 1) := by
    have := Module.Basis.constr_basis (MvPolynomial.basisMonomials (Fin s) (R ⧸ maximalIdeal R))
      (R ⧸ maximalIdeal R) (fun d => psi f hf m (MvPolynomial.monomial d 1)) d
    simp only [MvPolynomial.coe_basisMonomials] at this
    exact this
  rw [h, map_smul, hb]

theorem quot_smul_eq (m : ℕ) (c : R) (y : piece I m) :
    Ideal.Quotient.mk (maximalIdeal R) c • y = c • y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rfl

/-- `phi` computes on the reduction of an `R`-polynomial through `psi`. -/
theorem phi_map (m : ℕ) (p : MvPolynomial (Fin s) R) :
    phi f hf m (MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R)) p) = psi f hf m p := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [MvPolynomial.map_monomial, phi_monomial, quot_smul_eq, ← map_smul]
    congr 1
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]

theorem fiberMap_map (p : MvPolynomial (Fin s) R) :
    fiberMap f hf (MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R)) p) =
      Ideal.Quotient.mk _ (reesMap f hf p) :=
  RingHom.congr_fun (fiberMap_comp_map f hf) p

/-- A polynomial over `k` maps to zero in the fiber cone exactly when all its degree
coefficients vanish. -/
theorem fiberMap_eq_zero_iff (q : MvPolynomial (Fin s) (R ⧸ maximalIdeal R)) :
    fiberMap f hf q = 0 ↔ ∀ m, phi f hf m q = 0 := by
  obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective q
  rw [fiberMap_map, Ideal.Quotient.eq_zero_iff_mem, mem_map_maximalIdeal_iff]
  refine forall_congr' fun m => ?_
  rw [phi_map, psi_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff, smul_eq_mul]
  rfl

theorem phi_monomial_of_degree_ne {d : Fin s →₀ ℕ} {c : R ⧸ maximalIdeal R} {m : ℕ}
    (h : d.degree ≠ m) : phi f hf m (MvPolynomial.monomial d c) = 0 := by
  rw [phi_monomial, psi_monomial_of_degree_ne f hf h, smul_zero]

/-- Keeping the degree-`m` component leaves the degree-`m` coefficient unchanged. -/
theorem phi_homogeneousComponent_self (m : ℕ) (q : MvPolynomial (Fin s) (R ⧸ maximalIdeal R)) :
    phi f hf m (MvPolynomial.homogeneousComponent m q) = phi f hf m q := by
  induction q using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c rfl)]
    by_cases hm : m = d.degree
    · simp only [hm, ↓reduceIte]
    · simp only [hm, ↓reduceIte, map_zero]
      exact (phi_monomial_of_degree_ne f hf (fun h => hm h.symm)).symm
  | add p q hp hq => simp only [map_add, hp, hq]

/-- Keeping the degree-`m` component kills every other degree coefficient. -/
theorem phi_homogeneousComponent_ne {j m : ℕ} (h : j ≠ m)
    (q : MvPolynomial (Fin s) (R ⧸ maximalIdeal R)) :
    phi f hf j (MvPolynomial.homogeneousComponent m q) = 0 := by
  induction q using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c rfl)]
    by_cases hm : m = d.degree
    · simp only [hm, ↓reduceIte]
      exact phi_monomial_of_degree_ne f hf (fun hd => h (hd.symm.trans hm.symm))
    · simp only [hm, ↓reduceIte, map_zero]
  | add p q hp hq => rw [map_add, map_add, hp, hq, add_zero]

theorem phi_of_mem_homogeneous_ne {n j : ℕ} (h : j ≠ n)
    {q : MvPolynomial (Fin s) (R ⧸ maximalIdeal R)}
    (hq : q ∈ MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ maximalIdeal R) n) :
    phi f hf j q = 0 := by
  have e : MvPolynomial.homogeneousComponent n q = q := by
    rw [MvPolynomial.homogeneousComponent_of_mem hq]
    simp
  have := phi_homogeneousComponent_ne f hf h q
  rwa [e] at this

/-- On a homogeneous polynomial of degree `n`, `fiberMap` vanishes exactly when the degree-`n`
coefficient does. -/
theorem fiberMap_eq_zero_iff_of_mem_homogeneous {n : ℕ}
    {q : MvPolynomial (Fin s) (R ⧸ maximalIdeal R)}
    (hq : q ∈ MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ maximalIdeal R) n) :
    fiberMap f hf q = 0 ↔ phi f hf n q = 0 := by
  refine ⟨fun h => (fiberMap_eq_zero_iff f hf q).mp h n, fun h => ?_⟩
  refine (fiberMap_eq_zero_iff f hf q).mpr fun j => ?_
  by_cases hj : j = n
  · subst hj; exact h
  · exact phi_of_mem_homogeneous_ne f hf hj hq

/-- The kernel of `fiberMap` is a homogeneous ideal: it contains each homogeneous component of
each of its elements. -/
theorem homogeneousComponent_mem_ker {q : MvPolynomial (Fin s) (R ⧸ maximalIdeal R)}
    (hq : fiberMap f hf q = 0) (m : ℕ) :
    fiberMap f hf (MvPolynomial.homogeneousComponent m q) = 0 := by
  rw [fiberMap_eq_zero_iff] at hq ⊢
  intro j
  by_cases hj : j = m
  · subst hj; rw [phi_homogeneousComponent_self]; exact hq j
  · exact phi_homogeneousComponent_ne f hf hj q

/-- Every class of `I ^ n / m I ^ n` is the degree-`n` coefficient of a homogeneous polynomial of
degree `n`. -/
theorem exists_homogeneous_phi_eq (hI : Ideal.span (Set.range f) = I) (n : ℕ) (y : piece I n) :
    ∃ q ∈ MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ maximalIdeal R) n, phi f hf n q = y := by
  obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨p, hp⟩ := reesMap_surjective f hf hI
    ⟨Polynomial.monomial n a, reesAlgebra.monomial_mem.mpr ha⟩
  refine ⟨MvPolynomial.homogeneousComponent n
    (MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R)) p),
    MvPolynomial.homogeneousComponent_mem _ _, ?_⟩
  rw [phi_homogeneousComponent_self, phi_map, psi_apply, hp]
  congr 1
  exact Subtype.ext (by simp [coefLin])

/-- Over a ring, a surjection and a second map with the same kernel give an
isomorphism of the target of the first with the range of the second. -/
noncomputable def equivRangeOfKerEq {K V W X : Type*} [Ring K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X] (g : V →ₗ[K] W) (h : V →ₗ[K] X)
    (hg : Function.Surjective g) (hk : ∀ x, g x = 0 ↔ h x = 0) :
    W ≃ₗ[K] ↥(LinearMap.range h) :=
  (g.quotKerEquivOfSurjective hg).symm.trans
    ((Submodule.quotEquivOfEq _ _ (Submodule.ext fun x => hk x)).trans h.quotKerEquivRange)

variable (n : ℕ)

/-- The degree-`n` coefficient map on the homogeneous polynomials of degree `n`. -/
noncomputable def phiHom :
    ↥(MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ maximalIdeal R) n) →ₗ[R ⧸ maximalIdeal R]
      piece I n :=
  phi f hf n ∘ₗ (MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ maximalIdeal R) n).subtype

/-- `fiberMap` on the homogeneous polynomials of degree `n`. -/
noncomputable def fiberHom :
    ↥(MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ maximalIdeal R) n) →ₗ[R ⧸ maximalIdeal R]
      fiberCone I :=
  (fiberMap f hf).toLinearMap ∘ₗ
    (MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ maximalIdeal R) n).subtype

theorem phiHom_eq_zero_iff (x : ↥(MvPolynomial.homogeneousSubmodule (Fin s)
    (R ⧸ maximalIdeal R) n)) : phiHom f hf n x = 0 ↔ fiberHom f hf n x = 0 :=
  (fiberMap_eq_zero_iff_of_mem_homogeneous f hf x.2).symm

theorem ker_fiberHom_eq_comap : LinearMap.ker (fiberHom f hf n) =
    Submodule.comap (MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ maximalIdeal R) n).subtype
      ((RingHom.ker (fiberMap f hf)).restrictScalars (R ⧸ maximalIdeal R)) := by
  ext ⟨q, hq⟩
  exact Iff.rfl

theorem phiHom_surjective (hI : Ideal.span (Set.range f) = I) :
    Function.Surjective (phiHom f hf n) := fun y => by
  obtain ⟨q, hq, h⟩ := exists_homogeneous_phi_eq f hf hI n y
  exact ⟨⟨q, hq⟩, h⟩

/-- `I ^ n / m I ^ n` is the image of the degree-`n` homogeneous polynomials under the graded
map `fiberMap`: the surjection `phiHom` shares its kernel with `fiberHom`. -/
noncomputable def pieceEquivRange (hI : Ideal.span (Set.range f) = I) :
    piece I n ≃ₗ[R ⧸ maximalIdeal R] ↥(LinearMap.range (fiberHom f hf n)) := by
  have e := equivRangeOfKerEq (K := R ⧸ maximalIdeal R)
    (V := ↥(MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ maximalIdeal R) n))
    (W := piece I n) (X := fiberCone I) (phiHom f hf n) (fiberHom f hf n)
    (phiHom_surjective f hf n hI) (phiHom_eq_zero_iff f hf n)
  exact e

theorem range_fiberHom_eq_map : LinearMap.range (fiberHom f hf n) =
    Submodule.map (fiberMap f hf).toLinearMap
      (MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ maximalIdeal R) n) := by
  rw [fiberHom, LinearMap.range_comp, Submodule.range_subtype]

/-- The fiber Hilbert function is the dimension of the degree-`n` image of `fiberMap`. -/
theorem fiberHilbert_eq_finrank_map (hI : Ideal.span (Set.range f) = I) :
    fiberHilbert I n = Module.finrank (R ⧸ maximalIdeal R)
      ↥(Submodule.map (fiberMap f hf).toLinearMap
        (MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ maximalIdeal R) n)) := by
  rw [← range_fiberHom_eq_map]
  exact LinearEquiv.finrank_eq (pieceEquivRange f hf n hI)

/-- The fiber Hilbert function is the dimension of the degree-`n` part of `k[y] / K` with
`K = ker fiberMap` (the image of the degree-`n` homogeneous polynomials in the quotient ring),
and `K` is homogeneous by `homogeneousComponent_mem_ker`. -/
theorem fiberHilbert_eq_finrank_quotient (hI : Ideal.span (Set.range f) = I) :
    fiberHilbert I n = Module.finrank (R ⧸ maximalIdeal R)
      ↥(Submodule.map
        (Ideal.Quotient.mkₐ (R ⧸ maximalIdeal R) (RingHom.ker (fiberMap f hf))).toLinearMap
        (MvPolynomial.homogeneousSubmodule (Fin s) (R ⧸ maximalIdeal R) n)) := by
  rw [fiberHilbert_eq_finrank_map f hf n hI]
  have hcomp : (fiberMap f hf).toLinearMap =
      (Ideal.kerLiftAlg (fiberMap f hf)).toLinearMap ∘ₗ
        (Ideal.Quotient.mkₐ (R ⧸ maximalIdeal R) (RingHom.ker (fiberMap f hf))).toLinearMap := by
    exact LinearMap.ext fun x => (Ideal.kerLiftAlg_mk (fiberMap f hf) x).symm
  rw [hcomp, Submodule.map_comp]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective
    (Ideal.kerLiftAlg (fiberMap f hf)).toLinearMap
    (Ideal.kerLiftAlg_injective (fiberMap f hf)) _)).symm

/-- With `I` finitely generated each piece is finite over `k`. -/
theorem finite_piece (hI : Ideal.span (Set.range f) = I) :
    Module.Finite (R ⧸ maximalIdeal R) (piece I n) := by
  have hfg : I.FG := by
    rw [← hI]; exact Submodule.fg_span (Set.finite_range f)
  have h1 : Module.Finite R ↥(I ^ n) := Module.Finite.of_fg (Ideal.FG.pow hfg)
  exact Module.Finite.of_restrictScalars_finite R _ _

end FiberCone
