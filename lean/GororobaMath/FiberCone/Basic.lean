/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.KrullDimension.Field

/-!
# The fiber cone of an ideal and the polynomial fiber

Convention: `R` is a commutative local ring with maximal ideal `m` and residue field
`k = R ⧸ m`. The Rees algebra of an ideal `I` is Mathlib's `reesAlgebra I`, the subalgebra of
`R[X]` whose `n`-th coefficient lies in `I ^ n`. The fiber cone is
`F(I) = reesAlgebra I ⧸ m · reesAlgebra I`; its degree-`n` piece is `I ^ n / m I ^ n`
(`Ideal.map` of `m` along the structure map of the Rees algebra, which is the extension of `m`).
`F(I)` is a `k`-algebra through the structure map of `R`, which kills `m`.

For generators `f : Fin s → R` of `I`, the map `FiberCone.fiberMap` is the `k`-algebra
homomorphism `k[y₁, …, yₛ] → F(I)` with `yᵢ ↦` class of `fᵢ t`. It is surjective, and
`IsPolynomialFiber` says it is injective, so that `F(I) = k[y]`. The Krull dimension of `F(I)`
is `ringKrullDim`, the analytic spread of `I` when `R` is Noetherian.

## Main results

* `FiberCone.fiberMap_surjective`: the map is onto when the `fᵢ` generate `I`.
* `FiberCone.isPolynomialFiber_iff`: the fiber is polynomial exactly when
  `ringKrullDim F(I) = s`. No Noetherian hypothesis on `R` enters: the dimension lemmas apply to
  the polynomial ring over the field `k`.
* `FiberCone.isPolynomialFiber_iff_ker_eq`: the same condition as an equality of ideals of
  `R[y]`: the kernel of `R[y] → F(I)` is `m R[y]`.
* `FiberCone.not_isPolynomialFiber_of_dim_lt`: if `dim F(I) ≤ dim R < s`, the fiber is not
  polynomial. The bound `dim F(I) ≤ dim R` is a hypothesis; Mathlib has no Hilbert-Samuel theory.
-/

@[expose] public section

open IsLocalRing Polynomial

namespace FiberCone

variable {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)

/-- The fiber cone `F(I) = R[It] / m R[It]`, with graded pieces `I ^ n / m I ^ n`. -/
abbrev fiberCone : Type _ :=
  reesAlgebra I ⧸ (maximalIdeal R).map (algebraMap R (reesAlgebra I))

/-- The structure map of `R` into `F(I)` kills `m`, so `F(I)` is an algebra over `k = R ⧸ m`. -/
noncomputable instance : Algebra (R ⧸ maximalIdeal R) (fiberCone I) :=
  let g : R ⧸ maximalIdeal R →+* fiberCone I :=
    Ideal.Quotient.lift (maximalIdeal R) (algebraMap R (fiberCone I)) (fun a ha => by
      change Ideal.Quotient.mk _ (algebraMap R (reesAlgebra I) a) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha))
  @RingHom.toAlgebra _ _ _ (Ideal.Quotient.commSemiring _) g

theorem algebraMap_mk (r : R) :
    algebraMap (R ⧸ maximalIdeal R) (fiberCone I) (Ideal.Quotient.mk _ r) =
      algebraMap R (fiberCone I) r :=
  rfl

variable {I} {s : ℕ} (f : Fin s → R) (hf : ∀ i, f i ∈ I)

/-- The degree-one element `fᵢ t` of the Rees algebra. -/
noncomputable def gen (i : Fin s) : reesAlgebra I :=
  ⟨monomial 1 (f i), reesAlgebra.monomial_mem.mpr (by rw [pow_one]; exact hf i)⟩

/-- The `R`-algebra map `R[y] → R[It]` sending `yᵢ` to `fᵢ t`. -/
noncomputable def reesMap : MvPolynomial (Fin s) R →ₐ[R] reesAlgebra I :=
  MvPolynomial.aeval (gen f hf)

/-- The `k`-algebra map `k[y₁, …, yₛ] → F(I)` sending `yᵢ` to the class of `fᵢ t`. -/
noncomputable def fiberMap : MvPolynomial (Fin s) (R ⧸ maximalIdeal R) →ₐ[R ⧸ maximalIdeal R]
    fiberCone I :=
  MvPolynomial.aeval fun i => Ideal.Quotient.mk _ (gen f hf i)

/-- The fiber cone is the polynomial ring `k[y]`: `fiberMap` is injective. -/
def IsPolynomialFiber : Prop :=
  Function.Injective (fiberMap f hf)

omit [IsLocalRing R] in
theorem reesMap_surjective (hI : Ideal.span (Set.range f) = I) :
    Function.Surjective (reesMap f hf) := by
  intro x
  have hrange : (MvPolynomial.aeval (R := R) (fun i : Fin s => (monomial 1 (f i) : R[X]))).range =
      reesAlgebra I := by
    rw [MvPolynomial.aeval_range, ← adjoin_monomial_eq_reesAlgebra, ← hI]
    unfold Ideal.span
    rw [Submodule.map_span, Algebra.adjoin_span, ← Set.range_comp]
    rfl
  have hx : x.1 ∈
      (MvPolynomial.aeval (R := R) (fun i : Fin s => (monomial 1 (f i) : R[X]))).range := by
    rw [hrange]; exact x.2
  obtain ⟨p, hp⟩ := hx
  refine ⟨p, Subtype.ext ?_⟩
  have : (reesAlgebra I).val.comp (reesMap f hf) =
      MvPolynomial.aeval (R := R) (fun i : Fin s => (monomial 1 (f i) : R[X])) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [reesMap, gen]
  have h2 := congrArg (fun g => g p) this
  simpa using h2.trans hp

theorem fiberMap_comp_map :
    (fiberMap f hf).toRingHom.comp (MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R))) =
      (Ideal.Quotient.mk _).comp (reesMap f hf).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [fiberMap, reesMap]
  · intro i
    simp [fiberMap, reesMap]

theorem fiberMap_surjective (hI : Ideal.span (Set.range f) = I) :
    Function.Surjective (fiberMap f hf) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨p, rfl⟩ := reesMap_surjective f hf hI x
  refine ⟨MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R)) p, ?_⟩
  exact RingHom.congr_fun (fiberMap_comp_map f hf) p

noncomputable instance : IsNoetherianRing (R ⧸ maximalIdeal R) := by
  let _ := Ideal.Quotient.field (maximalIdeal R)
  infer_instance

theorem ringKrullDim_residue_mvPolynomial :
    ringKrullDim (MvPolynomial (Fin s) (R ⧸ maximalIdeal R)) = s := by
  have h0 : ringKrullDim (R ⧸ maximalIdeal R) = 0 := by
    let _ := Ideal.Quotient.field (maximalIdeal R)
    exact ringKrullDim_eq_zero_of_field _
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, h0]
  simp

theorem fiberMap_bijective_of (hI : Ideal.span (Set.range f) = I) (h : IsPolynomialFiber f hf) :
    Function.Bijective (fiberMap f hf) :=
  ⟨h, fiberMap_surjective f hf hI⟩

/-- A polynomial fiber has dimension `s`: `F(I)` is the polynomial ring in `s` variables over
the field `k`. -/
theorem ringKrullDim_fiberCone_of_isPolynomialFiber (hI : Ideal.span (Set.range f) = I)
    (h : IsPolynomialFiber f hf) : ringKrullDim (fiberCone I) = s := by
  have e := RingEquiv.ofBijective (fiberMap f hf) (fiberMap_bijective_of f hf hI h)
  rw [← ringKrullDim_eq_of_ringEquiv e, ringKrullDim_residue_mvPolynomial]

/-- A nonzero element of the kernel of `fiberMap` is a nonzerodivisor of the domain `k[y]`, so
`F(I)` is a quotient of `k[y] / (x)` and its dimension is below `s`. -/
theorem ringKrullDim_fiberCone_add_one_le_of_not_isPolynomialFiber
    (hI : Ideal.span (Set.range f) = I) (h : ¬ IsPolynomialFiber f hf) :
    ringKrullDim (fiberCone I) + 1 ≤ s := by
  have h' : ¬ ∀ a, fiberMap f hf a = 0 → a = 0 := fun H =>
    h ((injective_iff_map_eq_zero (fiberMap f hf)).mpr H)
  push Not at h'
  obtain ⟨x, hx, hx0⟩ := h'
  have hxnz : x ∈ nonZeroDivisors (MvPolynomial (Fin s) (R ⧸ maximalIdeal R)) :=
    mem_nonZeroDivisors_of_ne_zero hx0
  let q : MvPolynomial (Fin s) (R ⧸ maximalIdeal R) ⧸ Ideal.span {x} →+* fiberCone I :=
    Ideal.Quotient.lift (Ideal.span {x}) (fiberMap f hf).toRingHom (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    simp [hx])
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨p, rfl⟩ := fiberMap_surjective f hf hI y
    exact ⟨Ideal.Quotient.mk _ p, rfl⟩
  have h1 : ringKrullDim (fiberCone I) ≤
      ringKrullDim (MvPolynomial (Fin s) (R ⧸ maximalIdeal R) ⧸ Ideal.span {x}) :=
    ringKrullDim_le_of_surjective q hq
  have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hxnz
  rw [ringKrullDim_residue_mvPolynomial] at h2
  exact (add_le_add_left h1 1).trans h2

/-- The fiber cone of an ideal generated by `s` elements is the polynomial ring `k[y₁, …, yₛ]`
(through `fiberMap`) exactly when its Krull dimension is `s`. No Noetherian hypothesis on `R`. -/
theorem isPolynomialFiber_iff (hI : Ideal.span (Set.range f) = I) :
    IsPolynomialFiber f hf ↔ ringKrullDim (fiberCone I) = s := by
  refine ⟨ringKrullDim_fiberCone_of_isPolynomialFiber f hf hI, fun hd => ?_⟩
  by_contra h
  have := ringKrullDim_fiberCone_add_one_le_of_not_isPolynomialFiber f hf hI h
  rw [hd] at this
  have h4 : ((s + 1 : ℕ) : WithBot ℕ∞) ≤ (s : WithBot ℕ∞) := by exact_mod_cast this
  have h5 : s + 1 ≤ s := by exact_mod_cast h4
  omega

/-- The polynomial fiber reads as a kernel over `R`: the kernel of
`R[y] → R[It] → F(I)` is exactly the extension `m · R[y]` of the maximal ideal. -/
theorem isPolynomialFiber_iff_ker_eq :
    IsPolynomialFiber f hf ↔
      RingHom.ker ((Ideal.Quotient.mk _).comp (reesMap f hf).toRingHom :
        MvPolynomial (Fin s) R →+* fiberCone I) =
        (maximalIdeal R).map (MvPolynomial.C : R →+* MvPolynomial (Fin s) R) := by
  have hker : RingHom.ker (MvPolynomial.map (σ := Fin s) (Ideal.Quotient.mk (maximalIdeal R))) =
      (maximalIdeal R).map (MvPolynomial.C : R →+* MvPolynomial (Fin s) R) := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
  rw [← fiberMap_comp_map f hf, ← hker]
  constructor
  · intro h
    ext z
    simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    constructor
    · intro hz
      exact (injective_iff_map_eq_zero (fiberMap f hf)).mp h _ hz
    · intro hz
      rw [hz, map_zero]
  · intro h
    refine (injective_iff_map_eq_zero (fiberMap f hf)).mpr fun z hz => ?_
    obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective z
    have : p ∈ RingHom.ker ((fiberMap f hf).toRingHom.comp
        (MvPolynomial.map (Ideal.Quotient.mk (maximalIdeal R)))) := by
      simpa [RingHom.mem_ker] using hz
    rw [h] at this
    exact RingHom.mem_ker.mp this

/-- If `dim F(I) ≤ dim R < s`, the fiber cone is not the polynomial ring in `s` variables. -/
theorem not_isPolynomialFiber_of_dim_lt (hI : Ideal.span (Set.range f) = I)
    (hell : ringKrullDim (fiberCone I) ≤ ringKrullDim R) (hs : ringKrullDim R < s) :
    ¬ IsPolynomialFiber f hf := fun h => by
  have := ringKrullDim_fiberCone_of_isPolynomialFiber f hf hI h
  rw [this] at hell
  exact absurd (hell.trans_lt hs) (lt_irrefl _)

end FiberCone
