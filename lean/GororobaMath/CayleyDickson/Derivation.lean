/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Map
public import GororobaMath.CayleyDickson.TowerModule

/-!
# Derivations extend to the Cayley-Dickson double

Convention: `CayleyDickson A` is the double of `GororobaMath.CayleyDickson.Basic`, pairs
`(re, im)` with `(a, b) * (c, d) = (a * c - star d * b, d * a + b * star c)` and
`star (a, b) = (star a, -b)`. `CayleyDickson.mapAdd D` applies an additive map `D` of `A` to both
halves, `(a, b) ↦ (D a, D b)`.

A derivation `D` of `A` (an additive map with `D (x * y) = D x * y + x * D y`) that commutes
with the star extends to a derivation of the double. The hypotheses are those of Schafer 1954,
Theorem 2, stated over every nonassociative star ring `A`; over an `R`-module `A` with `D`
linear, `CayleyDickson.map_smul` gives the `R`-linear form.

## Main results

* `Tower.leibniz_four_iff_of_restricts`: the Rocq
  `schafer1954_theorem4_octonion_sedenion_identification` of `rocq/open/theories/Schafer1954.v`,
  with its premise `Hbackward` as a hypothesis.
* `Tower.finrank_leibniz_of_certificate`: independent derivations and a spanning relation give the
  dimension of the derivations (`rocq/quantum/CdTowerG2DerivationSpan.v`).
* `CayleyDickson.mapAdd_leibniz`: `mapAdd D (x * y) = mapAdd D x * y + x * mapAdd D y`, the Rocq
  `schafer1954_theorem2_extension_map` of `rocq/open/theories/Schafer1954.v`.
-/

@[expose] public section

namespace CayleyDickson

variable {A : Type*} [NonAssocRing A] [StarRing A]

/-- The additive map `(a, b) ↦ (D a, D b)` of the double of `A` induced by an additive map `D`. -/
def mapAdd (D : A →+ A) : CayleyDickson A →+ CayleyDickson A where
  toFun := map D
  map_zero' := by ext <;> simp
  map_add' := CayleyDickson.map_add D

@[simp] theorem mapAdd_re (D : A →+ A) (x : CayleyDickson A) : (mapAdd D x).re = D x.re := rfl

@[simp] theorem mapAdd_im (D : A →+ A) (x : CayleyDickson A) : (mapAdd D x).im = D x.im := rfl

/-- A derivation of `A` that commutes with the star extends componentwise to a derivation of the
double. The Rocq original is `schafer1954_theorem2_extension_map` of
`rocq/open/theories/Schafer1954.v`. -/
theorem mapAdd_leibniz (D : A →+ A) (hD : ∀ x y, D (x * y) = D x * y + x * D y)
    (hs : ∀ x, D (star x) = star (D x)) (x y : CayleyDickson A) :
    mapAdd D (x * y) = mapAdd D x * y + x * mapAdd D y := by
  ext
  · simp only [mapAdd_re, mul_re, add_re, map_sub, hD, hs]
    simp only [mapAdd_im]
    abel
  · simp only [mapAdd_im, mul_im, add_im, map_add, hD, hs]
    simp only [mapAdd_re]
    abel


namespace Tower

universe u

variable {K : Type u} [Field K] [StarRing K] [TrivialStar K]

/-- The `K`-linear maps of `Tower K k` that satisfy the Leibniz rule. The closure proofs use `rw`
alone: with `simp only` and `abel` the comparator rejected the challenge restatement at
`leibnizSubmodule._proof_2`, and with `rw` it accepts it (Lean 4.35.0). hypothesis: those
tactics leave terms that depend on the elaborating module. -/
def leibnizSubmodule (K : Type u) [Field K] [StarRing K] [TrivialStar K] (k : ℕ) :
    Submodule K (Tower K k →ₗ[K] Tower K k) where
  carrier := {F | ∀ x y, F (x * y) = F x * y + x * F y}
  add_mem' := fun {F G} hF hG x y => by
    rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.add_apply, hF x y, hG x y, add_mul,
      mul_add]
    exact add_add_add_comm _ _ _ _
  zero_mem' := fun x y => by
    rw [LinearMap.zero_apply, LinearMap.zero_apply, LinearMap.zero_apply, zero_mul, mul_zero,
      add_zero]
  smul_mem' := fun c F hF x y => by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, hF x y, smul_add,
      smul_mul_assoc', mul_smul_comm']

theorem mem_leibnizSubmodule {k : ℕ} {F : Tower K k →ₗ[K] Tower K k} :
    F ∈ leibnizSubmodule K k ↔ ∀ x y, F (x * y) = F x * y + x * F y := Iff.rfl

/-- Given `n` independent derivations of `Tower K k` and a nonzero scalar `d` with `d • F` in
their span for every derivation `F`, the derivations form a space of dimension `n`. The Rocq
original is `derivations_spanned` of the module `G2DerivationSpan` in
`rocq/quantum/CdTowerG2DerivationSpan.v` together with `derivations_independent` of
`rocq/quantum/CdTowerG2Derivations.v`; the value `14` at level `4` stays with those tables. -/
theorem finrank_leibniz_of_certificate {k n : ℕ} (T : Fin n → Tower K k →ₗ[K] Tower K k)
    (hT : ∀ t x y, T t (x * y) = T t x * y + x * T t y) (hind : LinearIndependent K T) (d : K)
    (hd : d ≠ 0)
    (hspan : ∀ F : Tower K k →ₗ[K] Tower K k, (∀ x y, F (x * y) = F x * y + x * F y) →
      d • F ∈ Submodule.span K (Set.range T)) :
    Module.finrank K (leibnizSubmodule K k) = n := by
  have h : leibnizSubmodule K k = Submodule.span K (Set.range T) := by
    apply le_antisymm
    · intro F hF
      have h1 := Submodule.smul_mem _ d⁻¹ (hspan F hF)
      rwa [smul_smul, inv_mul_cancel₀ hd, one_smul] at h1
    · rw [Submodule.span_le]
      rintro _ ⟨t, rfl⟩
      exact hT t
  rw [h, finrank_span_eq_card hind, Fintype.card_fin]

end Tower

/-- Given that every derivation of the sedenions restricts to a derivation of the octonions that
commutes with the star, the derivations of the sedenions are exactly the componentwise extensions
of octonion derivations. The Rocq original is
`schafer1954_theorem4_octonion_sedenion_identification` of `rocq/open/theories/Schafer1954.v`,
whose premise `Hbackward` is the hypothesis `hback` here;
the unconditional Theorem 4 of Schafer (1954) has no counterpart. -/
theorem leibniz_four_iff_of_restricts {K : Type*} [Field K] [StarRing K] [TrivialStar K]
    (D : Tower K 4 →ₗ[K] Tower K 4)
    (hback : (∀ x y, D (x * y) = D x * y + x * D y) →
      ∃ A : Tower K 3 →ₗ[K] Tower K 3, (∀ x y, A (x * y) = A x * y + x * A y) ∧
        (∀ x, A (star x) = star (A x)) ∧ ∀ a b, D (mk a b) = mk (A a) (A b)) :
    (∀ x y, D (x * y) = D x * y + x * D y) ↔
      ∃ A : Tower K 3 →ₗ[K] Tower K 3, (∀ x y, A (x * y) = A x * y + x * A y) ∧
        (∀ x, A (star x) = star (A x)) ∧ ∀ a b, D (mk a b) = mk (A a) (A b) := by
  refine ⟨hback, ?_⟩
  rintro ⟨A, hA, hAs, hDA⟩ x y
  have hD : ∀ z : Tower K 4, D z = mapAdd A.toAddMonoidHom z := fun z => by
    obtain ⟨a, b⟩ := z
    exact hDA a b
  simp only [hD]
  exact mapAdd_leibniz A.toAddMonoidHom hA hAs x y

end CayleyDickson
