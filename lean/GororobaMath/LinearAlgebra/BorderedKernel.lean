/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The kernel of a bordered skew matrix

Convention: for a square matrix `M` on an index type `n` and a vector `p : n → K`, the bordered
matrix `Matrix.bordered M p` is the block matrix `[[0, -pᵀ], [p, M]]` on `Unit ⊕ n`, built with
`Matrix.fromBlocks`: row `inl ()` is `(0, -p)` and column `inl ()` is `(0, p)`. A vector of
`Unit ⊕ n → K` is written `Sum.elim (fun _ => a) u` with `a : K` its `inl` coordinate and
`u : n → K` the rest. The product is `Matrix.mulVec`, `p ⬝ᵥ u` is the bilinear pairing with no
conjugation, and `Matrix.pperp p` is the kernel of `u ↦ p ⬝ᵥ u`. The hypothesis `Mᵀ = -M` is
skew-symmetry, and `z` is a kernel vector of `M` with `p ⬝ᵥ z ≠ 0`.

## Main results

* `Matrix.bordered_mulVec_eq_zero_iff`: `(a, u)` lies in the kernel of the bordered matrix exactly
  when `a = 0`, `M u = 0` and `p ⬝ᵥ u = 0`.
* `Matrix.ker_toLin'_eq_span_sup_inf`: `ker M = K z ⊔ (ker M ⊓ pperp p)`, and the two parts are
  disjoint (`Matrix.disjoint_span_ker_inf_pperp`).
* `Matrix.finrank_ker_bordered_add_one`: `finrank (ker bordered) + 1 = finrank (ker M)`.
-/

@[expose] public section

namespace Matrix

variable {K : Type*} [Field K] {n : Type*} [Fintype n]

/-- The bordered matrix `[[0, -pᵀ], [p, M]]` on `Unit ⊕ n`. -/
def bordered (M : Matrix n n K) (p : n → K) : Matrix (Unit ⊕ n) (Unit ⊕ n) K :=
  Matrix.fromBlocks 0 (Matrix.of fun _ j => -p j) (Matrix.of fun i _ => p i) M

/-- The kernel of the pairing with `p`. -/
def pperp (p : n → K) : Submodule K (n → K) where
  carrier := {u | p ⬝ᵥ u = 0}
  add_mem' := by
    intro u v hu hv
    change p ⬝ᵥ (u + v) = 0
    rw [dotProduct_add, show p ⬝ᵥ u = 0 from hu, show p ⬝ᵥ v = 0 from hv, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c u hu
    change p ⬝ᵥ (c • u) = 0
    rw [dotProduct_smul, show p ⬝ᵥ u = 0 from hu, smul_eq_mul, mul_zero]

theorem mem_pperp {p u : n → K} : u ∈ pperp p ↔ p ⬝ᵥ u = 0 := Iff.rfl

/-- The bordered matrix applied to `(a, u)` is `(-(p ⬝ᵥ u), a • p + M u)`. -/
theorem bordered_mulVec (M : Matrix n n K) (p : n → K) (a : K) (u : n → K) :
    bordered M p *ᵥ Sum.elim (fun _ => a) u =
      Sum.elim (fun _ => -(p ⬝ᵥ u)) (a • p + M *ᵥ u) := by
  rw [bordered, fromBlocks_mulVec]
  ext (i | i)
  · simp [mulVec, dotProduct]
  · simp [mulVec, dotProduct, mul_comm]

/-- Skew-symmetry and a kernel vector `z` with `p ⬝ᵥ z ≠ 0` force the border coordinate of a
kernel vector to vanish: pairing the second block row with `z` gives `a (p ⬝ᵥ z) = 0`. -/
theorem bordered_mulVec_eq_zero_iff {M : Matrix n n K} (hM : Mᵀ = -M) {z p : n → K}
    (hz : M *ᵥ z = 0) (hpz : p ⬝ᵥ z ≠ 0) (a : K) (u : n → K) :
    bordered M p *ᵥ Sum.elim (fun _ => a) u = 0 ↔ a = 0 ∧ M *ᵥ u = 0 ∧ p ⬝ᵥ u = 0 := by
  rw [bordered_mulVec]
  constructor
  · intro h
    have h1 : -(p ⬝ᵥ u) = 0 := congrFun h (Sum.inl ())
    have h2 : a • p + M *ᵥ u = 0 := funext fun i => congrFun h (Sum.inr i)
    have hpu : p ⬝ᵥ u = 0 := neg_eq_zero.mp h1
    have hzM : z ⬝ᵥ (M *ᵥ u) = 0 := by
      rw [dotProduct_mulVec]
      have : z ᵥ* M = 0 := by
        have h3 : z ᵥ* Mᵀ = M *ᵥ z := vecMul_transpose M z
        rw [hM, vecMul_neg, hz] at h3
        exact neg_eq_zero.mp h3
      rw [this, zero_dotProduct]
    have h4 : z ⬝ᵥ (a • p + M *ᵥ u) = 0 := by rw [h2]; simp
    rw [dotProduct_add, hzM, add_zero, dotProduct_smul, smul_eq_mul, dotProduct_comm] at h4
    have ha : a = 0 := by
      rcases mul_eq_zero.mp h4 with h | h
      · exact h
      · exact absurd h hpz
    refine ⟨ha, ?_, hpu⟩
    rw [ha, zero_smul, zero_add] at h2
    exact h2
  · rintro ⟨rfl, h1, h2⟩
    rw [h2, h1]
    ext (i | i) <;> simp

variable [DecidableEq n] (M : Matrix n n K) (p z : n → K)

/-- The projection `u ↦ u - (p ⬝ᵥ u / p ⬝ᵥ z) z` splits `ker M` into the line of `z` and the
part in `pperp p`. -/
theorem ker_toLin'_eq_span_sup_inf (hz : M *ᵥ z = 0) (hpz : p ⬝ᵥ z ≠ 0) :
    LinearMap.ker (Matrix.toLin' M) =
      Submodule.span K {z} ⊔ (LinearMap.ker (Matrix.toLin' M) ⊓ pperp p) := by
  apply le_antisymm
  · intro u hu
    have hu' : M *ᵥ u = 0 := hu
    have hmem : u - ((p ⬝ᵥ u) / (p ⬝ᵥ z)) • z ∈ LinearMap.ker (Matrix.toLin' M) ⊓ pperp p := by
      refine ⟨?_, ?_⟩
      · change M *ᵥ (u - ((p ⬝ᵥ u) / (p ⬝ᵥ z)) • z) = 0
        rw [mulVec_sub, mulVec_smul, hz, hu']
        simp
      · rw [SetLike.mem_coe, mem_pperp, dotProduct_sub, dotProduct_smul, smul_eq_mul,
          div_mul_cancel₀ _ hpz]
        simp
    have : u = ((p ⬝ᵥ u) / (p ⬝ᵥ z)) • z + (u - ((p ⬝ᵥ u) / (p ⬝ᵥ z)) • z) := by abel
    rw [this]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self z)) hmem
  · refine sup_le ?_ inf_le_left
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hz

/-- A multiple of `z` in `pperp p` is zero, since `p ⬝ᵥ z ≠ 0`. -/
theorem disjoint_span_ker_inf_pperp (hpz : p ⬝ᵥ z ≠ 0) :
    Disjoint (Submodule.span K {z}) (LinearMap.ker (Matrix.toLin' M) ⊓ pperp p) := by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
  have h : p ⬝ᵥ (c • z) = 0 := hx'.2
  rw [dotProduct_smul, smul_eq_mul] at h
  have hc : c = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h hpz
  rw [hc, zero_smul]

/-- Dropping the zero border coordinate is a linear equivalence from the kernel of the bordered
matrix onto `ker M ⊓ pperp p`. -/
noncomputable def borderedKerEquiv (hM : Mᵀ = -M) (hz : M *ᵥ z = 0) (hpz : p ⬝ᵥ z ≠ 0) :
    LinearMap.ker (Matrix.toLin' (bordered M p)) ≃ₗ[K]
      (LinearMap.ker (Matrix.toLin' M) ⊓ pperp p : Submodule K (n → K)) where
  toFun v :=
    ⟨fun i => (v : Unit ⊕ n → K) (Sum.inr i), by
      have hv : bordered M p *ᵥ (v : Unit ⊕ n → K) = 0 := v.2
      have hs : (v : Unit ⊕ n → K) =
          Sum.elim (fun _ => (v : Unit ⊕ n → K) (Sum.inl ()))
            (fun i => (v : Unit ⊕ n → K) (Sum.inr i)) := by
        ext (i | i)
        · rfl
        · rfl
      rw [hs] at hv
      obtain ⟨-, h1, h2⟩ := (bordered_mulVec_eq_zero_iff hM hz hpz _ _).mp hv
      exact ⟨h1, h2⟩⟩
  map_add' v w := rfl
  map_smul' c v := rfl
  invFun u :=
    ⟨Sum.elim (fun _ => 0) (u : n → K), by
      have h := (bordered_mulVec_eq_zero_iff hM hz hpz 0 (u : n → K)).mpr ⟨rfl, u.2.1, u.2.2⟩
      exact h⟩
  left_inv v := by
    apply Subtype.ext
    have hv : bordered M p *ᵥ (v : Unit ⊕ n → K) = 0 := v.2
    have hs : (v : Unit ⊕ n → K) =
        Sum.elim (fun _ => (v : Unit ⊕ n → K) (Sum.inl ()))
          (fun i => (v : Unit ⊕ n → K) (Sum.inr i)) := by
      ext (i | i)
      · rfl
      · rfl
    rw [hs] at hv
    obtain ⟨h0, -, -⟩ := (bordered_mulVec_eq_zero_iff hM hz hpz _ _).mp hv
    ext (i | i)
    · exact h0.symm
    · rfl
  right_inv u := rfl

/-- The kernel of the bordered matrix is one dimension smaller than `ker M`. -/
theorem finrank_ker_bordered_add_one (hM : Mᵀ = -M) (hz : M *ᵥ z = 0) (hpz : p ⬝ᵥ z ≠ 0) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' (bordered M p))) + 1 =
      Module.finrank K (LinearMap.ker (Matrix.toLin' M)) := by
  have hz0 : z ≠ 0 := fun h => hpz (by rw [h]; simp)
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span K {z})
    (LinearMap.ker (Matrix.toLin' M) ⊓ pperp p)
  rw [← ker_toLin'_eq_span_sup_inf M p z hz hpz,
    (disjoint_span_ker_inf_pperp M p z hpz).eq_bot, finrank_bot, finrank_span_singleton hz0,
    add_zero] at h1
  rw [(borderedKerEquiv M p z hM hz hpz).finrank_eq, h1, add_comm]

end Matrix
