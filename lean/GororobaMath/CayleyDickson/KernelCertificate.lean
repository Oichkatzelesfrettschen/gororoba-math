/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TowerModule

/-!
# A free basis of the kernel of left multiplication from a certificate

Convention: `Tower R k` is the `k`-fold Cayley-Dickson double of a commutative ring `R` whose
star is the identity, `Tower.mulLeft R k y` is the `R`-linear map `z ↦ y * z` of
`GororobaMath.CayleyDickson.TowerModule`, and `Fin n → Tower R k` lists the candidate kernel
vectors. A certificate is a family of vectors `v j` annihilated by `y`, functionals `g j` that
read them off up to the unit `d` (`g j (v l) = d` for `j = l` and `0` otherwise), and a linear map
`back` with the splitting identity `d • z = back (y * z) + ∑ j, g j z • v j`.

## Main results

* `Tower.ker_mulLeft_basis_of_certificate`: the kernel of `mulLeft R k y` is free on the `v j`.
  The Rocq original is `kernel_free_basis` of the module `KernelCertificate` in
  `rocq/quantum/CdTowerKernelCertificate.v`; the finite checks over the source ring and their
  transport (`Tower.baseChange_mul`) stay Rocq evidence, and Lean states the splitting lemma over
  the target ring.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

/-- The kernel of left multiplication by `y` is free on the vectors of a certificate. The Rocq
original is `kernel_free_basis` of `rocq/quantum/CdTowerKernelCertificate.v`. -/
theorem ker_mulLeft_basis_of_certificate {k n : ℕ} (y : Tower R k) (v : Fin n → Tower R k)
    (g : Fin n → Tower R k →ₗ[R] R) (back : Tower R k →ₗ[R] Tower R k) (d : Rˣ)
    (hv : ∀ j, y * v j = 0) (hg : ∀ j l, g j (v l) = if j = l then (d : R) else 0)
    (hs : ∀ z, (d : R) • z = back (y * z) + ∑ j, g j z • v j) :
    ∃ b : Module.Basis (Fin n) R (LinearMap.ker (mulLeft R k y)),
      ∀ j, (b j : Tower R k) = v j := by
  let w : Fin n → LinearMap.ker (mulLeft R k y) := fun j =>
    ⟨v j, LinearMap.mem_ker.2 (by simpa [mulLeft_apply] using hv j)⟩
  have hli : LinearIndependent R w := by
    rw [Fintype.linearIndependent_iff]
    intro c hc l
    have h1 : ∑ j, c j • v j = 0 := by
      have := congrArg Subtype.val hc
      simpa [w] using this
    have h2 := congrArg (g l) h1
    simp only [map_sum, map_smul, hg, smul_eq_mul, mul_ite, mul_zero, map_zero] at h2
    rw [Finset.sum_eq_single l] at h2
    · simp only [↓reduceIte] at h2
      have := congrArg (fun r => r * ((d⁻¹ : Rˣ) : R)) h2
      simpa [mul_assoc] using this
    · intro j _ hj
      simp [Ne.symm hj]
    · simp
  have hsp : ⊤ ≤ Submodule.span R (Set.range w) := by
    intro z _
    have hy : y * (z : Tower R k) = 0 := LinearMap.mem_ker.1 z.2
    have hz : (z : Tower R k) = ∑ j, (((d⁻¹ : Rˣ) : R) * g j z) • v j := by
      have h := hs z
      rw [hy, map_zero, zero_add] at h
      calc (z : Tower R k) = ((d⁻¹ : Rˣ) : R) • ((d : R) • (z : Tower R k)) := by
            rw [smul_smul, Units.inv_mul, one_smul]
        _ = _ := by
            rw [h, Finset.smul_sum]
            simp only [smul_smul]
    have : z = ∑ j, (((d⁻¹ : Rˣ) : R) * g j z) • w j :=
      Subtype.ext (by simpa [w] using hz)
    rw [this]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun j => by simp [Module.Basis.mk_apply, w]⟩

end Tower

end CayleyDickson
