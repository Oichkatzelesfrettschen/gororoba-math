/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TowerModule

/-!
# Challenge: the kernel of left multiplication as a free module on certified vectors

This file restates, with `sorry` as each proof, the headline theorems that the solution
module proves and that the "Lean library" table of `README.md` names, with the
definitions those statements use. It imports the library modules that the solution
module imports. `lake comparator --config` with the JSON file beside this one checks
that each named theorem of the solution module has the statement written here and
depends only on `propext`, `Classical.choice` and `Quot.sound`. No library module
imports this file, and the admission gate does not build it.
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
  sorry

end Tower

end CayleyDickson
