/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Dimensions of quaternion modules

Convention: `ℍ[ℝ]` is Mathlib's algebra of Hamilton quaternions over the reals, a division ring
and a four-dimensional real algebra (`Quaternion.finrank_eq_four`). A module `V` over `ℍ[ℝ]` is
also a real vector space through the scalar action, and `IsScalarTower ℝ ℍ[ℝ] V` says that the two
actions agree on real scalars. A right module over `ℍ[ℝ]` is a left module over the opposite ring,
which `star` identifies with `ℍ[ℝ]`, so the left reading carries the same dimension.

The tower law `finrank ℝ V = finrank ℝ ℍ[ℝ] * finrank ℍ[ℝ] V` makes the real dimension of such a
module a multiple of `4`.

## Main results

* `Module.four_dvd_finrank_of_quaternion`: the Rocq originals are `h_module_dim_div4` of
  `HModDimThm` in `rocq/open/theories/HModuleDim.v`, `h_module_dim_iff_div4` of
  `rocq/open/theories/FinDimHModule.v` (an inductive predicate on `ℕ`, whose reading here is the
  module statement), `moreno16_vlambda_dim_div4` of `MorenoVlambdaDim` in
  `rocq/open/theories/C1542_MorVlambdaOrbit.v` and `Moreno1997_theorem_1_16_abstract_div4` of
  `rocq/open/theories/Moreno1997.v`, the last two with the module structure as a hypothesis.
-/

@[expose] public section

open Quaternion

namespace Module

/-- A finite-dimensional module over the real quaternions has real dimension divisible by `4`. The
Rocq originals are `h_module_dim_div4` of `HModDimThm` in `rocq/open/theories/HModuleDim.v`,
`h_module_dim_iff_div4` of `rocq/open/theories/FinDimHModule.v`, `moreno16_vlambda_dim_div4` of
`MorenoVlambdaDim` in `rocq/open/theories/C1542_MorVlambdaOrbit.v` and
`Moreno1997_theorem_1_16_abstract_div4` of `rocq/open/theories/Moreno1997.v`. -/
theorem four_dvd_finrank_of_quaternion (V : Type*) [AddCommGroup V] [Module ℍ[ℝ] V] [Module ℝ V]
    [IsScalarTower ℝ ℍ[ℝ] V] [Module.Finite ℝ V] : 4 ∣ Module.finrank ℝ V := by
  have h := Module.finrank_mul_finrank ℝ ℍ[ℝ] V
  rw [Quaternion.finrank_eq_four] at h
  exact ⟨_, h.symm⟩

end Module
