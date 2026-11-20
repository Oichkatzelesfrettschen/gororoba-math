/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Challenge: dimensions of quaternion modules

This file restates, with `sorry` as each proof, the headline theorems that the solution
module proves and that the "Lean library" table of `README.md` names, with the
definitions those statements use. It imports the library modules that the solution
module imports. `lake comparator --config` with the JSON file beside this one checks
that each named theorem of the solution module has the statement written here and
depends only on `propext`, `Classical.choice` and `Quot.sound`. No library module
imports this file, and the admission gate does not build it.
-/

@[expose] public section

open Quaternion

namespace Module

/-- A finite-dimensional module over the real quaternions has real dimension divisible by `4`. -/
theorem four_dvd_finrank_of_quaternion (V : Type*) [AddCommGroup V] [Module ℍ[ℝ] V] [Module ℝ V]
    [IsScalarTower ℝ ℍ[ℝ] V] [Module.Finite ℝ V] : 4 ∣ Module.finrank ℝ V := by
  sorry

end Module
