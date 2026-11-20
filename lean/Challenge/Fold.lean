/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AnnihilatorSymmetry

/-!
# Challenge: the fold of a level onto its two halves

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

variable {K : Type u} [Field K] [StarRing K] [TrivialStar K]

/-- The average and detail transform `(a, b) ↦ ((a + b) / 2, (a - b) / 2)`. -/
def fold {k : ℕ} : Tower K (k + 1) → Tower K (k + 1)
  | ⟨a, b⟩ => mk ((2 : K)⁻¹ • (a + b)) ((2 : K)⁻¹ • (a - b))

omit [TrivialStar K] in
/-- The average and detail transform halves the squared norm, `dot v v`, when `2 ≠ 0`. The Rocq
original is `tower_fold_norm_scaling` of `rocq/open/theories/CDTowerFoldTransport.v`. -/
theorem dot_fold_self (h2 : (2 : K) ≠ 0) {k : ℕ} (v : Tower K (k + 1)) :
    dot (k + 1) (fold v) (fold v) = 2⁻¹ * dot (k + 1) v v := by
  sorry

end Tower

end CayleyDickson
