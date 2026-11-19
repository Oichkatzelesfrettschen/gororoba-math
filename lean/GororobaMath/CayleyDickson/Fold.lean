/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AnnihilatorSymmetry

/-!
# The average and detail transform

Convention: `Tower K k` is the tower of `GororobaMath.CayleyDickson.Tower` over a field `K` whose
star is the identity, and `Tower.dot k` is its trace form, the sum of the products of
corresponding coordinates (`GororobaMath.CayleyDickson.AnnihilatorSymmetry`). The transform
`Tower.fold` of level `k + 1` sends `(a, b)` to `((a + b) / 2, (a - b) / 2)`, the average and
the detail of the two halves.

## Main results

* `Tower.dot_fold_self`: the transform halves the squared norm `dot v v` when `2 ≠ 0`. The
  Rocq original is `tower_fold_norm_scaling` of `rocq/open/theories/CDTowerFoldTransport.v`,
  over the reals.
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
  obtain ⟨a, b⟩ := v
  change dot (k + 1) (mk _ _) (mk _ _) = 2⁻¹ * dot (k + 1) (mk a b) (mk a b)
  simp only [dot_mk, dot_smul_left, dot_smul_right, dot_add_left, dot_add_right, dot_sub_left,
    dot_sub_right]
  rw [dot_comm k b a]
  field_simp
  ring

end Tower

end CayleyDickson
