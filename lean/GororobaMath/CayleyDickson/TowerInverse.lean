/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AnnihilatorSymmetry

/-!
# The two-sided inverse of a nonzero element over an ordered field

Convention: the product of `Tower K k` is the Cayley-Dickson product of
`GororobaMath.CayleyDickson.Tower`, over a field `K` with the identity as star, and `Tower.dot k`
is the trace form of `GororobaMath.CayleyDickson.AnnihilatorSymmetry`, so `dot k x x` is the
sum of the squares of the coordinates of `x`.

The norm law `Tower.mul_star_eq_dot` gives `x * star x = star x * x = dot x x • 1`, and over an
ordered field `dot x x` is nonzero for nonzero `x`, so `(dot x x)⁻¹ • star x` is a two-sided
inverse at every level. No associativity enters.

## Main results

* `Tower.mul_inv_dot_smul_star`, `Tower.inv_dot_smul_star_mul`: the two products with `1`.
* `Tower.exists_two_sided_inv`: every nonzero element has the two-sided inverse
  `(dot x x)⁻¹ • star x`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

section Field

variable {K : Type u} [Field K] [StarRing K] [TrivialStar K] [PartialOrder K] [IsOrderedAddMonoid K]

/-- `x * ((dot x x)⁻¹ • star x) = 1` for nonzero `x`, at every level. -/
theorem mul_inv_dot_smul_star (hsq : ∀ x : K, 0 ≤ x * x) {k : ℕ} {x : Tower K k} (hx : x ≠ 0) :
    x * ((dot k x x)⁻¹ • star x) = 1 := by
  rw [mul_smul_comm', (mul_star_eq_dot k x).1, smul_smul, inv_mul_cancel₀ (dot_self_ne_zero hsq hx),
    one_smul]

/-- `((dot x x)⁻¹ • star x) * x = 1` for nonzero `x`, at every level. -/
theorem inv_dot_smul_star_mul (hsq : ∀ x : K, 0 ≤ x * x) {k : ℕ} {x : Tower K k} (hx : x ≠ 0) :
    ((dot k x x)⁻¹ • star x) * x = 1 := by
  rw [smul_mul_assoc', (mul_star_eq_dot k x).2, smul_smul, inv_mul_cancel₀ (dot_self_ne_zero hsq hx),
    one_smul]

/-- Every nonzero element of the tower over an ordered field has the two-sided inverse
`(dot x x)⁻¹ • star x`, at every level. -/
theorem exists_two_sided_inv (hsq : ∀ x : K, 0 ≤ x * x) {k : ℕ} {x : Tower K k} (hx : x ≠ 0) :
    ∃ y : Tower K k, x * y = 1 ∧ y * x = 1 ∧ y = (dot k x x)⁻¹ • star x :=
  ⟨_, mul_inv_dot_smul_star hsq hx, inv_dot_smul_star_mul hsq hx, rfl⟩

example {k : ℕ} {x : Tower ℝ k} (hx : x ≠ 0) :
    x * ((dot k x x)⁻¹ • star x) = 1 ∧ ((dot k x x)⁻¹ • star x) * x = 1 :=
  ⟨mul_inv_dot_smul_star (fun y => mul_self_nonneg y) hx,
    inv_dot_smul_star_mul (fun y => mul_self_nonneg y) hx⟩

end Field

end Tower

end CayleyDickson
