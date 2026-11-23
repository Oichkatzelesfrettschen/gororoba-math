/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.BasisIsometry

/-!
# Two-term operands with a scalar: trivial kernel away from `t ^ 2 = 1`

Convention: the product of `Tower R k` is the Cayley-Dickson product of
`GororobaMath.CayleyDickson.Tower`, over a commutative ring with the identity as star;
`Tower.e R k i` is the basis unit of index `i`, `Tower.dot k` the trace form and
`Tower.mulLeft R k y` left multiplication by `y` as a linear map. The order hypotheses are those
of `GororobaMath.CayleyDickson.AnnihilatorSymmetry`: a partial order compatible with addition,
nonnegative squares (`hsq`) and no zero divisors, which hold over the integers, the rationals and
the reals.

Left multiplication by a basis unit preserves the trace form (`Tower.dot_e_mul_e_mul`). If
`(e i + t • e j) * x = 0` then `e i * x = -(t • (e j * x))`, and taking `dot` of each side with
itself gives `dot x x = t * t * dot x x`, so `(t * t - 1) * dot x x = 0`. With `t * t ≠ 1` the
trace form of `x` with itself vanishes and `x = 0`. No index hypothesis enters: `i` and `j` may
be equal or zero.

## Main results

* `Tower.eq_zero_of_e_add_smul_e_mul_eq_zero`: for `t * t ≠ 1`, left multiplication by
  `e i + t • e j` has no nonzero kernel vector, at every level.
* `Tower.ker_mulLeft_e_add_smul_e`: its kernel is the zero submodule.

With `Tower.finrank_ker_mulLeft_e_add_e` and `Tower.finrank_ker_mulLeft_e_sub_e` of
`GororobaMath.CayleyDickson.TwoTermNullity` (the cases `t = 1` and `t = -1`), this gives the
nullity of `L_(e_i + t e_j)` for every scalar `t` of an ordered field, the statement of row A5-177
of the findings ledger of gororoba-quantum (`docs/evidence/a5-exceptional-fibers/ledger.tsv`)
outside its census counts.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]
variable [PartialOrder R] [IsOrderedAddMonoid R] [NoZeroDivisors R] {k : ℕ}

/-- For `t * t ≠ 1`, a vector that `e i + t • e j` annihilates on the left is zero. -/
theorem eq_zero_of_e_add_smul_e_mul_eq_zero (hsq : ∀ x : R, 0 ≤ x * x) (i j : BitVec k) {t : R}
    (ht : t * t ≠ 1) {x : Tower R k} (h : (e R k i + t • e R k j) * x = 0) : x = 0 := by
  rw [add_mul, smul_mul_assoc'] at h
  have h1 : e R k i * x = -(t • (e R k j * x)) := eq_neg_of_add_eq_zero_left h
  have h2 := dot_e_mul_e_mul i x x
  rw [h1, dot_neg_left, dot_neg_right, neg_neg, dot_smul_left, dot_smul_right,
    dot_e_mul_e_mul] at h2
  have h3 : (t * t - 1) * dot k x x = 0 := by linear_combination h2
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd (sub_eq_zero.mp h4) ht
  · exact eq_zero_of_dot_self_eq_zero hsq h4

/-- For `t * t ≠ 1`, the kernel of left multiplication by `e i + t • e j` is zero. -/
theorem ker_mulLeft_e_add_smul_e (hsq : ∀ x : R, 0 ≤ x * x) (i j : BitVec k) {t : R}
    (ht : t * t ≠ 1) : LinearMap.ker (mulLeft R k (e R k i + t • e R k j)) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  exact eq_zero_of_e_add_smul_e_mul_eq_zero hsq i j ht hx

end Tower

end CayleyDickson
