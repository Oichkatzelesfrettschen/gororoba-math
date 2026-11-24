/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.HalfFold

/-!
# Nullity strata of the Cayley-Dickson tower

Convention: `Tower K k` is the tower of `GororobaMath.CayleyDickson.Tower` over a field `K` whose
star is the identity, with the product `(a, b) (c, d) = (a c - star d b, d a + b star c)`, and
`Tower.mulLeft K k a` is left multiplication by `a` as a `K`-linear map. The nullity of `a` is
the dimension of the kernel of that map, so it counts the independent right annihilators of `a`.
The stratum of nullity `n` at level `k` is the set of elements of nullity `n`; the strata of the
`A_5` program (level 5) are sets of this form, cut out further by their closure ideals.

## Main results

* `Tower.nullity_mk_zero`: over an ordered field, `nullity (a, 0) = 2 * nullity a` at every
  level.
* `Tower.nullity_mk_zero_of_star_eq_neg`: the same doubling for a pure `a` over any field.
* `Tower.mk_zero_mem_stratum`: `a` of nullity `n` at level `k` gives `(a, 0)` in the stratum of
  nullity `2 n` at level `k + 1`.
* `Tower.mk_zero_mem_stratum_eight`: a sedenion of nullity 4 embeds at level 5 with nullity 8.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

open Module

variable (K : Type u) [Field K] [StarRing K] [TrivialStar K]

/-- The nullity of `a`: the dimension of the kernel of left multiplication by `a` at level `k`. -/
noncomputable def nullity (k : ℕ) (a : Tower K k) : ℕ :=
  finrank K (LinearMap.ker (mulLeft K k a))

/-- The stratum of nullity `n` at level `k`: the elements whose left multiplication has a kernel
of dimension `n`. -/
def Stratum (k n : ℕ) : Set (Tower K k) :=
  {a | nullity K k a = n}

variable {K}

theorem mem_stratum_iff {k n : ℕ} {a : Tower K k} : a ∈ Stratum K k n ↔ nullity K k a = n :=
  Iff.rfl

/-- For a pure `a` the nullity of `(a, 0)` is twice the nullity of `a`, over any field. -/
theorem nullity_mk_zero_of_star_eq_neg {k : ℕ} {a : Tower K k} (ha : star a = -a) :
    nullity K (k + 1) (mk a 0) = 2 * nullity K k a :=
  finrank_ker_mulLeft_mk_left_of_star_eq_neg ha

variable [PartialOrder K] [IsOrderedAddMonoid K]

/-- Over an ordered field the nullity of `(a, 0)` is twice the nullity of `a`, at every level. -/
theorem nullity_mk_zero (hsq : ∀ x : K, 0 ≤ x * x) {k : ℕ} (a : Tower K k) :
    nullity K (k + 1) (mk a 0) = 2 * nullity K k a :=
  finrank_ker_mulLeft_mk_left hsq a

/-- If `a` has nullity `n`, then `(a, 0)` lies in the stratum of nullity `2 n` one level up. -/
theorem mk_zero_mem_stratum (hsq : ∀ x : K, 0 ≤ x * x) {k n : ℕ} {a : Tower K k}
    (ha : a ∈ Stratum K k n) : (mk a 0 : Tower K (k + 1)) ∈ Stratum K (k + 1) (2 * n) := by
  rw [mem_stratum_iff] at ha ⊢
  rw [nullity_mk_zero hsq, ha]

/-- A sedenion of nullity 4 embeds at level 5 as `(a, 0)` with nullity 8. -/
theorem mk_zero_mem_stratum_eight (hsq : ∀ x : K, 0 ≤ x * x) {a : Tower K 4}
    (ha : a ∈ Stratum K 4 4) : (mk a 0 : Tower K 5) ∈ Stratum K 5 8 :=
  mk_zero_mem_stratum hsq ha

end Tower

end CayleyDickson
