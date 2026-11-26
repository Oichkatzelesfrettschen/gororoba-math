/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AlternativeIdentities
public import GororobaMath.CayleyDickson.NonAssociative

/-!
# Associativity, alternativity and division at the levels of the real division algebras

Convention: `Tower R k` is the tower of `GororobaMath.CayleyDickson.Tower` over a commutative
ring `R` whose star is the identity, with the product
`(a, b) (c, d) = (a c - star d b, d a + b star c)`.
Levels 0, 1, 2 and 3 are `R`, the complex pairs, the quaternions and the octonions, of dimension
1, 2, 4 and 8. An ordered coefficient ring carries the hypothesis `hsq : ∀ x : R, 0 ≤ x * x`, and
`Tower.dot k x x` is the sum of the squares of the coordinates of `x`
(`GororobaMath.CayleyDickson.AnnihilatorSymmetry`).

The product is associative at levels 0 to 2 and alternative at levels 0 to 3 over every commutative
ring (the existing theorems `Tower.associator_eq_zero_of_le_two`,
`Tower.left_alternative_of_le_three` and `Tower.right_alternative_of_le_three`), and the trace form
multiplies up to level 3 (`Tower.dot_mul_self_of_le_three`), so a product of nonzero elements is
nonzero on those levels over an ordered domain. Two nondegeneracy hypotheses make the levels exact.
Associativity fails at every level from 3 on only when `2 ≠ 0` (the zero ring and the rings with
`2 = 0` are associative at every level, where the tower is a group algebra of `(ℤ/2)^k`). A
zero-divisor pair exists from level 4 on only over a nontrivial ring, `1 ≠ 0`
(`Tower.exists_zero_divisor`); the zero ring has no nonzero element.

## Main results

* `Tower.mul_assoc_of_le_two`: `x * y * z = x * (y * z)` at levels 0 to 2.
* `Tower.exists_mul_assoc_ne_iff`: over a ring with `2 ≠ 0`, some triple fails associativity
  exactly at the levels `k ≥ 3`.
* `Tower.mul_eq_zero_of_le_three`: over a commutative ring with a partial order, ordered addition,
  no zero divisors and nonnegative squares, `x * y = 0` forces `x = 0` or `y = 0` at levels 0
  to 3.
* `Tower.mul_eq_zero_iff_of_le_three`: the same as an equivalence.
* `Tower.mul_comm_of_le_one` and `Tower.exists_mul_comm_ne`: the product is commutative at levels 0
  and 1 and, over a ring with `2 ≠ 0`, not at level 2, so commutativity is the first property lost.
* `Tower.existsUnique_mul_eq_of_le_three`: over an ordered field, for `a ≠ 0` at levels 0 to 3
  each of `a * x = b` and `y * a = b` has exactly one solution, which is the division property of
  the real quaternions and octonions.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] {k : ℕ}

/-- The product is associative at levels 0 to 2, since the associator vanishes there. -/
theorem mul_assoc_of_le_two (hk : k ≤ 2) (x y z : Tower R k) : x * y * z = x * (y * z) :=
  sub_eq_zero.mp (associator_eq_zero_of_le_two hk x y z)

/-- The product is commutative at levels 0 and 1: the base ring and its double. -/
theorem mul_comm_of_le_one (hk : k ≤ 1) (x y : Tower R k) : x * y = y * x := by
  interval_cases k
  · exact mul_comm (show R from x) (show R from y)
  · exact CayleyDickson.mul_comm_of_trivialStar (A := R) x y

omit [TrivialStar R] in
/-- Over a ring with `2 ≠ 0`, the quaternion units `e_1` and `e_2` do not commute: their
commutator is `2 e_3`. -/
theorem exists_mul_comm_ne (h2 : (2 : R) ≠ 0) : ∃ x y : Tower R 2, x * y ≠ y * x := by
  refine ⟨e R 2 1#2, e R 2 2#2, fun h => ?_⟩
  have hc : commutator (e R 2 1#2) (e R 2 2#2) = 0 := by
    unfold commutator
    rw [h, sub_self]
  rw [commutator_e_e] at hc
  have hs : sign 2 1#2 2#2 - sign 2 2#2 1#2 = 2 := by decide
  rw [hs] at hc
  exact zsmul_e_ne_zero (n := 2) (by simpa using h2) 2 _ hc

/-- Over a ring with `2 ≠ 0`, an associativity-violating triple exists exactly from level 3 on. -/
theorem exists_mul_assoc_ne_iff (h2 : (2 : R) ≠ 0) :
    (∃ x y z : Tower R k, x * y * z ≠ x * (y * z)) ↔ 3 ≤ k := by
  refine ⟨fun ⟨x, y, z, h⟩ => ?_, fun hk => exists_mul_assoc_ne h2 k hk⟩
  by_contra hk
  exact h (mul_assoc_of_le_two (by omega) x y z)

section Ordered

variable [PartialOrder R] [IsOrderedAddMonoid R] [NoZeroDivisors R]

/-- A product vanishes only with a factor at levels 0 to 3: the trace form multiplies there and
is nonzero on a nonzero element. -/
theorem mul_eq_zero_of_le_three (hsq : ∀ x : R, 0 ≤ x * x) (hk : k ≤ 3) {x y : Tower R k}
    (h : x * y = 0) : x = 0 ∨ y = 0 := by
  by_contra hne
  rw [not_or] at hne
  have hd := dot_mul_self_of_le_three hk x y
  rw [h, dot_zero_left] at hd
  exact mul_ne_zero (dot_self_ne_zero hsq hne.1) (dot_self_ne_zero hsq hne.2) hd.symm

/-- A product vanishes exactly when a factor does, at levels 0 to 3. -/
theorem mul_eq_zero_iff_of_le_three (hsq : ∀ x : R, 0 ≤ x * x) (hk : k ≤ 3) {x y : Tower R k} :
    x * y = 0 ↔ x = 0 ∨ y = 0 :=
  ⟨mul_eq_zero_of_le_three hsq hk, fun h => h.elim (fun hx => by rw [hx, zero_mul])
    (fun hy => by rw [hy, mul_zero])⟩

end Ordered

section Division

variable {K : Type u} [Field K] [StarRing K] [TrivialStar K] [PartialOrder K] [IsOrderedAddMonoid K]

/-- At levels 0 to 3 over an ordered field, for `a ≠ 0` the equations `a * x = b` and
`y * a = b` each have exactly one solution: the solutions are `(dot a a)⁻¹ • (star a * b)` and
`(dot a a)⁻¹ • (b * star a)`, and the left and right inverse properties give uniqueness. -/
theorem existsUnique_mul_eq_of_le_three (hsq : ∀ x : K, 0 ≤ x * x) (hk : k ≤ 3) {a : Tower K k}
    (ha : a ≠ 0) (b : Tower K k) : (∃! x, a * x = b) ∧ ∃! y, y * a = b := by
  have hd : dot k a a ≠ 0 := dot_self_ne_zero hsq ha
  refine ⟨⟨(dot k a a)⁻¹ • (star a * b), ?_, ?_⟩, ⟨(dot k a a)⁻¹ • (b * star a), ?_, ?_⟩⟩
  · have h := star_mul_mul_of_le_three hk (star a) b
    rw [star_star, dot_star_star] at h
    change a * ((dot k a a)⁻¹ • (star a * b)) = b
    rw [mul_smul_comm', h, smul_smul, inv_mul_cancel₀ hd, one_smul]
  · intro x hx
    have hx' : a * x = b := hx
    have h := normInv_mul_mul_of_le_three hk hd x
    rw [hx'] at h
    rw [← h]
    unfold normInv
    rw [smul_mul_assoc']
  · have h := mul_mul_star_of_le_three hk (star a) b
    rw [star_star, dot_star_star] at h
    change (dot k a a)⁻¹ • (b * star a) * a = b
    rw [smul_mul_assoc', h, smul_smul, inv_mul_cancel₀ hd, one_smul]
  · intro y hy
    have hy' : y * a = b := hy
    have h := mul_mul_normInv_of_le_three hk hd y
    rw [hy'] at h
    rw [← h]
    unfold normInv
    rw [mul_smul_comm']

end Division

end Tower

end CayleyDickson
