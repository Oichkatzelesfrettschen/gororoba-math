/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Tower

/-!
# Non-associativity at every level of the tower from the octonions on

Convention: the product of `Tower R k` is the Cayley-Dickson product of
`GororobaMath.CayleyDickson.Tower`, `(a, b) (c, d) = (a c - star d b, d a + b star c)`,
and `e R k p` is its basis element of index `p`. `Tower R 3` is the
octonions and `Tower R 7` the 128-dimensional algebra. The map
`x ↦ mk x 0` of level `k` into level `k + 1` preserves products
(`Tower.mk_zero_mul_mk_zero`) and is injective (`Tower.mk_inj`), so it
carries a triple that violates associativity to one of the level above.

## Main results

* `Tower.e_ne_neg_e`: over a ring in which `2 ≠ 0`, no basis element
  equals its negative.
* `Tower.octonion_e1_e2_e4_mul_assoc_ne`: in the octonions over such a
  ring, `(e 1 * e 2) * e 4 = e 7` while `e 1 * (e 2 * e 4) = -e 7`.
* `Tower.exists_mul_assoc_ne`: at every level `k ≥ 3`, over every ring
  with a star in which `2 ≠ 0`, some triple `a, b, c` has
  `(a * b) * c ≠ a * (b * c)`; `Tower.exists_mul_assoc_ne_level_seven`
  is dimension 128.

The results state the existence of one violating triple per level and no
count of violating triples.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [NonAssocRing R] [StarRing R]

/-- The embedding `x ↦ (x, 0)` of level `k` into level `k + 1` preserves
products. -/
theorem mk_zero_mul_mk_zero {k : ℕ} (a c : Tower R k) : mk a 0 * mk c 0 = mk (a * c) 0 := by
  rw [mk_mul_mk, star_zero, zero_mul, sub_zero, zero_mul, zero_mul, add_zero]

/-- A triple of level `k` that violates associativity gives one of level
`k + 1` under the embedding `x ↦ (x, 0)`. -/
theorem mul_assoc_ne_mk_zero {k : ℕ} {a b c : Tower R k} (h : a * b * c ≠ a * (b * c)) :
    mk a 0 * mk b 0 * mk c 0 ≠ mk a 0 * (mk b 0 * mk c 0) := by
  simp only [mk_zero_mul_mk_zero]
  intro hm
  exact h (mk_inj.1 hm).1

/-- Over a ring in which `2 ≠ 0`, no basis element equals its negative. -/
theorem e_ne_neg_e (h2 : (2 : R) ≠ 0) : ∀ (k : ℕ) (p : BitVec k), e R k p ≠ -e R k p
  | 0, _ => by
    intro h
    have h1 : (1 : R) = -1 := h
    apply h2
    calc (2 : R) = 1 + 1 := one_add_one_eq_two.symm
      _ = -1 + 1 := by rw [← h1]
      _ = 0 := neg_add_cancel 1
  | k + 1, p => by
    intro h
    cases hp : p.msb
    · rw [e_succ_of_not_msb hp, neg_mk, neg_zero] at h
      exact e_ne_neg_e h2 k _ (mk_inj.1 h).1
    · rw [e_succ_of_msb hp, neg_mk, neg_zero] at h
      exact e_ne_neg_e h2 k _ (mk_inj.1 h).2

/-- In the octonions over a ring in which `2 ≠ 0`, `(e 1 * e 2) * e 4 = e 7`
and `e 1 * (e 2 * e 4) = -e 7`, so the two products differ. -/
theorem octonion_e1_e2_e4_mul_assoc_ne (h2 : (2 : R) ≠ 0) :
    e R 3 1#3 * e R 3 2#3 * e R 3 4#3 ≠ e R 3 1#3 * (e R 3 2#3 * e R 3 4#3) := by
  have p12 : e R 3 1#3 * e R 3 2#3 = e R 3 3#3 := by
    rw [e_mul_e, show negSign 3 1#3 2#3 = false by decide]
    exact ite_eq_right Bool.false_ne_true
  have p34 : e R 3 3#3 * e R 3 4#3 = e R 3 7#3 := by
    rw [e_mul_e, show negSign 3 3#3 4#3 = false by decide]
    exact ite_eq_right Bool.false_ne_true
  have p24 : e R 3 2#3 * e R 3 4#3 = e R 3 6#3 := by
    rw [e_mul_e, show negSign 3 2#3 4#3 = false by decide]
    exact ite_eq_right Bool.false_ne_true
  have p16 : e R 3 1#3 * e R 3 6#3 = -e R 3 7#3 := by
    rw [e_mul_e, show negSign 3 1#3 6#3 = true by decide]
    exact ite_eq_left rfl
  rw [p12, p34, p24, p16]
  exact e_ne_neg_e h2 3 7#3

/-- At every level `k ≥ 3` of the tower over a ring with a star in which
`2 ≠ 0`, some triple violates associativity. -/
theorem exists_mul_assoc_ne (h2 : (2 : R) ≠ 0) :
    ∀ k : ℕ, 3 ≤ k → ∃ a b c : Tower R k, a * b * c ≠ a * (b * c) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact ⟨_, _, _, octonion_e1_e2_e4_mul_assoc_ne h2⟩
  | succ k _ ih =>
    obtain ⟨a, b, c, h⟩ := ih
    exact ⟨mk a 0, mk b 0, mk c 0, mul_assoc_ne_mk_zero h⟩

/-- The 128-dimensional algebra, level `7`, is not associative. -/
theorem exists_mul_assoc_ne_level_seven (h2 : (2 : R) ≠ 0) :
    ∃ a b c : Tower R 7, a * b * c ≠ a * (b * c) :=
  exists_mul_assoc_ne h2 7 (by decide)

end Tower

end CayleyDickson
