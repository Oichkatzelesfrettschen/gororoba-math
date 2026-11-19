/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TwoTerm
public import GororobaMath.CayleyDickson.NonAssociative
public import GororobaMath.CayleyDickson.AnnihilatorSymmetry

/-!
# Zero divisors persist from level 4

Convention: `Tower R k` is the tower of `GororobaMath.CayleyDickson.Tower` over a nontrivial ring
`R` with a star, with the product `(a, b) (c, d) = (a c - star d b, d a + b star c)`, and
`Tower.e R k p`, `p : BitVec k`, is the basis unit of index `p`. The sedenion product
`(e₁ + e₁₀)(e₅ + e₁₄) = 0` (`Tower.sedenion_e1_add_e10_mul_e5_add_e14`) has two nonzero factors, and
`x ↦ (x, 0)` preserves products and nonzero elements, so a zero-divisor pair exists at every level
`k ≥ 4`. Over an ordered domain the trace form `Tower.dot k` then fails to multiply: the product
of the pair has `dot = 0` while both factors have `dot ≠ 0`.

## Main results

* `Tower.exists_zero_divisor`: the Rocq original is `zd_edge_count_base_case` of
  `rocq/open/verified/C957_VoudonZD.v`, which states the sedenion case and asserts the
  persistence in its header.
* `Tower.exists_dot_mul_self_ne`: the Rocq `hurwitz_fails_implies_zd_persistent` of the same file.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

section Ring

variable {R : Type u} [NonAssocRing R] [StarRing R] [Nontrivial R]

/-- Every basis unit is nonzero over a nontrivial ring. -/
theorem e_ne_zero : ∀ (k : ℕ) (p : BitVec k), e R k p ≠ 0
  | 0, _ => fun h => one_ne_zero (show (1 : R) = 0 from h)
  | k + 1, p => by
    by_cases hp : p.msb
    · rw [e_succ_of_msb hp]
      intro h
      exact e_ne_zero k _ (mk_inj.1 (h.trans (zero_eq_mk k))).2
    · rw [e_succ_of_not_msb (by simpa using hp)]
      intro h
      exact e_ne_zero k _ (mk_inj.1 (h.trans (zero_eq_mk k))).1

/-- A unit with top bit `0` plus a unit with top bit `1` is nonzero. -/
theorem e_add_e_ne_zero {k : ℕ} {p q : BitVec (k + 1)} (hp : p.msb = false) (hq : q.msb = true) :
    e R (k + 1) p + e R (k + 1) q ≠ 0 := by
  rw [e_succ_of_not_msb hp, e_succ_of_msb hq]
  change mk (e R k (p.setWidth k) + 0) (0 + e R k (q.setWidth k)) ≠ 0
  rw [add_zero, zero_add]
  intro h
  exact e_ne_zero k _ (mk_inj.1 (h.trans (zero_eq_mk k))).1

omit [Nontrivial R] in
/-- The embedding `x ↦ (x, 0)` keeps a zero-divisor pair a zero-divisor pair. -/
theorem exists_zero_divisor_succ {k : ℕ} (h : ∃ a b : Tower R k, a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0) :
    ∃ a b : Tower R (k + 1), a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 := by
  obtain ⟨a, b, ha, hb, hab⟩ := h
  refine ⟨mk a 0, mk b 0, fun h => ha ?_, fun h => hb ?_, ?_⟩
  · exact (mk_inj.1 (h.trans (zero_eq_mk k))).1
  · exact (mk_inj.1 (h.trans (zero_eq_mk k))).1
  · rw [mk_zero_mul_mk_zero, hab, zero_eq_mk]

/-- The tower holds a pair of nonzero elements with zero product at every level `k ≥ 4`, over every
nontrivial ring with a star. The Rocq original is `zd_edge_count_base_case` of
`rocq/open/verified/C957_VoudonZD.v`, which proves the sedenion case. -/
theorem exists_zero_divisor {k : ℕ} (hk : 4 ≤ k) :
    ∃ a b : Tower R k, a ≠ 0 ∧ b ≠ 0 ∧ a * b = 0 := by
  induction k, hk using Nat.le_induction with
  | base =>
    exact ⟨_, _, e_add_e_ne_zero (k := 3) (p := 1#4) (q := 10#4) (by decide) (by decide),
      e_add_e_ne_zero (k := 3) (p := 5#4) (q := 14#4) (by decide) (by decide),
      sedenion_e1_add_e10_mul_e5_add_e14⟩
  | succ k _ ih => exact exists_zero_divisor_succ ih

end Ring

section Ordered

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] [PartialOrder R]
  [IsOrderedAddMonoid R] [NoZeroDivisors R] [Nontrivial R]

omit [TrivialStar R] in
/-- The trace form of the product is not the product of the trace forms at any level `k ≥ 4` over a
nontrivial ordered domain: a zero-divisor pair has `dot (x * y) (x * y) = 0` while
`dot x x * dot y y ≠ 0`. The Rocq original is `hurwitz_fails_implies_zd_persistent` of
`rocq/open/verified/C957_VoudonZD.v`, which states the sedenion norm over the reals. -/
theorem exists_dot_mul_self_ne (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ} (hk : 4 ≤ k) :
    ∃ x y : Tower R k, dot k (x * y) (x * y) ≠ dot k x x * dot k y y := by
  obtain ⟨a, b, ha, hb, hab⟩ := exists_zero_divisor (R := R) hk
  refine ⟨a, b, ?_⟩
  rw [hab, dot_zero_left]
  exact (mul_ne_zero (dot_self_ne_zero hsq ha) (dot_self_ne_zero hsq hb)).symm

end Ordered

end Tower

end CayleyDickson
