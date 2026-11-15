/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TwoTermRecursion

/-!
# The spectrum of the aligned-pair count

`alignedPairCount k i j` (`N k i j` below) counts the aligned pairs of the
operand `e i + e j` at level `k` of the tower, with the indices as bit
vectors, top bit outermost, and the signs `Tower.negSign` of
`cd_core.cd_sign`. Every count is a multiple of `4`
(`Tower.four_dvd_alignedPairCount`), and from `k = 3` on every count
satisfies `N k i j + 4 ≤ 2 ^ (k - 1)`.

The values are exactly the multiples of `4` up to `2 ^ (k - 1) - 4` for
every `k ≥ 3` (`k = 3` has the single value `0`; the statement about
`k ≥ 4` is its instance). The pairs come from the doubling recursion
(`Tower.alignedPairCount_succ_cases`) by induction on `k` carrying
nonzero, distinct low parts: `v = 2w` doubles a level-`k` pair of count
`4w` in the first half, and `v = 2w + 1` takes a level-`k` pair `(a, b)`
of count `2 ^ (k - 1) - 4 - 4w` and moves its second term to the second
half, where the mixed case gives `2 ^ k - 4 - 2 * N k a b = 4v`. Through
`Tower.finrank_ker_mulLeft_e_add_e` the same set is the set of kernel
ranks of left multiplication by `e i + e j`.

## Main results

* `Tower.alignedPairCount_add_four_le_of_three_le`: `N k i j + 4 ≤ 2 ^ (k - 1)`
  for every pair at every level `k ≥ 3`.
* `Tower.exists_alignedPairCount_eq`: every multiple `4 v` with
  `4 v + 4 ≤ 2 ^ (k - 1)` is the count of a pair of nonzero distinct
  indices, at every level.
* `Tower.exists_alignedPairCount_add_four_eq`: the bound is attained for
  `k ≥ 3`.
* `Tower.range_alignedPairCount`: for `k ≥ 3` the set of counts is
  `{n | 4 ∣ n ∧ n + 4 ≤ 2 ^ (k - 1)}`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

/-- `2 ^ (k - 1)` is at least `4` from `k = 3` on. -/
theorem four_le_two_pow_sub_one {k : ℕ} (hk : 3 ≤ k) : 4 ≤ 2 ^ (k - 1) :=
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Bound.** From `k = 3` on every count satisfies
`N k i j + 4 ≤ 2 ^ (k - 1)`, the value `0` included. -/
theorem alignedPairCount_add_four_le_of_three_le {k : ℕ} (hk : 3 ≤ k) (i j : BitVec k) :
    alignedPairCount k i j + 4 ≤ 2 ^ (k - 1) := by
  have h4 := four_le_two_pow_sub_one hk
  rcases alignedPairCount_eq_zero_or_add_four_le k i j with h | h <;> omega

/-- An index with a nonzero low part is nonzero. -/
theorem cons_ne_zero_of_ne_zero {k : ℕ} (b : Bool) {p : BitVec k} (hp : p ≠ 0#k) :
    BitVec.cons b p ≠ 0#(k + 1) := fun h => hp ((cons_eq_zero_iff b p).1 h).2

/-- An index in the second half is nonzero. -/
theorem cons_true_ne_zero {k : ℕ} (p : BitVec k) : BitVec.cons true p ≠ 0#(k + 1) :=
  fun h => by simpa using ((cons_eq_zero_iff true p).1 h).1

/-- **Every value occurs.** Every multiple `4 v` with `4 v + 4 ≤ 2 ^ (k - 1)` is
the count of a pair of nonzero distinct indices, at every level `k` (the
hypothesis has no solution for `k ≤ 2`). -/
theorem exists_alignedPairCount_eq :
    ∀ (k v : ℕ), 4 * v + 4 ≤ 2 ^ (k - 1) →
      ∃ i j : BitVec k, i ≠ 0#k ∧ j ≠ 0#k ∧ i ≠ j ∧ alignedPairCount k i j = 4 * v
  | 0, v, h => by
    have : 2 ^ (0 - 1) = 1 := rfl
    omega
  | k + 1, v, h => by
    rw [Nat.add_sub_cancel] at h
    rcases Nat.lt_or_ge k 3 with hk | hk
    · interval_cases k
      · norm_num at h
      · norm_num at h
      · have hv : v = 0 := by norm_num at h; omega
        subst hv
        exact ⟨1#3, 2#3, by decide, by decide, by decide,
          alignedPairCount_eq_zero_of_le_three le_rfl _ _⟩
    · obtain ⟨m, hm⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
      have hP : 2 ^ k = 8 * 2 ^ m := by rw [hm]; ring
      have hP1 : 2 ^ (k - 1) = 4 * 2 ^ m := by
        rw [hm, show m + 3 - 1 = m + 2 by omega]; ring
      rcases Nat.even_or_odd v with ⟨w, rfl⟩ | ⟨w, rfl⟩
      · obtain ⟨a, b, ha, hb, hab, hN⟩ := exists_alignedPairCount_eq k w (by omega)
        refine ⟨BitVec.cons false a, BitVec.cons false b, cons_ne_zero_of_ne_zero _ ha,
          cons_ne_zero_of_ne_zero _ hb, fun h => hab ?_, ?_⟩
        · simpa using congrArg (BitVec.setWidth k) h
        · rw [alignedPairCount_succ_of_msb_eq (i := BitVec.cons false a) (j := BitVec.cons false b)
            (by simp), BitVec.setWidth_cons,
            BitVec.setWidth_cons, hN]
          ring
      · obtain ⟨a, b, ha, hb, hab, hN⟩ := exists_alignedPairCount_eq k (2 ^ m - 1 - w) (by omega)
        refine ⟨BitVec.cons false a, BitVec.cons true b, cons_ne_zero_of_ne_zero _ ha,
          cons_true_ne_zero b, fun h => by simpa using congrArg BitVec.msb h, ?_⟩
        have hs := alignedPairCount_succ_add (i := BitVec.cons false a) (j := BitVec.cons true b)
          (by simp) (by rwa [BitVec.setWidth_cons]) (by rwa [BitVec.setWidth_cons])
          (by rwa [BitVec.setWidth_cons, BitVec.setWidth_cons])
        rw [BitVec.setWidth_cons, BitVec.setWidth_cons, hN] at hs
        omega

/-- **The bound is sharp.** For `k ≥ 3` some pair attains
`N k i j + 4 = 2 ^ (k - 1)`. -/
theorem exists_alignedPairCount_add_four_eq {k : ℕ} (hk : 3 ≤ k) :
    ∃ i j : BitVec k, alignedPairCount k i j + 4 = 2 ^ (k - 1) := by
  have h4 := four_le_two_pow_sub_one hk
  obtain ⟨c, hc⟩ : ∃ c, 2 ^ (k - 1) = 4 * c :=
    ⟨2 ^ (k - 3), by rw [show k - 1 = (k - 3) + 2 by omega, pow_add]; ring⟩
  obtain ⟨i, j, -, -, -, h⟩ := exists_alignedPairCount_eq k (c - 1) (by omega)
  exact ⟨i, j, by omega⟩

/-- **Spectrum.** For `k ≥ 3` the counts of all pairs are exactly the
multiples of `4` from `0` to `2 ^ (k - 1) - 4`. -/
theorem range_alignedPairCount {k : ℕ} (hk : 3 ≤ k) :
    Set.range (fun p : BitVec k × BitVec k => alignedPairCount k p.1 p.2) =
      {n | 4 ∣ n ∧ n + 4 ≤ 2 ^ (k - 1)} := by
  ext n
  simp only [Set.mem_range, Prod.exists, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨i, j, rfl⟩
    exact ⟨four_dvd_alignedPairCount k i j, alignedPairCount_add_four_le_of_three_le hk i j⟩
  · rintro ⟨⟨v, rfl⟩, h⟩
    obtain ⟨i, j, -, -, -, hN⟩ := exists_alignedPairCount_eq k v h
    exact ⟨i, j, hN⟩

end Tower

end CayleyDickson
