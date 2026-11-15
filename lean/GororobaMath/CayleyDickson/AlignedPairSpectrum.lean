/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TwoTermRecursion

/-!
# The spectrum of the aligned-pair count and the mirror of its multiplicities

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

Moving the second term of the operand to the other half of the last
doubling, `j ↦ j ^^^ 2 ^ (k - 1)`, carries a nonzero count `n` to
`2 ^ (k - 1) - 4 - n`: the same-half and nondegenerate mixed cases of the
recursion share the low parts, and a degenerate low part has count `0` in
both. This involution of the ordered pairs gives the mirror of the
multiplicities.

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
* `Tower.alignedPairCount_add_flip`: the flip of the top bit of `j` mirrors
  a nonzero count about `2 ^ (k - 1) - 4`.
* `Tower.multiplicity_mirror`, `Tower.multiplicity_mirror_four_mul`: the
  number of ordered pairs `(i, j)` with count `n` equals the number with
  count `2 ^ (k - 1) - 4 - n` for `0 < n` and `n + 4 < 2 ^ (k - 1)`; in the
  issue's form, for `1 ≤ v ≤ 2 ^ (k - 3) - 2` with `n = 4 v` (a range that
  is empty below `k = 5`). Ordered pairs, pairs `i < j` and pairs `i ≠ j`
  give the same equation, since the count is symmetric
  (`Tower.alignedPairCount_comm`) and vanishes on `i = j`.
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


/-- A nonzero count forces nonzero, distinct indices. -/
theorem alignedPairCount_low_ne_of_ne_zero {k : ℕ} {a b : BitVec k}
    (h : alignedPairCount k a b ≠ 0) : a ≠ 0#k ∧ b ≠ 0#k ∧ a ≠ b := by
  refine ⟨fun ha => h ?_, fun hb => h ?_, fun hab => h ?_⟩
  · rw [ha, alignedPairCount_zero_left]
  · rw [hb, alignedPairCount_zero_right]
  · rw [hab, alignedPairCount_self]

/-- Exclusive or with the index of the unit that the last doubling adjoins
flips the top bit. -/
theorem cons_xor_top {k : ℕ} (J : Bool) (b : BitVec k) :
    BitVec.cons J b ^^^ BitVec.cons true 0#k = BitVec.cons (!J) b := by
  rw [BitVec.cons_xor_cons, BitVec.xor_zero]
  cases J <;> rfl

/-- Moving the second term of the operand to the other half of level
`k + 1` mirrors a nonzero count about `2 ^ k - 4`. -/
theorem alignedPairCount_add_flip {k : ℕ} (i j : BitVec (k + 1))
    (h : alignedPairCount (k + 1) i j ≠ 0) :
    alignedPairCount (k + 1) i j + alignedPairCount (k + 1) i (j ^^^ BitVec.cons true 0#k) + 4 =
      2 ^ k := by
  obtain ⟨I, a, rfl⟩ : ∃ I a, i = BitVec.cons I a := ⟨_, _, (BitVec.cons_msb_setWidth i).symm⟩
  obtain ⟨J, b, rfl⟩ : ∃ J b, j = BitVec.cons J b := ⟨_, _, (BitVec.cons_msb_setWidth j).symm⟩
  rw [cons_xor_top]
  by_cases hIJ : I = J
  · subst hIJ
    have hs := alignedPairCount_succ_of_msb_eq (i := BitVec.cons I a) (j := BitVec.cons I b)
      (by simp)
    rw [BitVec.setWidth_cons, BitVec.setWidth_cons] at hs
    obtain ⟨ha, hb, hab⟩ := alignedPairCount_low_ne_of_ne_zero (a := a) (b := b) (by omega)
    have hm := alignedPairCount_succ_add (i := BitVec.cons I a) (j := BitVec.cons (!I) b)
      (by cases I <;> simp) (by rwa [BitVec.setWidth_cons]) (by rwa [BitVec.setWidth_cons])
      (by rwa [BitVec.setWidth_cons, BitVec.setWidth_cons])
    rw [BitVec.setWidth_cons, BitVec.setWidth_cons] at hm
    omega
  · have hJ : (!J) = I := by cases I <;> cases J <;> simp_all
    have hmsb : (BitVec.cons I a).msb ≠ (BitVec.cons J b).msb := by simpa using hIJ
    by_cases hd : a = 0#k ∨ b = 0#k ∨ a = b
    · exact absurd (alignedPairCount_succ_eq_zero hmsb
        (by simpa only [BitVec.setWidth_cons] using hd)) h
    · simp only [not_or] at hd
      have hm := alignedPairCount_succ_add hmsb (by rw [BitVec.setWidth_cons]; exact hd.1)
        (by rw [BitVec.setWidth_cons]; exact hd.2.1)
        (by rw [BitVec.setWidth_cons, BitVec.setWidth_cons]; exact hd.2.2)
      have hs := alignedPairCount_succ_of_msb_eq (i := BitVec.cons I a) (j := BitVec.cons (!J) b)
        (by simp [hJ])
      rw [BitVec.setWidth_cons, BitVec.setWidth_cons] at hm hs
      omega

/-- The number of ordered pairs of indices at level `k` whose count is `n`. -/
def alignedPairCountMultiplicity (k n : ℕ) : ℕ :=
  (Finset.univ.filter fun p : BitVec k × BitVec k => alignedPairCount k p.1 p.2 = n).card

/-- The mirror at level `k + 1`, through the flip of the top bit of `j`. -/
theorem multiplicity_succ_mirror (k n : ℕ) (hn : n ≠ 0) (hn' : n + 4 < 2 ^ k) :
    alignedPairCountMultiplicity (k + 1) n =
      alignedPairCountMultiplicity (k + 1) (2 ^ k - 4 - n) := by
  unfold alignedPairCountMultiplicity
  refine Finset.card_bij' (fun p _ => (p.1, p.2 ^^^ BitVec.cons true 0#k))
    (fun p _ => (p.1, p.2 ^^^ BitVec.cons true 0#k))
    ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have := alignedPairCount_add_flip p.1 p.2 (by omega)
    omega
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    have := alignedPairCount_add_flip p.1 p.2 (by omega)
    omega
  · intro p _
    simp
  · intro p _
    simp

/-- **Mirror of multiplicities.** For `0 < n` and `n + 4 < 2 ^ (k - 1)`, as many
ordered pairs have count `n` as have count `2 ^ (k - 1) - 4 - n`. -/
theorem multiplicity_mirror (k n : ℕ) (hn : n ≠ 0) (hn' : n + 4 < 2 ^ (k - 1)) :
    alignedPairCountMultiplicity k n = alignedPairCountMultiplicity k (2 ^ (k - 1) - 4 - n) := by
  rcases k with _ | k
  · have : 2 ^ (0 - 1) = 1 := rfl
    omega
  · rw [Nat.add_sub_cancel] at hn' ⊢
    exact multiplicity_succ_mirror k n hn hn'

/-- The mirror in the form of the issue: for `1 ≤ v ≤ 2 ^ (k - 3) - 2`, as many
ordered pairs have count `4 v` as have count `2 ^ (k - 1) - 4 - 4 v`. The
range is empty below `k = 5`. -/
theorem multiplicity_mirror_four_mul (k v : ℕ) (hv : 1 ≤ v) (hv' : v ≤ 2 ^ (k - 3) - 2) :
    alignedPairCountMultiplicity k (4 * v) =
      alignedPairCountMultiplicity k (2 ^ (k - 1) - 4 - 4 * v) := by
  apply multiplicity_mirror k (4 * v) (by omega)
  rcases Nat.lt_or_ge k 3 with hk | hk
  · have : 2 ^ (k - 3) = 1 := by rw [show k - 3 = 0 by omega]; rfl
    omega
  · have : 2 ^ (k - 1) = 4 * 2 ^ (k - 3) := by
      rw [show k - 1 = (k - 3) + 2 by omega, pow_add]; ring
    omega

end Tower

end CayleyDickson
