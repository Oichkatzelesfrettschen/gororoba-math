/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AlignedPairEndpoints

/-!
# The total of the aligned-pair counts over a level

The convention is that of `Tower.alignedPairCount` (`N k i j` below): the indices are bit vectors
with the top bit outermost, and a pair `(i, j)` is an ordered pair of indices of level `k`. The
pairs summed here are the ordered pairs of nonzero distinct indices, the predicate of
`Tower.zeroCount` without its count condition; `Tower.alignedPairTotal k` is the sum of
`N k i j` over them, and the sum over unordered pairs is half of it.

The doubling recursion (`Tower.alignedPairCount_succ_cases`) splits the pairs of level `k + 1` by
their top bits. The two same-half cases contribute `2 * N k a b` each. The two different-half
cases contribute `2 ^ k - 4 - 2 * N k a b` at every pair of low parts `(a, b)` that is nonzero
and distinct, and `0` at the other pairs. The total at level `k` cancels from the sum, so level
`k + 1` is a function of `k` alone.

The value `2 * (2 ^ k - 1) * (2 ^ k - 2) * (2 ^ k - 4)` at level `k + 1` is the total that
Abdessalem, "Unveiling the structure of Cayley-Dickson algebras" (2025 draft), Theorem 3.1, states
as a conjectured counting formula; its unordered values at levels `4`, `5` and `6` are `168`,
`2520` and `26040`. The sum here is a sum of the nullities `alignedPairCount`
of left multiplication by `e i + e j`; its reading as a count of zero-divisor pairs is the source's
reading and is not proved here.

## Main results

* `Tower.alignedPairTotal_succ_add`: `T (k + 1) + 8 * D = 2 * 2 ^ k * D` with
  `D = (2 ^ k - 1) * (2 ^ k - 2)`, the number of nonzero distinct pairs of level `k`.
* `Tower.alignedPairTotal_succ`: `T (k + 1) = 2 * (2 ^ k - 1) * (2 ^ k - 2) * (2 ^ k - 4)`, at
  every `k` (the natural subtraction makes the right side `0` for `k ≤ 2`).
* `Tower.alignedPairTotal_four`, `Tower.alignedPairTotal_five`, `Tower.alignedPairTotal_six`:
  the values `336`, `5040` and `52080`, each twice the unordered value.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

/-- The ordered pairs of nonzero distinct indices of level `k`. -/
def nonzeroDistinctPairs (k : ℕ) : Finset (BitVec k × BitVec k) :=
  Finset.univ.filter fun p => p.1 ≠ 0#k ∧ p.2 ≠ 0#k ∧ p.1 ≠ p.2

theorem mem_nonzeroDistinctPairs {k : ℕ} {p : BitVec k × BitVec k} :
    p ∈ nonzeroDistinctPairs k ↔ p.1 ≠ 0#k ∧ p.2 ≠ 0#k ∧ p.1 ≠ p.2 := by
  simp only [nonzeroDistinctPairs, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The nonzero distinct ordered pairs of level `k` number `(2 ^ k - 1) * (2 ^ k - 2)`. -/
theorem card_nonzeroDistinctPairs (k : ℕ) :
    (nonzeroDistinctPairs k).card = (2 ^ k - 1) * (2 ^ k - 2) := by
  have hnz : (Finset.univ.filter fun x : BitVec k => x ≠ 0#k).card = 2 ^ k - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      card_bitVec]
  have hfib : ∀ a : BitVec k, a ≠ 0#k →
      (Finset.univ.filter fun b : BitVec k => a ≠ 0#k ∧ b ≠ 0#k ∧ a ≠ b).card = 2 ^ k - 2 := by
    intro a ha
    have hset : (Finset.univ.filter fun b : BitVec k => a ≠ 0#k ∧ b ≠ 0#k ∧ a ≠ b) =
        (Finset.univ.erase 0#k).erase a := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
      exact ⟨fun h => ⟨h.2.2.symm, h.2.1⟩, fun h => ⟨ha, h.2, h.1.symm⟩⟩
    rw [hset, Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨ha, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, card_bitVec]
    omega
  have hrow : ∀ a : BitVec k, (∑ b : BitVec k,
      if a ≠ 0#k ∧ b ≠ 0#k ∧ a ≠ b then 1 else 0) = if a ≠ 0#k then 2 ^ k - 2 else 0 := by
    intro a
    by_cases ha : a = 0#k
    · simp [ha]
    · have h := hfib a ha
      rw [Finset.card_filter] at h
      simpa [ha] using h
  rw [nonzeroDistinctPairs, Finset.card_filter, Fintype.sum_prod_type]
  simp only [hrow]
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, hnz]

/-- The sum of `N k i j` over the ordered pairs of nonzero distinct indices of level `k`. -/
def alignedPairTotal (k : ℕ) : ℕ :=
  ∑ p ∈ nonzeroDistinctPairs k, alignedPairCount k p.1 p.2

/-- A function that vanishes off the nonzero distinct pairs sums over them as over all pairs. -/
theorem sum_univ_eq_sum_nonzeroDistinctPairs {k : ℕ} (f : BitVec k × BitVec k → ℕ)
    (hf : ∀ p, p ∉ nonzeroDistinctPairs k → f p = 0) :
    ∑ p, f p = ∑ p ∈ nonzeroDistinctPairs k, f p :=
  (Finset.sum_subset (Finset.subset_univ _) fun p _ hp => hf p hp).symm

/-- The count vanishes at a pair with a zero term or equal terms. -/
theorem alignedPairCount_eq_zero_of_not_mem {k : ℕ} {p : BitVec k × BitVec k}
    (hp : p ∉ nonzeroDistinctPairs k) : alignedPairCount k p.1 p.2 = 0 := by
  rw [mem_nonzeroDistinctPairs] at hp
  by_cases h1 : p.1 = 0#k
  · rw [h1, alignedPairCount_zero_left]
  by_cases h2 : p.2 = 0#k
  · rw [h2, alignedPairCount_zero_right]
  have h3 : p.1 = p.2 := by
    by_contra h3
    exact hp ⟨h1, h2, h3⟩
  rw [h3, alignedPairCount_self]

/-- The total is the sum over all ordered pairs. -/
theorem alignedPairTotal_eq_sum (k : ℕ) :
    alignedPairTotal k = ∑ p : BitVec k × BitVec k, alignedPairCount k p.1 p.2 :=
  (sum_univ_eq_sum_nonzeroDistinctPairs (fun p => alignedPairCount k p.1 p.2)
    fun _ hp => alignedPairCount_eq_zero_of_not_mem hp).symm

/-- Two indices in the same half: the sum over the low parts doubles the total. -/
theorem sum_cons_same (k : ℕ) (I : Bool) :
    ∑ y : BitVec k × BitVec k, alignedPairCount (k + 1) (BitVec.cons I y.1) (BitVec.cons I y.2) =
      2 * alignedPairTotal k := by
  rw [alignedPairTotal_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => alignedPairCount_cons_same I y.1 y.2

/-- Two indices in different halves: the counts and twice the level-`k` counts of the low
parts add to `2 ^ k` at each nonzero distinct pair of low parts, and the count is `0` at the
other pairs. -/
theorem sum_cons_mixed_add (k : ℕ) {I J : Bool} (hIJ : I ≠ J) :
    (∑ y : BitVec k × BitVec k,
        alignedPairCount (k + 1) (BitVec.cons I y.1) (BitVec.cons J y.2)) +
      2 * alignedPairTotal k + 4 * ((2 ^ k - 1) * (2 ^ k - 2)) =
      2 ^ k * ((2 ^ k - 1) * (2 ^ k - 2)) := by
  have hm : ∀ a b : BitVec k, (BitVec.cons I a).msb ≠ (BitVec.cons J b).msb := fun a b => by
    simpa using hIJ
  have h0 : ∀ y : BitVec k × BitVec k, y ∉ nonzeroDistinctPairs k →
      alignedPairCount (k + 1) (BitVec.cons I y.1) (BitVec.cons J y.2) = 0 := by
    intro y hy
    rw [mem_nonzeroDistinctPairs] at hy
    have hd : y.1 = 0#k ∨ y.2 = 0#k ∨ y.1 = y.2 := by
      by_contra h
      push Not at h
      exact hy ⟨h.1, h.2.1, h.2.2⟩
    exact alignedPairCount_succ_eq_zero (hm y.1 y.2)
      (by simpa only [BitVec.setWidth_cons] using hd)
  rw [sum_univ_eq_sum_nonzeroDistinctPairs _ h0]
  have hS : ∑ y ∈ nonzeroDistinctPairs k,
      (alignedPairCount (k + 1) (BitVec.cons I y.1) (BitVec.cons J y.2) +
        2 * alignedPairCount k y.1 y.2 + 4) = ∑ _y ∈ nonzeroDistinctPairs k, 2 ^ k :=
    Finset.sum_congr rfl fun y hy => by
      rw [mem_nonzeroDistinctPairs] at hy
      exact alignedPairCount_cons_mixed_add hIJ hy.1 hy.2.1 hy.2.2
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hS
  simp only [Finset.sum_const, smul_eq_mul, card_nonzeroDistinctPairs] at hS
  unfold alignedPairTotal
  linarith [hS]

/-- The four top-bit cases of the recursion give the total of level `k + 1` from the number of
nonzero distinct pairs of level `k`. -/
theorem alignedPairTotal_succ_add (k : ℕ) :
    alignedPairTotal (k + 1) + 8 * ((2 ^ k - 1) * (2 ^ k - 2)) =
      2 * 2 ^ k * ((2 ^ k - 1) * (2 ^ k - 2)) := by
  have e2 : ∀ g : Bool × Bool → ℕ,
      ∑ x, g x = g (true, true) + g (true, false) + (g (false, true) + g (false, false)) := by
    intro g
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
  have h1 := sum_cons_same k true
  have h2 := sum_cons_same k false
  have h3 := sum_cons_mixed_add k (I := true) (J := false) (by decide)
  have h4 := sum_cons_mixed_add k (I := false) (J := true) (by decide)
  rw [alignedPairTotal_eq_sum (k + 1), ← (consPairEquiv k).sum_comp, Fintype.sum_prod_type, e2]
  simp only [consPairEquiv, Equiv.coe_fn_mk]
  linarith

/-- The total over the ordered pairs of nonzero distinct indices of level `k + 1`:
`2 * (2 ^ k - 1) * (2 ^ k - 2) * (2 ^ k - 4)`. -/
theorem alignedPairTotal_succ (k : ℕ) :
    alignedPairTotal (k + 1) = 2 * (2 ^ k - 1) * (2 ^ k - 2) * (2 ^ k - 4) := by
  have h := alignedPairTotal_succ_add k
  by_cases hk : 2 ≤ k
  · have h4 : 4 ≤ 2 ^ k :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le h4
    rw [ht, Nat.add_sub_cancel_left]
    rw [ht] at h
    rw [show 2 * (4 + t - 1) * (4 + t - 2) * t = 2 * ((4 + t - 1) * (4 + t - 2)) * t by ring]
    generalize (4 + t - 1) * (4 + t - 2) = D at h ⊢
    nlinarith [h]
  · have hk' : k = 0 ∨ k = 1 := by omega
    rcases hk' with rfl | rfl <;> simp_all

/-- The total at level `4` is `336`, twice `168`. -/
theorem alignedPairTotal_four : alignedPairTotal 4 = 336 := by
  rw [alignedPairTotal_succ 3]
  norm_num

/-- The total at level `5` is `5040`, twice `2520`. -/
theorem alignedPairTotal_five : alignedPairTotal 5 = 5040 := by
  rw [alignedPairTotal_succ 4]
  norm_num

/-- The total at level `6` is `52080`, twice `26040`. -/
theorem alignedPairTotal_six : alignedPairTotal 6 = 52080 := by
  rw [alignedPairTotal_succ 5]
  norm_num

end Tower

end CayleyDickson
