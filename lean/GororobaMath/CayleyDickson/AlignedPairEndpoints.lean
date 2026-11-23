/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AlignedPairSpectrum

/-!
# Counts of the aligned-pair spectrum at its two ends

The convention is that of `Tower.alignedPairCount` (`N k i j` below): the
indices are bit vectors with the top bit outermost, and a pair `(i, j)` is
an ordered pair of indices of level `k`. `Tower.alignedPairCountMultiplicity k n`
is the number of ordered pairs with count `n`. `Tower.zeroCount k` is the number
of ordered pairs of nonzero distinct indices with count `0`.

`Tower.multiplicity_mirror` excludes the ends `n = 0` and `n = 2 ^ (k - 1) - 4` of
the spectrum. The doubling recursion (`Tower.alignedPairCount_succ_cases`)
reaches the top value `2 ^ k - 4` of level `k + 1` only through two indices in
different halves with nonzero distinct low parts of count `0`, which gives
the multiplicity of the top value as twice `zeroCount k`. Splitting the pairs of
level `k + 1` by their top bits gives `zeroCount (k + 1)` from `zeroCount k`: the
same-half pairs contribute through the low parts, and the different-half
pairs contribute exactly the degenerate low parts, since a count of `0` in the
nondegenerate case would need a low count `2 ^ (k - 1) - 2`, above the bound.

## Main results

* `Tower.alignedPairCountMultiplicity_succ_top`: for `3 ≤ k`, the number of
  ordered pairs of level `k + 1` with count `2 ^ k - 4` is `2 * zeroCount k`.
* `Tower.zeroCount_succ`: for `3 ≤ k`,
  `zeroCount (k + 1) = 2 * zeroCount k + 6 * (2 ^ k - 1)`.
* `Tower.zeroCount_five`, `Tower.alignedPairCountMultiplicity_four_four`,
  `Tower.alignedPairCountMultiplicity_five_twelve`,
  `Tower.alignedPairCountMultiplicity_six_twentyEight`,
  `Tower.alignedPairCountMultiplicity_seven_sixty`: the values `342`, `84`, `252`,
  `684` and `1740`, from the recurrences and the base value `zeroCount 3 = 42`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

/-- The pairs counted by `zeroCount`: nonzero distinct indices with count `0`. -/
def zeroPred (k : ℕ) (p : BitVec k × BitVec k) : Prop :=
  p.1 ≠ 0#k ∧ p.2 ≠ 0#k ∧ p.1 ≠ p.2 ∧ alignedPairCount k p.1 p.2 = 0

instance (k : ℕ) : DecidablePred (zeroPred k) := fun p => by
  unfold zeroPred
  infer_instance

/-- The number of ordered pairs of nonzero distinct indices at level `k` with
count `0`. -/
def zeroCount (k : ℕ) : ℕ :=
  (Finset.univ.filter (zeroPred k)).card

/-- Top bits and low parts of an ordered pair of indices of level `k + 1`. -/
def consPairEquiv (k : ℕ) :
    (Bool × Bool) × (BitVec k × BitVec k) ≃ BitVec (k + 1) × BitVec (k + 1) where
  toFun q := (BitVec.cons q.1.1 q.2.1, BitVec.cons q.1.2 q.2.2)
  invFun p := ((p.1.msb, p.2.msb), (p.1.setWidth k, p.2.setWidth k))
  left_inv := by
    rintro ⟨⟨I, J⟩, ⟨a, b⟩⟩
    simp
  right_inv := by
    rintro ⟨i, j⟩
    simp [BitVec.cons_msb_setWidth]

/-- A count over the ordered pairs of level `k + 1` is the sum of the counts
over the four choices of top bits. -/
private theorem card_filter_prod_cons {k : ℕ} (Q : BitVec (k + 1) × BitVec (k + 1) → Prop)
    [DecidablePred Q] :
    (Finset.univ.filter Q).card =
      ((Finset.univ.filter fun p : BitVec k × BitVec k =>
          Q (BitVec.cons true p.1, BitVec.cons true p.2)).card +
        (Finset.univ.filter fun p : BitVec k × BitVec k =>
          Q (BitVec.cons true p.1, BitVec.cons false p.2)).card) +
      ((Finset.univ.filter fun p : BitVec k × BitVec k =>
          Q (BitVec.cons false p.1, BitVec.cons true p.2)).card +
        (Finset.univ.filter fun p : BitVec k × BitVec k =>
          Q (BitVec.cons false p.1, BitVec.cons false p.2)).card) := by
  simp only [Finset.card_filter]
  rw [← (consPairEquiv k).sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  rfl

/-- `2 ^ k` is twice `2 ^ (k - 1)` from `k = 1` on. -/
private theorem two_pow_eq_two_mul_pred {k : ℕ} (hk : 1 ≤ k) : 2 ^ k = 2 * 2 ^ (k - 1) := by
  rw [← pow_succ']
  congr 1
  omega

/-- Two indices in the same half: the count doubles the count of the low parts. -/
theorem alignedPairCount_cons_same {k : ℕ} (I : Bool) (a b : BitVec k) :
    alignedPairCount (k + 1) (BitVec.cons I a) (BitVec.cons I b) =
      2 * alignedPairCount k a b := by
  have h := alignedPairCount_succ_of_msb_eq (i := BitVec.cons I a) (j := BitVec.cons I b)
    (by simp)
  simpa only [BitVec.setWidth_cons] using h

/-- Two indices in different halves with nonzero distinct low parts. -/
theorem alignedPairCount_cons_mixed_add {k : ℕ} {I J : Bool} (hIJ : I ≠ J) {a b : BitVec k}
    (ha : a ≠ 0#k) (hb : b ≠ 0#k) (hab : a ≠ b) :
    alignedPairCount (k + 1) (BitVec.cons I a) (BitVec.cons J b) +
      2 * alignedPairCount k a b + 4 = 2 ^ k := by
  have hm : (BitVec.cons I a).msb ≠ (BitVec.cons J b).msb := by simpa using hIJ
  have hs := alignedPairCount_succ_add (i := BitVec.cons I a) (j := BitVec.cons J b) hm
    (by rwa [BitVec.setWidth_cons]) (by rwa [BitVec.setWidth_cons])
    (by rwa [BitVec.setWidth_cons, BitVec.setWidth_cons])
  rwa [BitVec.setWidth_cons, BitVec.setWidth_cons] at hs

/-- From `k = 3` on, two indices in different halves have count `0` exactly when a
low part is `0` or the low parts agree: the nondegenerate case would need the low
count `2 ^ (k - 1) - 2`, above the bound. -/
theorem alignedPairCount_cons_mixed_eq_zero_iff {k : ℕ} (hk : 3 ≤ k) {I J : Bool}
    (hIJ : I ≠ J) (a b : BitVec k) :
    alignedPairCount (k + 1) (BitVec.cons I a) (BitVec.cons J b) = 0 ↔
      a = 0#k ∨ b = 0#k ∨ a = b := by
  have hm : (BitVec.cons I a).msb ≠ (BitVec.cons J b).msb := by simpa using hIJ
  constructor
  · intro h
    by_contra hd
    simp only [not_or] at hd
    have hs := alignedPairCount_cons_mixed_add hIJ hd.1 hd.2.1 hd.2.2
    have h4 := alignedPairCount_add_four_le_of_three_le hk a b
    have hp := two_pow_eq_two_mul_pred (k := k) (by omega)
    omega
  · intro hd
    exact alignedPairCount_succ_eq_zero hm (by simpa only [BitVec.setWidth_cons] using hd)

/-- From `k = 3` on, two indices in different halves reach the top value
`2 ^ k - 4` exactly when the low parts are nonzero, distinct and of count `0`. -/
theorem alignedPairCount_cons_mixed_eq_top_iff {k : ℕ} (hk : 3 ≤ k) {I J : Bool}
    (hIJ : I ≠ J) (a b : BitVec k) :
    alignedPairCount (k + 1) (BitVec.cons I a) (BitVec.cons J b) = 2 ^ k - 4 ↔
      a ≠ 0#k ∧ b ≠ 0#k ∧ a ≠ b ∧ alignedPairCount k a b = 0 := by
  have h8 : 8 ≤ 2 ^ k :=
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  constructor
  · intro h
    by_cases hd : a = 0#k ∨ b = 0#k ∨ a = b
    · have := (alignedPairCount_cons_mixed_eq_zero_iff hk hIJ a b).2 hd
      omega
    · simp only [not_or] at hd
      have hs := alignedPairCount_cons_mixed_add hIJ hd.1 hd.2.1 hd.2.2
      exact ⟨hd.1, hd.2.1, hd.2.2, by omega⟩
  · rintro ⟨ha, hb, hab, h0⟩
    have hs := alignedPairCount_cons_mixed_add hIJ ha hb hab
    omega

/-- Indices with a clear top bit are nonzero exactly when the low part is. -/
private theorem cons_false_ne_zero_iff {k : ℕ} (a : BitVec k) :
    BitVec.cons false a ≠ 0#(k + 1) ↔ a ≠ 0#k :=
  ⟨fun h ha => h (by rw [ha]; exact (cons_eq_zero_iff false 0#k).2 ⟨rfl, rfl⟩),
    cons_ne_zero_of_ne_zero false⟩

/-- Indices with equal top bits are equal exactly when the low parts are. -/
private theorem cons_same_eq_iff {k : ℕ} (I : Bool) (a b : BitVec k) :
    BitVec.cons I a = BitVec.cons I b ↔ a = b :=
  ⟨fun h => by simpa using congrArg (BitVec.setWidth k) h, fun h => by rw [h]⟩

/-- Indices in different halves are distinct. -/
private theorem cons_ne_cons_of_ne {k : ℕ} {I J : Bool} (hIJ : I ≠ J) (a b : BitVec k) :
    BitVec.cons I a ≠ BitVec.cons J b := fun h => hIJ (by simpa using congrArg BitVec.msb h)

/-- The nonzero indices of level `k` number `2 ^ k - 1`. -/
private theorem card_ne_zero_bitVec (k : ℕ) :
    (Finset.univ.filter fun x : BitVec k => x ≠ 0#k).card = 2 ^ k - 1 := by
  rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    card_bitVec]

/-- Pairs with a nonzero first term and a zero second term or equal terms. -/
private theorem card_left_ne_zero_right_zero_or_eq (k : ℕ) :
    (Finset.univ.filter fun p : BitVec k × BitVec k =>
      p.1 ≠ 0#k ∧ (p.2 = 0#k ∨ p.1 = p.2)).card = 2 * (2 ^ k - 1) := by
  have h : (Finset.univ.filter fun p : BitVec k × BitVec k =>
      p.1 ≠ 0#k ∧ (p.2 = 0#k ∨ p.1 = p.2)).card =
      ((Finset.univ.filter fun x : BitVec k => x ≠ 0#k) ×ˢ (Finset.univ : Finset Bool)).card := by
    refine Finset.card_bij' (fun p _ => (p.1, decide (p.2 = 0#k)))
      (fun q _ => (q.1, if q.2 then 0#k else q.1)) ?_ ?_ ?_ ?_
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        and_true] at hp ⊢
      exact hp.1
    · rintro ⟨a, c⟩ hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        and_true] at hq ⊢
      cases c <;> simp [hq]
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      by_cases hb : b = 0#k
      · simp [hb]
      · have hab := hp.2.resolve_left hb
        simp [hb, hab]
    · rintro ⟨a, c⟩ hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        and_true] at hq
      cases c <;> simp [hq]
  rw [h, Finset.card_product, card_ne_zero_bitVec, Finset.card_univ, Fintype.card_bool]
  ring

/-- Pairs with a nonzero second term and a zero first term or equal terms. -/
private theorem card_right_ne_zero_left_zero_or_eq (k : ℕ) :
    (Finset.univ.filter fun p : BitVec k × BitVec k =>
      p.2 ≠ 0#k ∧ (p.1 = 0#k ∨ p.1 = p.2)).card = 2 * (2 ^ k - 1) := by
  rw [← card_left_ne_zero_right_zero_or_eq k]
  refine Finset.card_bij' (fun p _ => p.swap) (fun p _ => p.swap) ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap_prod_mk] at hp ⊢
    rcases hp.2 with h | h
    · exact ⟨hp.1, Or.inl h⟩
    · exact ⟨hp.1, Or.inr h.symm⟩
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.swap_prod_mk] at hp ⊢
    rcases hp.2 with h | h
    · exact ⟨hp.1, Or.inl h⟩
    · exact ⟨hp.1, Or.inr h.symm⟩
  · rintro ⟨a, b⟩ _
    rfl
  · rintro ⟨a, b⟩ _
    rfl

/-- Distinct pairs with a zero term. -/
private theorem card_ne_and_zero (k : ℕ) :
    (Finset.univ.filter fun p : BitVec k × BitVec k =>
      p.1 ≠ p.2 ∧ (p.1 = 0#k ∨ p.2 = 0#k)).card = 2 * (2 ^ k - 1) := by
  have h : (Finset.univ.filter fun p : BitVec k × BitVec k =>
      p.1 ≠ p.2 ∧ (p.1 = 0#k ∨ p.2 = 0#k)).card =
      ((Finset.univ.filter fun x : BitVec k => x ≠ 0#k) ×ˢ (Finset.univ : Finset Bool)).card := by
    refine Finset.card_bij' (fun p _ => (if p.1 = 0#k then p.2 else p.1, decide (p.1 = 0#k)))
      (fun q _ => if q.2 then (0#k, q.1) else (q.1, 0#k)) ?_ ?_ ?_ ?_
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        and_true] at hp ⊢
      by_cases ha : a = 0#k
      · simp only [ha, ite_true]
        exact fun hb => hp.1 (by rw [ha, hb])
      · simp [ha]
    · rintro ⟨a, c⟩ hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        and_true] at hq
      cases c
      · simp [hq]
      · simpa using Ne.symm hq
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      by_cases ha : a = 0#k
      · simp [ha]
      · have hb : b = 0#k := hp.2.resolve_left ha
        simp [ha, hb]
    · rintro ⟨a, c⟩ hq
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
        and_true] at hq
      cases c <;> simp [hq]
  rw [h, Finset.card_product, card_ne_zero_bitVec, Finset.card_univ, Fintype.card_bool]
  ring

/-- Distinct pairs of count `0`: the pairs of `zeroCount` and the distinct pairs with a
zero term. -/
private theorem card_ne_and_count_zero (k : ℕ) :
    (Finset.univ.filter fun p : BitVec k × BitVec k =>
      p.1 ≠ p.2 ∧ alignedPairCount k p.1 p.2 = 0).card = zeroCount k + 2 * (2 ^ k - 1) := by
  rw [← card_ne_and_zero k]
  unfold zeroCount
  simp only [Finset.card_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hz : p.1 = 0#k ∨ p.2 = 0#k → alignedPairCount k p.1 p.2 = 0 := by
    rintro (h | h)
    · rw [h, alignedPairCount_zero_left]
    · rw [h, alignedPairCount_zero_right]
  unfold zeroPred
  by_cases ha : p.1 = 0#k <;> by_cases hb : p.2 = 0#k <;> by_cases hab : p.1 = p.2 <;>
    by_cases hN : alignedPairCount k p.1 p.2 = 0 <;> simp_all

/-- The pairs of level `k + 1` with count `2 ^ k - 4`, for two indices in different
halves, are the pairs of `zeroCount` of the low parts. -/
private theorem card_mixed_top (k : ℕ) (hk : 3 ≤ k) {I J : Bool} (hIJ : I ≠ J) :
    (Finset.univ.filter fun p : BitVec k × BitVec k =>
      alignedPairCount (k + 1) (BitVec.cons I p.1) (BitVec.cons J p.2) = 2 ^ k - 4).card =
      zeroCount k := by
  unfold zeroCount
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  rw [alignedPairCount_cons_mixed_eq_top_iff hk hIJ]
  rfl

/-- The pairs of level `k + 1` in the same half have count at most `2 ^ k - 8`. -/
private theorem card_same_top (k : ℕ) (hk : 3 ≤ k) (I : Bool) :
    (Finset.univ.filter fun p : BitVec k × BitVec k =>
      alignedPairCount (k + 1) (BitVec.cons I p.1) (BitVec.cons I p.2) = 2 ^ k - 4).card = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro p _ h
  rw [alignedPairCount_cons_same] at h
  have h4 := alignedPairCount_add_four_le_of_three_le hk p.1 p.2
  have hp := two_pow_eq_two_mul_pred (k := k) (by omega)
  have h4' := four_le_two_pow_sub_one hk
  omega

/-- **Top of the spectrum.** For `k ≥ 3`, the ordered pairs of level `k + 1` with the
largest count `2 ^ k - 4` number twice `zeroCount k`. -/
theorem alignedPairCountMultiplicity_succ_top {k : ℕ} (hk : 3 ≤ k) :
    alignedPairCountMultiplicity (k + 1) (2 ^ k - 4) = 2 * zeroCount k := by
  unfold alignedPairCountMultiplicity
  rw [card_filter_prod_cons (fun p : BitVec (k + 1) × BitVec (k + 1) =>
    alignedPairCount (k + 1) p.1 p.2 = 2 ^ k - 4)]
  simp only []
  rw [card_same_top k hk true, card_same_top k hk false,
    card_mixed_top k hk (by decide : true ≠ false), card_mixed_top k hk (by decide : false ≠ true)]
  omega

/-- Indices with equal top bits are distinct exactly when the low parts are. -/
private theorem cons_same_ne_iff {k : ℕ} (I : Bool) (a b : BitVec k) :
    BitVec.cons I a ≠ BitVec.cons I b ↔ a ≠ b :=
  (cons_same_eq_iff I a b).not

/-- Same half, top bit set: the pairs of `zeroCount` and the distinct pairs with a zero term. -/
private theorem card_zero_true (k : ℕ) :
    (Finset.univ.filter fun p : BitVec k × BitVec k =>
      zeroPred (k + 1) (BitVec.cons true p.1, BitVec.cons true p.2)).card =
      zeroCount k + 2 * (2 ^ k - 1) := by
  rw [← card_ne_and_count_zero]
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  simp only [zeroPred, alignedPairCount_cons_same, cons_same_ne_iff]
  constructor
  · rintro ⟨-, -, h3, h4⟩
    exact ⟨h3, by omega⟩
  · rintro ⟨h3, h4⟩
    exact ⟨cons_true_ne_zero _, cons_true_ne_zero _, h3, by omega⟩

/-- Same half, top bit clear: the pairs of `zeroCount` of the low parts. -/
private theorem card_zero_false (k : ℕ) :
    (Finset.univ.filter fun p : BitVec k × BitVec k =>
      zeroPred (k + 1) (BitVec.cons false p.1, BitVec.cons false p.2)).card =
      zeroCount k := by
  unfold zeroCount
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  simp only [zeroPred, alignedPairCount_cons_same, cons_same_ne_iff, cons_false_ne_zero_iff]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, by omega⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, h3, by omega⟩

/-- First index in the first half, second in the second: the degenerate low parts. -/
private theorem card_zero_false_true {k : ℕ} (hk : 3 ≤ k) :
    (Finset.univ.filter fun p : BitVec k × BitVec k =>
      zeroPred (k + 1) (BitVec.cons false p.1, BitVec.cons true p.2)).card =
      2 * (2 ^ k - 1) := by
  rw [← card_left_ne_zero_right_zero_or_eq k]
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  have hm := alignedPairCount_cons_mixed_eq_zero_iff hk (I := false) (J := true) (by decide)
    p.1 p.2
  have hne := cons_ne_cons_of_ne (I := false) (J := true) (by decide) p.1 p.2
  simp only [zeroPred, hm, cons_false_ne_zero_iff]
  constructor
  · rintro ⟨h1, -, -, h4⟩
    exact ⟨h1, h4.resolve_left h1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, cons_true_ne_zero _, hne, Or.inr h2⟩

/-- First index in the second half, second in the first: the degenerate low parts. -/
private theorem card_zero_true_false {k : ℕ} (hk : 3 ≤ k) :
    (Finset.univ.filter fun p : BitVec k × BitVec k =>
      zeroPred (k + 1) (BitVec.cons true p.1, BitVec.cons false p.2)).card =
      2 * (2 ^ k - 1) := by
  rw [← card_right_ne_zero_left_zero_or_eq k]
  congr 1
  refine Finset.filter_congr fun p _ => ?_
  have hm := alignedPairCount_cons_mixed_eq_zero_iff hk (I := true) (J := false) (by decide)
    p.1 p.2
  have hne := cons_ne_cons_of_ne (I := true) (J := false) (by decide) p.1 p.2
  simp only [zeroPred, hm, cons_false_ne_zero_iff]
  constructor
  · rintro ⟨-, h2, -, h4⟩
    refine ⟨h2, ?_⟩
    rcases h4 with h | h | h
    · exact Or.inl h
    · exact absurd h h2
    · exact Or.inr h
  · rintro ⟨h2, h⟩
    refine ⟨cons_true_ne_zero _, h2, hne, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-- **Recurrence of the zero count.** For `k ≥ 3`,
`zeroCount (k + 1) = 2 * zeroCount k + 6 * (2 ^ k - 1)`. -/
theorem zeroCount_succ {k : ℕ} (hk : 3 ≤ k) :
    zeroCount (k + 1) = 2 * zeroCount k + 6 * (2 ^ k - 1) := by
  have h := card_filter_prod_cons (k := k) (zeroPred (k + 1))
  have e : zeroCount (k + 1) = (Finset.univ.filter (zeroPred (k + 1))).card := rfl
  rw [e, h, card_zero_true, card_zero_false, card_zero_true_false hk, card_zero_false_true hk]
  omega

/-- The zero count at level `3`, by kernel evaluation of the `64` ordered pairs. -/
theorem zeroCount_three : zeroCount 3 = 42 := by decide +kernel

theorem zeroCount_four : zeroCount 4 = 126 := by
  have h := zeroCount_succ (k := 3) (by norm_num)
  rw [zeroCount_three] at h
  norm_num at h
  exact h

theorem zeroCount_five : zeroCount 5 = 342 := by
  have h := zeroCount_succ (k := 4) (by norm_num)
  rw [zeroCount_four] at h
  norm_num at h
  exact h

theorem zeroCount_six : zeroCount 6 = 870 := by
  have h := zeroCount_succ (k := 5) (by norm_num)
  rw [zeroCount_five] at h
  norm_num at h
  exact h

theorem alignedPairCountMultiplicity_four_four : alignedPairCountMultiplicity 4 4 = 84 := by
  have h := alignedPairCountMultiplicity_succ_top (k := 3) (by norm_num)
  rw [zeroCount_three] at h
  norm_num at h
  exact h

theorem alignedPairCountMultiplicity_five_twelve :
    alignedPairCountMultiplicity 5 12 = 252 := by
  have h := alignedPairCountMultiplicity_succ_top (k := 4) (by norm_num)
  rw [zeroCount_four] at h
  norm_num at h
  exact h

theorem alignedPairCountMultiplicity_six_twentyEight :
    alignedPairCountMultiplicity 6 28 = 684 := by
  have h := alignedPairCountMultiplicity_succ_top (k := 5) (by norm_num)
  rw [zeroCount_five] at h
  norm_num at h
  exact h

theorem alignedPairCountMultiplicity_seven_sixty :
    alignedPairCountMultiplicity 7 60 = 1740 := by
  have h := alignedPairCountMultiplicity_succ_top (k := 6) (by norm_num)
  rw [zeroCount_six] at h
  norm_num at h
  exact h

end Tower

end CayleyDickson
