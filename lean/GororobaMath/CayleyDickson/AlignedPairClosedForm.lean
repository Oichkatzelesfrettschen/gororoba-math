/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TwoTermRecursion

/-!
# A closed form of the aligned-pair count

The indices are bit vectors with the top bit outermost and bit `s` read by
`BitVec.getLsbD s` (bit `k - 1` is the top bit of level `k`); the signs are
`Tower.negSign`, the convention of `cd_core.cd_sign`. For `i j : BitVec k`
and a bit position `p < k`, the *split at `p`* separates bit `p` from the
bits below it: it is the step of the doubling recursion
(`Tower.alignedPairCount_succ_cases`) from the low `p` bits to the low
`p + 1` bits. The split is *degenerate* (`Tower.DegenerateSplit`) when bit
`p` of `i` and of `j` differ and the parts below bit `p` satisfy
`a = 0`, `b = 0` or `a = b`, the middle case of the recursion, which
resets the count to `0`.

Let `m' = i ^^^ j` with bit `p` and every bit below it cleared, for the
highest degenerate split `p`, and `m' = i ^^^ j` when no split is
degenerate (`Tower.clearedXorBit` is bit `s` of `m'`). The bit of the
degenerate split itself is cleared. With `parity t` the parity of the
number of set bits of `m'` at positions `t` to `k - 1` (that is, of
`m' >>> t`),

  `alignedPairCount k i j = 4 * ∑ t ∈ [3, k), 2 ^ (k - 1 - t) * parity t`

(`Tower.alignedPairCount_eq_closedForm`). The proof is an induction on
`k` through the three cases of the recursion: the same-half case doubles
both sides, the degenerate mixed case clears every bit of `m'`, and the
nondegenerate mixed case complements every parity below the top bit.

## Main results

* `Tower.alignedPairCount_eq_closedForm`: the closed form at every level
  and for all indices, `i = j` included (both sides `0`).
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

/-- The split of `(i, j)` at bit `p` is degenerate: bit `p` of `i` and of
`j` differ, and below bit `p` the index `i` is zero, `j` is zero, or the
two agree. -/
def DegenerateSplit {k : ℕ} (i j : BitVec k) (p : ℕ) : Prop :=
  i.getLsbD p ≠ j.getLsbD p ∧
    ((∀ s < p, i.getLsbD s = false) ∨ (∀ s < p, j.getLsbD s = false) ∨
      ∀ s < p, i.getLsbD s = j.getLsbD s)

instance {k : ℕ} (i j : BitVec k) : DecidablePred (DegenerateSplit i j) := fun p => by
  unfold DegenerateSplit
  infer_instance

/-- Bit `s` of `m'`: bit `s` of `i ^^^ j`, kept when every degenerate split
lies below position `s`. -/
def clearedXorBit {k : ℕ} (i j : BitVec k) (s : ℕ) : Bool :=
  (i.getLsbD s ^^ j.getLsbD s) && decide (∀ p < k, DegenerateSplit i j p → p < s)

/-- The parity of the set bits of `m'` at positions `t` to `k - 1`. -/
def clearedXorParity {k : ℕ} (i j : BitVec k) (t : ℕ) : ℕ :=
  (∑ s ∈ Finset.Ico t k, (clearedXorBit i j s).toNat) % 2

/-- The closed form `4 * ∑ t ∈ [3, k), 2 ^ (k - 1 - t) * parity t`. -/
def closedForm (k : ℕ) (i j : BitVec k) : ℕ :=
  4 * ∑ t ∈ Finset.Ico 3 k, 2 ^ (k - 1 - t) * clearedXorParity i j t

theorem getLsbD_cons_of_lt {k : ℕ} (I : Bool) (a : BitVec k) {s : ℕ} (hs : s < k) :
    (BitVec.cons I a).getLsbD s = a.getLsbD s := by
  simp [BitVec.getLsbD_cons, show s ≠ k by omega]

theorem getLsbD_cons_self {k : ℕ} (I : Bool) (a : BitVec k) :
    (BitVec.cons I a).getLsbD k = I := by
  rw [BitVec.getLsbD_cons]
  simp

theorem eq_zero_iff_getLsbD {k : ℕ} (a : BitVec k) : a = 0#k ↔ ∀ s < k, a.getLsbD s = false := by
  constructor
  · rintro rfl s _
    simp
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro s hs
    rw [h s hs, BitVec.getLsbD_zero]

theorem eq_iff_getLsbD {k : ℕ} (a b : BitVec k) : a = b ↔ ∀ s < k, a.getLsbD s = b.getLsbD s :=
  ⟨by rintro rfl s _; rfl, BitVec.eq_of_getLsbD_eq⟩

theorem not_degenerateSplit_of_le {k : ℕ} (i j : BitVec k) {p : ℕ} (hp : k ≤ p) :
    ¬DegenerateSplit i j p := by
  rintro ⟨h, -⟩
  rw [BitVec.getLsbD_of_ge i p hp, BitVec.getLsbD_of_ge j p hp] at h
  exact h rfl

theorem degenerateSplit_cons_of_lt {k : ℕ} (I J : Bool) (a b : BitVec k) {p : ℕ} (hp : p < k) :
    DegenerateSplit (BitVec.cons I a) (BitVec.cons J b) p ↔ DegenerateSplit a b p := by
  have e1 : (∀ s < p, (BitVec.cons I a).getLsbD s = false) ↔ ∀ s < p, a.getLsbD s = false :=
    forall₂_congr fun s hs => by rw [getLsbD_cons_of_lt I a (by omega)]
  have e2 : (∀ s < p, (BitVec.cons J b).getLsbD s = false) ↔ ∀ s < p, b.getLsbD s = false :=
    forall₂_congr fun s hs => by rw [getLsbD_cons_of_lt J b (by omega)]
  have e3 : (∀ s < p, (BitVec.cons I a).getLsbD s = (BitVec.cons J b).getLsbD s) ↔
      ∀ s < p, a.getLsbD s = b.getLsbD s :=
    forall₂_congr fun s hs => by
      rw [getLsbD_cons_of_lt I a (by omega), getLsbD_cons_of_lt J b (by omega)]
  unfold DegenerateSplit
  rw [getLsbD_cons_of_lt I a hp, getLsbD_cons_of_lt J b hp, e1, e2, e3]

theorem degenerateSplit_cons_self {k : ℕ} (I J : Bool) (a b : BitVec k) :
    DegenerateSplit (BitVec.cons I a) (BitVec.cons J b) k ↔
      I ≠ J ∧ (a = 0#k ∨ b = 0#k ∨ a = b) := by
  have e1 : (∀ s < k, (BitVec.cons I a).getLsbD s = false) ↔ a = 0#k := by
    rw [eq_zero_iff_getLsbD]
    exact forall₂_congr fun s hs => by rw [getLsbD_cons_of_lt I a hs]
  have e2 : (∀ s < k, (BitVec.cons J b).getLsbD s = false) ↔ b = 0#k := by
    rw [eq_zero_iff_getLsbD]
    exact forall₂_congr fun s hs => by rw [getLsbD_cons_of_lt J b hs]
  have e3 : (∀ s < k, (BitVec.cons I a).getLsbD s = (BitVec.cons J b).getLsbD s) ↔ a = b := by
    rw [eq_iff_getLsbD]
    exact forall₂_congr fun s hs => by rw [getLsbD_cons_of_lt I a hs, getLsbD_cons_of_lt J b hs]
  unfold DegenerateSplit
  rw [getLsbD_cons_self, getLsbD_cons_self, e1, e2, e3]

/-- A degenerate top split clears every bit of `m'` at level `k + 1`. -/
theorem clearedXorBit_cons_of_degenerate {k : ℕ} {I J : Bool} {a b : BitVec k}
    (hd : DegenerateSplit (BitVec.cons I a) (BitVec.cons J b) k) {s : ℕ} (hs : s ≤ k) :
    clearedXorBit (BitVec.cons I a) (BitVec.cons J b) s = false := by
  unfold clearedXorBit
  have : ¬∀ p < k + 1, DegenerateSplit (BitVec.cons I a) (BitVec.cons J b) p → p < s :=
    fun h => absurd (h k (by omega) hd) (by omega)
  rw [decide_eq_false this, Bool.and_false]

/-- Below a nondegenerate top split, `m'` keeps the bits of level `k`. -/
theorem clearedXorBit_cons_of_lt {k : ℕ} {I J : Bool} {a b : BitVec k}
    (hd : ¬DegenerateSplit (BitVec.cons I a) (BitVec.cons J b) k) {s : ℕ} (hs : s < k) :
    clearedXorBit (BitVec.cons I a) (BitVec.cons J b) s = clearedXorBit a b s := by
  unfold clearedXorBit
  rw [getLsbD_cons_of_lt I a hs, getLsbD_cons_of_lt J b hs]
  congr 1
  rw [decide_eq_decide]
  constructor
  · intro h p hp hdp
    exact h p (by omega) ((degenerateSplit_cons_of_lt I J a b hp).2 hdp)
  · intro h p hp hdp
    rcases Nat.lt_or_ge p k with hpk | hpk
    · exact h p hpk ((degenerateSplit_cons_of_lt I J a b hpk).1 hdp)
    · have : p = k := by omega
      subst this
      exact absurd hdp hd

/-- At a nondegenerate top split, the top bit of `m'` is `I ^^ J`. -/
theorem clearedXorBit_cons_self {k : ℕ} {I J : Bool} {a b : BitVec k}
    (hd : ¬DegenerateSplit (BitVec.cons I a) (BitVec.cons J b) k) :
    clearedXorBit (BitVec.cons I a) (BitVec.cons J b) k = (I ^^ J) := by
  unfold clearedXorBit
  rw [getLsbD_cons_self, getLsbD_cons_self]
  have : ∀ p < k + 1, DegenerateSplit (BitVec.cons I a) (BitVec.cons J b) p → p < k := by
    intro p hp hdp
    rcases Nat.lt_or_ge p k with hpk | hpk
    · exact hpk
    · have : p = k := by omega
      subst this
      exact absurd hdp hd
  rw [decide_eq_true this, Bool.and_true]

/-- The sum of the bits of `m'` from position `t` at level `k + 1`, below a
nondegenerate top split. -/
theorem sum_clearedXorBit_cons {k : ℕ} {I J : Bool} {a b : BitVec k}
    (hd : ¬DegenerateSplit (BitVec.cons I a) (BitVec.cons J b) k) {t : ℕ} (ht : t ≤ k) :
    ∑ s ∈ Finset.Ico t (k + 1), (clearedXorBit (BitVec.cons I a) (BitVec.cons J b) s).toNat =
      ∑ s ∈ Finset.Ico t k, (clearedXorBit a b s).toNat + (I ^^ J).toNat := by
  rw [Finset.sum_Ico_succ_top ht, clearedXorBit_cons_self hd]
  congr 1
  exact Finset.sum_congr rfl fun s hs => by
    rw [clearedXorBit_cons_of_lt hd (Finset.mem_Ico.1 hs).2]

theorem closedForm_eq_zero_of_le_three {k : ℕ} (hk : k ≤ 3) (i j : BitVec k) :
    closedForm k i j = 0 := by
  unfold closedForm
  rw [Finset.Ico_eq_empty (by omega), Finset.sum_empty, mul_zero]

/-- A degenerate top split gives the closed form `0`. -/
theorem closedForm_cons_of_degenerate {k : ℕ} {I J : Bool} {a b : BitVec k}
    (hd : DegenerateSplit (BitVec.cons I a) (BitVec.cons J b) k) :
    closedForm (k + 1) (BitVec.cons I a) (BitVec.cons J b) = 0 := by
  unfold closedForm clearedXorParity
  rw [Finset.sum_eq_zero, mul_zero]
  intro t ht
  rw [Finset.sum_eq_zero, Nat.zero_mod, mul_zero]
  intro s hs
  rw [clearedXorBit_cons_of_degenerate hd (by simp at hs; omega)]
  rfl

theorem two_pow_sub_succ {k t : ℕ} (ht : t < k) : 2 ^ (k - t) = 2 * 2 ^ (k - 1 - t) := by
  rw [← pow_succ']
  congr 1
  omega

/-- The same-half step doubles the closed form. -/
theorem closedForm_cons_same {k : ℕ} (I : Bool) (a b : BitVec k) :
    closedForm (k + 1) (BitVec.cons I a) (BitVec.cons I b) = 2 * closedForm k a b := by
  have hd : ¬DegenerateSplit (BitVec.cons I a) (BitVec.cons I b) k := by
    rw [degenerateSplit_cons_self]
    exact fun h => h.1 rfl
  have hp : ∀ t ≤ k, clearedXorParity (BitVec.cons I a) (BitVec.cons I b) t =
      clearedXorParity a b t := by
    intro t ht
    unfold clearedXorParity
    rw [sum_clearedXorBit_cons hd ht]
    simp
  rcases Nat.lt_or_ge k 3 with hk | hk
  · rw [closedForm_eq_zero_of_le_three (by omega), closedForm_eq_zero_of_le_three (by omega)]
  · unfold closedForm
    rw [Finset.sum_Ico_succ_top hk, hp k le_rfl]
    have hk0 : clearedXorParity a b k = 0 := by
      simp [clearedXorParity]
    rw [hk0, mul_zero, add_zero, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' := Finset.mem_Ico.1 ht
    rw [hp t (by omega), Nat.add_sub_cancel, two_pow_sub_succ ht'.2]
    ring

/-- `∑ t ∈ [3, k), 2 ^ (k - t) + 2 = 2 ^ (k - 2)` for `k ≥ 3`. -/
theorem sum_Ico_two_pow {k : ℕ} (hk : 3 ≤ k) :
    ∑ t ∈ Finset.Ico 3 k, 2 ^ (k - t) + 2 = 2 ^ (k - 2) := by
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top hk, show k + 1 - k = 1 by omega, pow_one]
    have : ∑ t ∈ Finset.Ico 3 k, 2 ^ (k + 1 - t) = 2 * ∑ t ∈ Finset.Ico 3 k, 2 ^ (k - t) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [← pow_succ']
      congr 1
      have := (Finset.mem_Ico.1 ht).2
      omega
    rw [this, show k + 1 - 2 = (k - 2) + 1 by omega, pow_succ]
    omega

/-- The nondegenerate mixed step: `F (k + 1) + 2 F k + 4 = 2 ^ k`. -/
theorem closedForm_cons_mixed_add {k : ℕ} (hk : 3 ≤ k) {I J : Bool} (hIJ : I ≠ J)
    {a b : BitVec k} (hd : ¬DegenerateSplit (BitVec.cons I a) (BitVec.cons J b) k) :
    closedForm (k + 1) (BitVec.cons I a) (BitVec.cons J b) + 2 * closedForm k a b + 4 =
      2 ^ k := by
  have hx : (I ^^ J).toNat = 1 := by cases I <;> cases J <;> simp_all
  have hp : ∀ t ≤ k, clearedXorParity (BitVec.cons I a) (BitVec.cons J b) t +
      clearedXorParity a b t = 1 := by
    intro t ht
    unfold clearedXorParity
    rw [sum_clearedXorBit_cons hd ht, hx]
    omega
  have hg := sum_Ico_two_pow hk
  unfold closedForm
  rw [Finset.sum_Ico_succ_top hk, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
  have hk1 : clearedXorParity (BitVec.cons I a) (BitVec.cons J b) k = 1 := by
    have := hp k le_rfl
    have h0 : clearedXorParity a b k = 0 := by simp [clearedXorParity]
    omega
  rw [hk1]
  have hsum : ∑ t ∈ Finset.Ico 3 k,
      2 ^ (k - t) * clearedXorParity (BitVec.cons I a) (BitVec.cons J b) t +
        2 * ∑ t ∈ Finset.Ico 3 k, 2 ^ (k - 1 - t) * clearedXorParity a b t =
      ∑ t ∈ Finset.Ico 3 k, 2 ^ (k - t) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht' := Finset.mem_Ico.1 ht
    have h1 := hp t (by omega)
    rw [two_pow_sub_succ ht'.2]
    calc 2 * 2 ^ (k - 1 - t) * clearedXorParity (BitVec.cons I a) (BitVec.cons J b) t +
          2 * (2 ^ (k - 1 - t) * clearedXorParity a b t) =
        2 * 2 ^ (k - 1 - t) * (clearedXorParity (BitVec.cons I a) (BitVec.cons J b) t +
          clearedXorParity a b t) := by ring
      _ = 2 * 2 ^ (k - 1 - t) := by rw [h1, mul_one]
  have h4 : 2 ^ k = 4 * 2 ^ (k - 2) := by
    conv_lhs => rw [show k = (k - 2) + 2 by omega]
    rw [pow_add]
    ring
  omega

/-- **Closed form of the aligned-pair count.** At every level and for all
indices, `alignedPairCount k i j` is `4 * ∑ t ∈ [3, k), 2 ^ (k - 1 - t) * parity t`,
with `parity t` the parity of `m' >>> t` and `m'` the exclusive or of the
indices with every bit at or below the highest degenerate split cleared. -/
theorem alignedPairCount_eq_closedForm : ∀ (k : ℕ) (i j : BitVec k),
    alignedPairCount k i j = closedForm k i j
  | 0, i, j => by
    rw [alignedPairCount_eq_zero_of_le_three (k := 0) (by omega),
      closedForm_eq_zero_of_le_three (k := 0) (by omega)]
  | k + 1, i, j => by
    obtain ⟨I, a, rfl⟩ : ∃ I a, i = BitVec.cons I a := ⟨_, _, (BitVec.cons_msb_setWidth i).symm⟩
    obtain ⟨J, b, rfl⟩ : ∃ J b, j = BitVec.cons J b := ⟨_, _, (BitVec.cons_msb_setWidth j).symm⟩
    have ih := alignedPairCount_eq_closedForm k a b
    rcases Nat.lt_or_ge k 3 with hk | hk
    · rw [alignedPairCount_eq_zero_of_le_three (k := k + 1) (by omega),
        closedForm_eq_zero_of_le_three (k := k + 1) (by omega)]
    by_cases hIJ : I = J
    · subst hIJ
      rw [alignedPairCount_succ_of_msb_eq (i := BitVec.cons I a) (j := BitVec.cons I b) (by simp),
        BitVec.setWidth_cons, BitVec.setWidth_cons, closedForm_cons_same, ih]
    · have hmsb : (BitVec.cons I a).msb ≠ (BitVec.cons J b).msb := by simpa using hIJ
      by_cases hd : DegenerateSplit (BitVec.cons I a) (BitVec.cons J b) k
      · rw [closedForm_cons_of_degenerate hd]
        have h := ((degenerateSplit_cons_self I J a b).1 hd).2
        exact alignedPairCount_succ_eq_zero hmsb (by simpa only [BitVec.setWidth_cons] using h)
      · have hnd : ¬(a = 0#k ∨ b = 0#k ∨ a = b) := fun h =>
          hd ((degenerateSplit_cons_self I J a b).2 ⟨hIJ, h⟩)
        simp only [not_or] at hnd
        have hN := alignedPairCount_succ_add hmsb (by rw [BitVec.setWidth_cons]; exact hnd.1)
          (by rw [BitVec.setWidth_cons]; exact hnd.2.1)
          (by rw [BitVec.setWidth_cons, BitVec.setWidth_cons]; exact hnd.2.2)
        rw [BitVec.setWidth_cons, BitVec.setWidth_cons] at hN
        have hF := closedForm_cons_mixed_add hk hIJ hd
        omega

end Tower

end CayleyDickson
