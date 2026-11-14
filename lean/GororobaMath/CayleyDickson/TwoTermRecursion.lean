/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TwoTermNullity

/-!
# The doubling recursion of the aligned-pair count

`alignedPairCount k i j` is the nullity of left multiplication by
`e i + e j` on the `2 ^ k`-dimensional level of the tower over every
nontrivial commutative ring with the identity as star in which `2` is a
non-zero-divisor (`Tower.finrank_ker_mulLeft_e_add_e`). The indices are bit
vectors with the top bit outermost and the signs are `Tower.negSign`, the
convention of `cd_core.cd_sign`. The count obeys a recursion on the top bit
of the indices. For `i j : BitVec (k + 1)` with low parts
`a = i.setWidth k` and `b = j.setWidth k`, and `N = alignedPairCount`:

* `i` and `j` in the same half (`i.msb = j.msb`):
  `N (k + 1) i j = 2 * N k a b`;
* `i` and `j` in different halves with `a = 0`, `b = 0` or `a = b`:
  `N (k + 1) i j = 0`;
* `i` and `j` in different halves otherwise:
  `N (k + 1) i j + 2 * N k a b + 4 = 2 ^ k`.

The pair `{x, x'}`, `x' = partner i j x`, is aligned exactly when the signs
of `e i * e x`, `e i * e x'`, `e j * e x` and `e j * e x'` multiply to `+1`
(`Tower.misaligned` is `true` when they multiply to `-1`).
`Tower.negSign_cons` writes each sign of level `k + 1` as the level-`k` sign
of the low parts with corrections from the top bits: a transposition of the
factors when the right index lies in the second half, and conjugation
signs when the left index does. For `i` and `j` in the same half the
corrections cancel at every index, so each half of the indices contributes
the level-`k` count of aligned indices. For `i` and `j` in different halves
every pair has one element in each half; at a low index outside
`{0, a, b, a ^^^ b}` the corrections multiply to `-1`, so the index is
aligned at level `k + 1` exactly when it is not aligned at level `k`, and
the four exceptional indices are aligned at neither level
(`Tower.negSign_xor_right`, `Tower.negSign_swap_xor`). When `a = 0`,
`b = 0` or `a = b`, no index is aligned.

Over the reals the recursion is the specialization, to sums of two standard
basis vectors, of results of Biss, Dugger and Isaksen, *Large annihilators
in Cayley-Dickson algebras* (arXiv:math/0511691): Theorem 10.1 there doubles
the annihilator of `(a, 0)` and of `(0, a)`, Proposition 11.1 gives the
annihilator of `(e a, e b)` the dimension of an anti-associator space, and
Lemmas 8.7 and 8.8 double the associator dimensions; Theorem 9.8 is the
divisibility by `4`, and Lemmas 9.4 and 9.5 the vanishing at `e 0` and at
the adjoined unit. The statements here are about the count, so they hold
over every ring of the first paragraph.

## Main results

* `Tower.alignedPairCount_succ_of_msb_eq`,
  `Tower.alignedPairCount_succ_eq_zero`, `Tower.alignedPairCount_succ_add`:
  the three cases of the recursion.
* `Tower.alignedPairCount_eq_zero_of_le_three`: no two-term operand has an
  aligned pair at a level `k ≤ 3`.
* `Tower.alignedPairCount_zero_left`, `Tower.alignedPairCount_zero_right`,
  `Tower.alignedPairCount_top_left`, `Tower.alignedPairCount_top_right`: an
  operand with the term `e 0 = 1`, or with the unit that the last doubling
  adjoins, has no aligned pair.
* `Tower.four_dvd_alignedPairCount`, `Tower.alignedPairCount_add_four_le`:
  every count is a multiple of `4`, and a nonzero count at level `k` is at
  most `2 ^ (k - 1) - 4`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

/-- `true` when the pair `{x, partner i j x}` of the operand `e i + e j` is
not aligned: the signs of `e i * e x`, `e i * e x'`, `e j * e x` and
`e j * e x'`, `x' = partner i j x`, multiply to `-1`. -/
def misaligned (k : ℕ) (i j x : BitVec k) : Bool :=
  negSign k i x ^^ negSign k i (partner i j x) ^^ negSign k j x ^^ negSign k j (partner i j x)

/-- A pair is aligned exactly when it is not misaligned. -/
theorem aligned_eq_not_misaligned (k : ℕ) (i j x : BitVec k) :
    (alignedAdd k i j x || alignedSub k i j x) = !misaligned k i j x := by
  unfold alignedAdd alignedSub misaligned
  cases negSign k i x <;> cases negSign k j (partner i j x) <;> cases negSign k j x <;>
    cases negSign k i (partner i j x) <;> rfl

theorem partner_comm {k : ℕ} (i j x : BitVec k) : partner i j x = partner j i x := by
  unfold partner
  rw [BitVec.xor_assoc, BitVec.xor_comm i j, ← BitVec.xor_assoc]

theorem partner_eq_iff {k : ℕ} (i j x z : BitVec k) : partner i j x = z ↔ x = partner i j z :=
  ⟨fun h => by rw [← h, partner_partner], fun h => by rw [h, partner_partner]⟩

@[simp] theorem partner_zero {k : ℕ} (i j : BitVec k) : partner i j 0#k = i ^^^ j := by
  simp [partner]

@[simp] theorem partner_self_left {k : ℕ} (i j : BitVec k) : partner i j i = j := by
  simp [partner]

@[simp] theorem partner_self_right {k : ℕ} (i j : BitVec k) : partner i j j = i := by
  unfold partner
  rw [BitVec.xor_comm j i, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

@[simp] theorem partner_xor {k : ℕ} (i j : BitVec k) : partner i j (i ^^^ j) = 0#k := by
  unfold partner
  rw [BitVec.xor_assoc, BitVec.xor_self]

theorem partner_cons {k : ℕ} (I J X : Bool) (a b y : BitVec k) :
    partner (BitVec.cons I a) (BitVec.cons J b) (BitVec.cons X y) =
      BitVec.cons (X ^^ I ^^ J) (partner a b y) := by
  simp [partner]

theorem self_eq_xor_left_iff {k : ℕ} (p q : BitVec k) : p = p ^^^ q ↔ q = 0#k :=
  eq_comm.trans (xor_eq_left_iff p q)

theorem self_eq_xor_right_iff {k : ℕ} (p q : BitVec k) : q = p ^^^ q ↔ p = 0#k := by
  rw [BitVec.xor_comm]
  exact self_eq_xor_left_iff q p

theorem xor_eq_right_iff {k : ℕ} (p q : BitVec k) : p ^^^ q = q ↔ p = 0#k :=
  eq_comm.trans (self_eq_xor_right_iff p q)

/-- The sign of `e k q * e k (p ^^^ q)` is that of `e k q * e k p`, reversed
when `q ≠ 0`. -/
theorem negSign_xor_left (k : ℕ) (p q : BitVec k) :
    negSign k q (p ^^^ q) = xor (decide (q ≠ 0#k)) (negSign k q p) := by
  rw [BitVec.xor_comm, negSign_xor_right]

theorem misaligned_comm (k : ℕ) (i j x : BitVec k) :
    misaligned k i j x = misaligned k j i x := by
  unfold misaligned
  rw [partner_comm j i]
  cases negSign k i x <;> cases negSign k j (partner i j x) <;> cases negSign k j x <;>
    cases negSign k i (partner i j x) <;> rfl

/-- Alignment is a property of the pair. -/
theorem misaligned_partner (k : ℕ) (i j x : BitVec k) :
    misaligned k i j (partner i j x) = misaligned k i j x := by
  unfold misaligned
  rw [partner_partner]
  cases negSign k i x <;> cases negSign k j (partner i j x) <;> cases negSign k j x <;>
    cases negSign k i (partner i j x) <;> rfl

/-- The number of indices whose pair under the operand `e i + e j` is
aligned. -/
def alignedCount (k : ℕ) (i j : BitVec k) : ℕ :=
  (Finset.univ.filter fun x => misaligned k i j x = false).card

/-- For `i ≠ j` every pair has two elements, so the aligned indices are
twice the aligned pairs. -/
theorem alignedCount_eq_two_mul {k : ℕ} {i j : BitVec k} (hij : i ≠ j) :
    alignedCount k i j = 2 * alignedPairCount k i j := by
  have hne : ∀ x, partner i j x ≠ x := fun x h => hij ((partner_eq_self_iff i j x).1 h)
  have hc := card_agree_eq_two_mul (δ := pairSign i j) (key := BitVec.toNat)
    (partner_partner i j) hne (fun _ _ h => BitVec.eq_of_toNat_eq h)
  have hf : alignedCount k i j =
      (Finset.univ.filter fun x => pairSign i j x = pairSign i j (partner i j x)).card := by
    unfold alignedCount
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← aligned_iff_pairSign, aligned_eq_not_misaligned]
    cases misaligned k i j x <;> simp
  have hg : (Finset.univ.filter fun x => (alignedAdd k i j x || alignedSub k i j x) = true).card =
      alignedCount k i j := by
    unfold alignedCount
    congr 1
    ext x
    simp [aligned_eq_not_misaligned]
  rw [alignedPairCount_eq_card hij, hg, hf, hc, Nat.mul_div_cancel_left _ two_pos]

/-- The aligned-pair count is symmetric in the two terms of the operand. -/
theorem alignedPairCount_comm (k : ℕ) (i j : BitVec k) :
    alignedPairCount k i j = alignedPairCount k j i := by
  by_cases hij : i = j
  · rw [hij]
  · have h1 := alignedCount_eq_two_mul hij
    have h2 := alignedCount_eq_two_mul (Ne.symm hij)
    have h3 : alignedCount k i j = alignedCount k j i := by
      simp only [alignedCount, misaligned_comm k i j]
    omega

/-- `BitVec (k + 1)` as a top bit and a low part. -/
def consEquiv (k : ℕ) : Bool × BitVec k ≃ BitVec (k + 1) where
  toFun q := BitVec.cons q.1 q.2
  invFun p := (p.msb, p.setWidth k)
  left_inv q := by simp
  right_inv p := BitVec.cons_msb_setWidth p

/-- A count over the indices of level `k + 1` is the sum of the counts over
its two halves. -/
theorem card_filter_cons {k : ℕ} (f : BitVec (k + 1) → Bool) :
    (Finset.univ.filter fun x => f x = false).card =
      (Finset.univ.filter fun y => f (BitVec.cons false y) = false).card +
        (Finset.univ.filter fun y => f (BitVec.cons true y) = false).card := by
  simp only [Finset.card_filter]
  rw [← (consEquiv k).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  rfl

/-- A count is invariant under the translation `y ↦ y ^^^ c`. -/
theorem card_filter_xor {k : ℕ} (c : BitVec k) (f : BitVec k → Bool) :
    (Finset.univ.filter fun y => f (y ^^^ c) = false).card =
      (Finset.univ.filter fun y => f y = false).card := by
  simp only [Finset.card_filter]
  let e : BitVec k ≃ BitVec k :=
    ⟨(· ^^^ c), (· ^^^ c), fun y => by simp,
      fun y => by simp⟩
  exact e.sum_comp (fun y => if f y = false then 1 else 0)

theorem card_bitVec (k : ℕ) : Fintype.card (BitVec k) = 2 ^ k := by
  rw [Fintype.card_congr
    (⟨BitVec.toFin, BitVec.ofFin, fun _ => rfl, fun _ => rfl⟩ : BitVec k ≃ Fin (2 ^ k)),
    Fintype.card_fin]

/-- The transposition corrections of the four signs of a pair cancel. -/
theorem transpose_corrections_cancel {k : ℕ} (a b y : BitVec k) :
    (decide (a ≠ 0#k ∧ y ≠ 0#k ∧ a ≠ y) ^^
        decide (a ≠ 0#k ∧ partner a b y ≠ 0#k ∧ a ≠ partner a b y)) =
      (decide (b ≠ 0#k ∧ y ≠ 0#k ∧ b ≠ y) ^^
        decide (b ≠ 0#k ∧ partner a b y ≠ 0#k ∧ b ≠ partner a b y)) := by
  have h0 : partner a b y = 0#k ↔ y = a ^^^ b := by rw [partner_eq_iff, partner_zero]
  have ha : a = partner a b y ↔ y = b := by rw [eq_comm, partner_eq_iff, partner_self_left]
  have hb : b = partner a b y ↔ y = a := by rw [eq_comm, partner_eq_iff, partner_self_right]
  have e1 : a ^^^ b = 0#k ↔ a = b := BitVec.xor_eq_zero_iff
  have e2 : a = a ^^^ b ↔ b = 0#k := self_eq_xor_left_iff a b
  have e3 : b = a ^^^ b ↔ a = 0#k := self_eq_xor_right_iff a b
  grind

/-- For `i` and `j` in the same half, the pair of an index is aligned at
level `k + 1` exactly when the pair of its low part is aligned at level
`k`. -/
theorem misaligned_cons_same {k : ℕ} (I X : Bool) (a b y : BitVec k) :
    misaligned (k + 1) (BitVec.cons I a) (BitVec.cons I b) (BitVec.cons X y) =
      misaligned k a b y := by
  have ht := transpose_corrections_cancel a b y
  unfold misaligned
  rw [partner_cons]
  simp only [negSign_cons]
  generalize negSign k a y = s1
  generalize negSign k a (partner a b y) = s2
  generalize negSign k b y = s3
  generalize negSign k b (partner a b y) = s4
  generalize decide (a ≠ 0#k ∧ y ≠ 0#k ∧ a ≠ y) = t1 at ht ⊢
  generalize decide (a ≠ 0#k ∧ partner a b y ≠ 0#k ∧ a ≠ partner a b y) = t2 at ht ⊢
  generalize decide (b ≠ 0#k ∧ y ≠ 0#k ∧ b ≠ y) = t3 at ht ⊢
  generalize decide (b ≠ 0#k ∧ partner a b y ≠ 0#k ∧ b ≠ partner a b y) = t4 at ht ⊢
  generalize decide (y ≠ 0#k) = d1
  generalize decide (partner a b y ≠ 0#k) = d2
  revert I X s1 s2 s3 s4 t1 t2 t3 t4 d1 d2
  decide

/-- For `i` in the first half and `j` in the second, with nonzero distinct
low parts `a` and `b`, a low index outside `{0, a, b, a ^^^ b}` is aligned
at level `k + 1` exactly when it is not aligned at level `k`. -/
theorem misaligned_cons_mixed {k : ℕ} {a b y : BitVec k} (ha : a ≠ 0#k) (hb : b ≠ 0#k)
    (hy0 : y ≠ 0#k) (hya : y ≠ a) (hyb : y ≠ b) (hyc : y ≠ a ^^^ b) :
    misaligned (k + 1) (BitVec.cons false a) (BitVec.cons true b) (BitVec.cons false y) =
      !misaligned k a b y := by
  have h1 : partner a b y ≠ 0#k := fun h => hyc (by rwa [partner_eq_iff, partner_zero] at h)
  have h2 : a ≠ partner a b y := fun h =>
    hyb (by rwa [eq_comm, partner_eq_iff, partner_self_left] at h)
  have h3 : b ≠ partner a b y := fun h =>
    hya (by rwa [eq_comm, partner_eq_iff, partner_self_right] at h)
  unfold misaligned
  rw [partner_cons]
  simp only [negSign_cons]
  simp only [ne_eq, ha, hb, hy0, h1, h2, h3, not_false_eq_true, and_self, decide_true,
    Bool.false_and, Bool.true_and, Bool.xor_false, Bool.xor_true, Bool.true_xor]
  generalize negSign k a y = s1
  generalize negSign k a (partner a b y) = s2
  generalize negSign k b y = s3
  generalize negSign k b (partner a b y) = s4
  revert s1 s2 s3 s4
  decide

/-- For nonzero distinct `a` and `b`, the four indices `0`, `a`, `b` and
`a ^^^ b` are aligned at neither level. -/
theorem misaligned_special {k : ℕ} {a b y : BitVec k} (ha : a ≠ 0#k) (hb : b ≠ 0#k)
    (hab : a ≠ b) (hy : y = 0#k ∨ y = a ∨ y = b ∨ y = a ^^^ b) :
    misaligned k a b y = true ∧
      misaligned (k + 1) (BitVec.cons false a) (BitVec.cons true b) (BitVec.cons false y) =
        true := by
  unfold misaligned
  rw [partner_cons]
  simp only [negSign_cons]
  rcases hy with h | h | h | h <;> rw [h] <;>
  · simp only [partner_zero, partner_self_left, partner_self_right, partner_xor,
      negSign_xor_right, negSign_xor_left, negSign_zero_right, negSign_self_eq,
      negSign_swap_xor k a b]
    simp only [ne_eq, ha, hb, hab, Ne.symm hab, BitVec.xor_eq_zero_iff, self_eq_xor_left_iff,
      self_eq_xor_right_iff, not_false_eq_true, not_true_eq_false, and_self, and_true,
      and_false, decide_true, decide_false]
    generalize negSign k a b = s
    revert s
    decide

/-- For `i` in the first half and `j` in the second, with low parts
`a = 0`, `b = 0` or `a = b`, no low index is aligned at level `k + 1`. -/
theorem misaligned_cons_degenerate {k : ℕ} {a b : BitVec k}
    (h : a = 0#k ∨ b = 0#k ∨ a = b) (y : BitVec k) :
    misaligned (k + 1) (BitVec.cons false a) (BitVec.cons true b) (BitVec.cons false y) =
      true := by
  unfold misaligned
  rw [partner_cons]
  simp only [negSign_cons]
  rcases h with rfl | rfl | rfl
  · have hp : partner 0#k b y = b ^^^ y := by simp [partner, BitVec.xor_comm]
    rw [hp, negSign_xor_right]
    simp only [negSign_zero_left, ne_eq, BitVec.xor_eq_zero_iff, self_eq_xor_left_iff]
    grind
  · have hp : partner a 0#k y = a ^^^ y := by simp [partner, BitVec.xor_comm]
    rw [hp, negSign_xor_right]
    simp only [negSign_zero_left, ne_eq, BitVec.xor_eq_zero_iff, self_eq_xor_left_iff]
    grind
  · rw [(partner_eq_self_iff a a y).2 rfl]
    generalize negSign k a y = s
    generalize decide (a ≠ 0#k ∧ y ≠ 0#k ∧ a ≠ y) = t
    generalize decide (y ≠ 0#k) = d
    revert s t d
    decide

/-- For `i` and `j` in the same half, each half of the indices contributes
the level-`k` count of aligned indices. -/
theorem alignedCount_cons_same {k : ℕ} (I : Bool) (a b : BitVec k) :
    alignedCount (k + 1) (BitVec.cons I a) (BitVec.cons I b) = 2 * alignedCount k a b := by
  unfold alignedCount
  rw [card_filter_cons]
  simp only [misaligned_cons_same]
  omega

/-- For `i` in the first half and `j` in the second, the partner map
exchanges the two halves, so the aligned indices are twice the aligned
low indices. -/
theorem alignedCount_cons_mixed {k : ℕ} (a b : BitVec k) :
    alignedCount (k + 1) (BitVec.cons false a) (BitVec.cons true b) =
      2 * (Finset.univ.filter fun y =>
        misaligned (k + 1) (BitVec.cons false a) (BitVec.cons true b)
          (BitVec.cons false y) = false).card := by
  have hx : ∀ y : BitVec k,
      misaligned (k + 1) (BitVec.cons false a) (BitVec.cons true b) (BitVec.cons true y) =
        misaligned (k + 1) (BitVec.cons false a) (BitVec.cons true b)
          (BitVec.cons false (y ^^^ (a ^^^ b))) := by
    intro y
    rw [← misaligned_partner (k + 1) _ _ (BitVec.cons true y), partner_cons]
    simp [partner, BitVec.xor_assoc]
  have hs := card_filter_xor (a ^^^ b) fun y =>
    misaligned (k + 1) (BitVec.cons false a) (BitVec.cons true b) (BitVec.cons false y)
  unfold alignedCount
  rw [card_filter_cons]
  simp only [hx]
  rw [hs]
  omega

/-- The level-`k + 1` count for `i` in the first half and `j` in the
second, with low parts `a = 0`, `b = 0` or `a = b`. -/
theorem alignedPairCount_false_true_eq_zero {k : ℕ} {a b : BitVec k}
    (h : a = 0#k ∨ b = 0#k ∨ a = b) :
    alignedPairCount (k + 1) (BitVec.cons false a) (BitVec.cons true b) = 0 := by
  have hij : BitVec.cons false a ≠ BitVec.cons true b := fun h => by
    simpa using congrArg BitVec.msb h
  have h1 := alignedCount_eq_two_mul hij
  rw [alignedCount_cons_mixed] at h1
  have h2 : (Finset.univ.filter fun y =>
      misaligned (k + 1) (BitVec.cons false a) (BitVec.cons true b)
        (BitVec.cons false y) = false).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y _
    rw [misaligned_cons_degenerate h y]
    simp
  omega

/-- The level-`k + 1` count for `i` in the first half and `j` in the
second, with nonzero distinct low parts `a` and `b`. -/
theorem alignedPairCount_false_true_add {k : ℕ} {a b : BitVec k} (ha : a ≠ 0#k)
    (hb : b ≠ 0#k) (hab : a ≠ b) :
    alignedPairCount (k + 1) (BitVec.cons false a) (BitVec.cons true b) +
      2 * alignedPairCount k a b + 4 = 2 ^ k := by
  have hij : BitVec.cons false a ≠ BitVec.cons true b := fun h => by
    simpa using congrArg BitVec.msb h
  have h1 := alignedCount_eq_two_mul hij
  rw [alignedCount_cons_mixed] at h1
  have h2 := alignedCount_eq_two_mul hab
  have hy : ∀ y : BitVec k,
      ((((((if misaligned k a b y = false then 1 else 0) +
        if misaligned (k + 1) (BitVec.cons false a) (BitVec.cons true b)
          (BitVec.cons false y) = false then 1 else 0) +
        if y = 0#k then 1 else 0) + if y = a then 1 else 0) + if y = b then 1 else 0) +
        if y = a ^^^ b then 1 else 0) = 1 := by
    intro y
    by_cases hs : y = 0#k ∨ y = a ∨ y = b ∨ y = a ^^^ b
    · obtain ⟨e1, e2⟩ := misaligned_special ha hb hab hs
      have hz : 0#k ≠ a ^^^ b := fun h => hab (BitVec.xor_eq_zero_iff.1 h.symm)
      rw [e1, e2]
      rcases hs with h | h | h | h <;> rw [h] <;>
        simp [ha, hb, hab, hz, Ne.symm ha, Ne.symm hb, Ne.symm hab, self_eq_xor_left_iff,
          self_eq_xor_right_iff]
    · simp only [not_or] at hs
      obtain ⟨h0, hya, hyb, hyc⟩ := hs
      rw [misaligned_cons_mixed ha hb h0 hya hyb hyc]
      cases misaligned k a b y <;> simp [h0, hya, hyb, hyc]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (BitVec k))) rfl
    fun y (_ : y ∈ Finset.univ) => hy y
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, card_bitVec, smul_eq_mul, mul_one] at hsum
  rw [← Finset.card_filter, ← Finset.card_filter] at hsum
  unfold alignedCount at h2
  omega

/-- For `i` and `j` in the same half, the aligned-pair count of level
`k + 1` is twice that of the low parts. -/
theorem alignedPairCount_succ_of_msb_eq {k : ℕ} {i j : BitVec (k + 1)} (h : i.msb = j.msb) :
    alignedPairCount (k + 1) i j = 2 * alignedPairCount k (i.setWidth k) (j.setWidth k) := by
  obtain ⟨I, a, rfl⟩ : ∃ I a, i = BitVec.cons I a := ⟨_, _, (BitVec.cons_msb_setWidth i).symm⟩
  obtain ⟨J, b, rfl⟩ : ∃ J b, j = BitVec.cons J b := ⟨_, _, (BitVec.cons_msb_setWidth j).symm⟩
  simp only [BitVec.msb_cons] at h
  subst h
  simp only [BitVec.setWidth_cons]
  by_cases hab : a = b
  · subst hab
    simp [alignedPairCount_self]
  · have hij : BitVec.cons I a ≠ BitVec.cons I b := fun h =>
      hab (by simpa using congrArg (BitVec.setWidth k) h)
    have h1 := alignedCount_eq_two_mul hij
    have h2 := alignedCount_eq_two_mul hab
    rw [alignedCount_cons_same] at h1
    omega

/-- For `i` and `j` in different halves with low parts `a = 0`, `b = 0` or
`a = b`, the operand has no aligned pair. -/
theorem alignedPairCount_succ_eq_zero {k : ℕ} {i j : BitVec (k + 1)} (h : i.msb ≠ j.msb)
    (hd : i.setWidth k = 0#k ∨ j.setWidth k = 0#k ∨ i.setWidth k = j.setWidth k) :
    alignedPairCount (k + 1) i j = 0 := by
  obtain ⟨I, a, rfl⟩ : ∃ I a, i = BitVec.cons I a := ⟨_, _, (BitVec.cons_msb_setWidth i).symm⟩
  obtain ⟨J, b, rfl⟩ : ∃ J b, j = BitVec.cons J b := ⟨_, _, (BitVec.cons_msb_setWidth j).symm⟩
  simp only [BitVec.msb_cons, BitVec.setWidth_cons] at h hd
  cases I <;> cases J
  · exact absurd rfl h
  · exact alignedPairCount_false_true_eq_zero hd
  · rw [alignedPairCount_comm]
    exact alignedPairCount_false_true_eq_zero (by rcases hd with hd | hd | hd <;> simp [hd])
  · exact absurd rfl h

/-- For `i` and `j` in different halves with nonzero distinct low parts
`a` and `b`, the aligned-pair counts of the two levels satisfy
`N (k + 1) i j + 2 * N k a b + 4 = 2 ^ k`. -/
theorem alignedPairCount_succ_add {k : ℕ} {i j : BitVec (k + 1)} (h : i.msb ≠ j.msb)
    (ha : i.setWidth k ≠ 0#k) (hb : j.setWidth k ≠ 0#k) (hab : i.setWidth k ≠ j.setWidth k) :
    alignedPairCount (k + 1) i j + 2 * alignedPairCount k (i.setWidth k) (j.setWidth k) + 4 =
      2 ^ k := by
  obtain ⟨I, a, rfl⟩ : ∃ I a, i = BitVec.cons I a := ⟨_, _, (BitVec.cons_msb_setWidth i).symm⟩
  obtain ⟨J, b, rfl⟩ : ∃ J b, j = BitVec.cons J b := ⟨_, _, (BitVec.cons_msb_setWidth j).symm⟩
  simp only [BitVec.msb_cons, BitVec.setWidth_cons] at h ha hb hab ⊢
  cases I <;> cases J
  · exact absurd rfl h
  · exact alignedPairCount_false_true_add ha hb hab
  · rw [alignedPairCount_comm, alignedPairCount_comm k]
    exact alignedPairCount_false_true_add hb ha (Ne.symm hab)
  · exact absurd rfl h

/-- The three cases of the recursion in one statement. -/
theorem alignedPairCount_succ_cases {k : ℕ} (i j : BitVec (k + 1)) :
    alignedPairCount (k + 1) i j = 2 * alignedPairCount k (i.setWidth k) (j.setWidth k) ∨
      alignedPairCount (k + 1) i j = 0 ∨
      alignedPairCount (k + 1) i j + 2 * alignedPairCount k (i.setWidth k) (j.setWidth k) + 4 =
        2 ^ k := by
  by_cases h : i.msb = j.msb
  · exact Or.inl (alignedPairCount_succ_of_msb_eq h)
  · by_cases hd : i.setWidth k = 0#k ∨ j.setWidth k = 0#k ∨ i.setWidth k = j.setWidth k
    · exact Or.inr (Or.inl (alignedPairCount_succ_eq_zero h hd))
    · simp only [not_or] at hd
      exact Or.inr (Or.inr (alignedPairCount_succ_add h hd.1 hd.2.1 hd.2.2))

/-- No two-term operand has an aligned pair at a level `k ≤ 3`. -/
theorem alignedPairCount_eq_zero_of_le_three :
    ∀ {k : ℕ}, k ≤ 3 → ∀ i j : BitVec k, alignedPairCount k i j = 0
  | 0, _, i, j => by rw [Subsingleton.elim i j, alignedPairCount_self]
  | k + 1, hk, i, j => by
    have ih := alignedPairCount_eq_zero_of_le_three (k := k) (by omega)
      (i.setWidth k) (j.setWidth k)
    have h4 : 2 ^ k ≤ 4 := by
      calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 4 := by norm_num
    rcases alignedPairCount_succ_cases i j with h | h | h <;> omega

/-- An operand with the term `e 0 = 1` has no aligned pair. -/
theorem alignedPairCount_zero_left : ∀ (k : ℕ) (j : BitVec k), alignedPairCount k 0#k j = 0
  | 0, j => by rw [Subsingleton.elim j 0#0, alignedPairCount_self]
  | k + 1, j => by
    have hz : (0#(k + 1)).setWidth k = 0#k := by simp
    by_cases h : (0#(k + 1)).msb = j.msb
    · rw [alignedPairCount_succ_of_msb_eq h, hz, alignedPairCount_zero_left k]
    · exact alignedPairCount_succ_eq_zero h (Or.inl hz)

theorem alignedPairCount_zero_right (k : ℕ) (i : BitVec k) : alignedPairCount k i 0#k = 0 := by
  rw [alignedPairCount_comm, alignedPairCount_zero_left]

/-- An operand with the term `e (2 ^ k)`, the unit that the last doubling
adjoins, has no aligned pair. -/
theorem alignedPairCount_top_left (k : ℕ) (j : BitVec (k + 1)) :
    alignedPairCount (k + 1) (BitVec.cons true 0#k) j = 0 := by
  by_cases h : (BitVec.cons true 0#k).msb = j.msb
  · rw [alignedPairCount_succ_of_msb_eq h, BitVec.setWidth_cons, alignedPairCount_zero_left]
  · exact alignedPairCount_succ_eq_zero h (Or.inl BitVec.setWidth_cons)

/-- The unit that the last doubling adjoins has the index `2 ^ k`. -/
theorem cons_true_zero_eq_twoPow (k : ℕ) : BitVec.cons true 0#k = BitVec.twoPow (k + 1) k := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.lt_succ_self k))]

theorem alignedPairCount_top_right (k : ℕ) (i : BitVec (k + 1)) :
    alignedPairCount (k + 1) i (BitVec.cons true 0#k) = 0 := by
  rw [alignedPairCount_comm, alignedPairCount_top_left]

theorem four_dvd_two_pow_or_lt {k : ℕ} : 2 ^ k < 4 ∨ 4 ∣ 2 ^ k := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · left
    calc 2 ^ k < 2 ^ 2 := Nat.pow_lt_pow_right (by norm_num) hk
      _ = 4 := by norm_num
  · right
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    exact ⟨2 ^ m, by ring⟩

/-- Every aligned-pair count is a multiple of `4`. -/
theorem four_dvd_alignedPairCount : ∀ (k : ℕ) (i j : BitVec k), 4 ∣ alignedPairCount k i j
  | 0, i, j => by rw [Subsingleton.elim i j, alignedPairCount_self]; exact dvd_zero 4
  | k + 1, i, j => by
    have ih := four_dvd_alignedPairCount k (i.setWidth k) (j.setWidth k)
    have hp := four_dvd_two_pow_or_lt (k := k)
    rcases alignedPairCount_succ_cases i j with h | h | h <;> omega

/-- An aligned-pair count at level `k` is `0` or at most `2 ^ (k - 1) - 4`. -/
theorem alignedPairCount_eq_zero_or_add_four_le :
    ∀ (k : ℕ) (i j : BitVec k),
      alignedPairCount k i j = 0 ∨ alignedPairCount k i j + 4 ≤ 2 ^ (k - 1)
  | 0, i, j => Or.inl (by rw [Subsingleton.elim i j, alignedPairCount_self])
  | k + 1, i, j => by
    have ih := alignedPairCount_eq_zero_or_add_four_le k (i.setWidth k) (j.setWidth k)
    have hp : k = 0 ∨ 2 ^ k = 2 * 2 ^ (k - 1) := by
      rcases k with _ | m
      · exact Or.inl rfl
      · exact Or.inr (by rw [Nat.add_sub_cancel, pow_succ]; ring)
    have hz : 3 < k ∨ alignedPairCount k (i.setWidth k) (j.setWidth k) = 0 := by
      rcases Nat.lt_or_ge 3 k with hk | hk
      · exact Or.inl hk
      · exact Or.inr (alignedPairCount_eq_zero_of_le_three hk _ _)
    rw [Nat.add_sub_cancel]
    rcases alignedPairCount_succ_cases i j with h | h | h <;> omega

/-- A nonzero aligned-pair count at level `k` is at most `2 ^ (k - 1) - 4`. -/
theorem alignedPairCount_add_four_le {k : ℕ} {i j : BitVec k} (h : alignedPairCount k i j ≠ 0) :
    alignedPairCount k i j + 4 ≤ 2 ^ (k - 1) :=
  (alignedPairCount_eq_zero_or_add_four_le k i j).resolve_left h

end Tower

end CayleyDickson
