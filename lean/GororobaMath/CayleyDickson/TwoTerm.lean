/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Tower

/-!
# Two-term operands and their aligned pairs

Left multiplication by `e i + e j` carries the pair of basis elements
`{e x, e x'}`, `x' = x ^^^ i ^^^ j`, into the pair
`{e (i ^^^ x), e (j ^^^ x)}`, since `i ^^^ x' = j ^^^ x`. On that pair it is
a two-by-two matrix of signs. When the pair is *aligned*, `e x + e x'` or
`e x - e x'` lies in its kernel; this file proves that implication. The
converse, that an unaligned pair has determinant `±2`, and the resulting
nullity are in `GororobaMath.CayleyDickson.TwoTermNullity`. gororoba-quantum
reads the nullity of a two-term operand with `i ≠ j` as its number of
aligned pairs (`docs/evidence/pathion-kernel-map/README.md`,
`gororoba_quantum/pathion_kernel_map.py`).

## Main results

* `Tower.two_term_mul_add_eq_zero`, `Tower.two_term_mul_sub_eq_zero`: over
  every ring and at every level, an aligned pair gives the explicit zero
  product `(e i + e j) * (e x ± e x') = 0`.
* `Tower.partner_partner`, `Tower.partner_eq_self_iff`: `partner i j` is an
  involution, with a fixed point exactly when `i = j`, so for `i ≠ j` the
  indices split into two-element pairs.
* `Tower.alignedAdd_partner`, `Tower.alignedSub_partner`,
  `Tower.alignedAdd_and_alignedSub`: alignment is a property of the pair, and
  the two kinds exclude each other.
* `Tower.alignedPairCount`: the number of aligned pairs for `i ≠ j`, and `0`
  for `i = j`, where every index is its own partner and the operand is
  `e i + e i`; the instances below evaluate it in the kernel for the
  operands of the retained hardware runs.

Each aligned pair contributes one explicit zero product, and the vectors
`e x ± e x'` of different pairs have disjoint index sets. No nullity is
defined in this file; `Tower.finrank_ker_mulLeft_e_add_e` proves that the
nullity of left multiplication by `e i + e j` equals `alignedPairCount`
over every nontrivial commutative ring with the identity as star in which
`2` is a non-zero-divisor.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [NonAssocRing R] [StarRing R]

/-- The partner index of `x` under the operand `e i + e j`. -/
def partner {k : ℕ} (i j x : BitVec k) : BitVec k := x ^^^ i ^^^ j

/-- The pair `{x, partner i j x}` is aligned with opposite signs: the sign
of `e i * e x` is opposite to that of `e j * e x'`, and the sign of
`e j * e x` opposite to that of `e i * e x'`. -/
def alignedAdd (k : ℕ) (i j x : BitVec k) : Bool :=
  (negSign k i x != negSign k j (partner i j x)) &&
    (negSign k j x != negSign k i (partner i j x))

/-- The pair `{x, partner i j x}` is aligned with equal signs. -/
def alignedSub (k : ℕ) (i j x : BitVec k) : Bool :=
  (negSign k i x == negSign k j (partner i j x)) &&
    (negSign k j x == negSign k i (partner i j x))

theorem xor_partner_left {k : ℕ} (i j x : BitVec k) : i ^^^ partner i j x = j ^^^ x := by
  rw [partner, BitVec.xor_comm x i, BitVec.xor_assoc, ← BitVec.xor_assoc i i, BitVec.xor_self,
    BitVec.zero_xor, BitVec.xor_comm]

theorem xor_partner_right {k : ℕ} (i j x : BitVec k) : j ^^^ partner i j x = i ^^^ x := by
  rw [partner, BitVec.xor_comm (x ^^^ i) j, ← BitVec.xor_assoc, BitVec.xor_self,
    BitVec.zero_xor, BitVec.xor_comm]

/-- `partner i j` is an involution. -/
theorem partner_partner {k : ℕ} (i j x : BitVec k) : partner i j (partner i j x) = x := by
  unfold partner
  ext n hn
  simp only [BitVec.getElem_xor]
  cases x[n] <;> cases i[n] <;> cases j[n] <;> rfl

/-- An index is its own partner exactly when the operand repeats one basis
element, so for `i ≠ j` every pair `{x, partner i j x}` has two elements. -/
theorem partner_eq_self_iff {k : ℕ} (i j x : BitVec k) : partner i j x = x ↔ i = j := by
  unfold partner
  constructor
  · intro h
    ext n hn
    have hb := congrArg (fun v : BitVec k => v[n]) h
    simp only [BitVec.getElem_xor] at hb
    revert hb
    cases x[n] <;> cases i[n] <;> cases j[n] <;> simp
  · rintro rfl
    ext n hn
    simp only [BitVec.getElem_xor]
    cases x[n] <;> cases i[n] <;> rfl

/-- Alignment with opposite signs is a property of the pair. -/
theorem alignedAdd_partner (k : ℕ) (i j x : BitVec k) :
    alignedAdd k i j (partner i j x) = alignedAdd k i j x := by
  unfold alignedAdd
  rw [partner_partner]
  cases negSign k i x <;> cases negSign k j (partner i j x) <;> cases negSign k j x <;>
    cases negSign k i (partner i j x) <;> rfl

/-- Alignment with equal signs is a property of the pair. -/
theorem alignedSub_partner (k : ℕ) (i j x : BitVec k) :
    alignedSub k i j (partner i j x) = alignedSub k i j x := by
  unfold alignedSub
  rw [partner_partner]
  cases negSign k i x <;> cases negSign k j (partner i j x) <;> cases negSign k j x <;>
    cases negSign k i (partner i j x) <;> rfl

/-- No pair is aligned in both ways. -/
theorem alignedAdd_and_alignedSub (k : ℕ) (i j x : BitVec k) :
    (alignedAdd k i j x && alignedSub k i j x) = false := by
  unfold alignedAdd alignedSub
  cases negSign k i x <;> cases negSign k j (partner i j x) <;> cases negSign k j x <;>
    cases negSign k i (partner i j x) <;> rfl

/-- The four products of the operand's terms with the pair's terms. -/
theorem two_term_mul_pair (k : ℕ) (i j x : BitVec k) :
    (e R k i + e R k j) * (e R k x + e R k (partner i j x)) =
      (e R k i * e R k x + e R k j * e R k (partner i j x)) +
        (e R k j * e R k x + e R k i * e R k (partner i j x)) := by
  rw [add_mul, mul_add, mul_add]
  abel

/-- An aligned pair of opposite signs gives the zero product
`(e i + e j) * (e x + e x') = 0`. -/
theorem two_term_mul_add_eq_zero (k : ℕ) (i j x : BitVec k) (h : alignedAdd k i j x = true) :
    (e R k i + e R k j) * (e R k x + e R k (partner i j x)) = 0 := by
  simp only [alignedAdd, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [two_term_mul_pair, e_mul_e, e_mul_e, e_mul_e, e_mul_e, xor_partner_left,
    xor_partner_right]
  cases a : negSign k i x <;> cases b : negSign k j (partner i j x) <;>
    cases c : negSign k j x <;> cases d : negSign k i (partner i j x) <;> simp_all

/-- An aligned pair of equal signs gives the zero product
`(e i + e j) * (e x - e x') = 0`. -/
theorem two_term_mul_sub_eq_zero (k : ℕ) (i j x : BitVec k) (h : alignedSub k i j x = true) :
    (e R k i + e R k j) * (e R k x - e R k (partner i j x)) = 0 := by
  simp only [alignedSub, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [sub_eq_add_neg, add_mul, mul_add, mul_add, mul_neg, mul_neg, e_mul_e, e_mul_e, e_mul_e,
    e_mul_e, xor_partner_left, xor_partner_right, h1, h2]
  cases negSign k j (partner i j x) <;> cases negSign k i (partner i j x) <;> simp

/-- The number of aligned pairs of the operand `e i + e j` with `i ≠ j`:
each pair `{x, partner i j x}` has two elements (`partner_eq_self_iff`) that
are aligned together (`alignedAdd_partner`, `alignedSub_partner`), so the
count of aligned indices is halved. For `i = j` every index is its own
partner and `e x - e x = 0` is no kernel direction, so the count is `0`. -/
def alignedPairCount (k : ℕ) (i j : BitVec k) : ℕ :=
  if i = j then 0
  else
    ((List.range (2 ^ k)).filter fun n =>
      alignedAdd k i j (BitVec.ofNat k n) || alignedSub k i j (BitVec.ofNat k n)).length / 2

/-- A repeated basis element has no aligned pair. -/
theorem alignedPairCount_self (k : ℕ) (i : BitVec k) : alignedPairCount k i i = 0 := by
  simp [alignedPairCount]

/-- The sedenion operand `e_1 + e_10` has four aligned pairs. -/
theorem alignedPairCount_sedenion_1_10 : alignedPairCount 4 1#4 10#4 = 4 := by decide

/-- The `A_5` operand `e_1 + e_18` has twelve aligned pairs. -/
theorem alignedPairCount_pathion_1_18 : alignedPairCount 5 1#5 18#5 = 12 := by decide

/-- The `A_5` operand `e_1 + e_24` has twelve aligned pairs. -/
theorem alignedPairCount_pathion_1_24 : alignedPairCount 5 1#5 24#5 = 12 := by decide

/-- The `A_5` operand `e_1 + e_17` has no aligned pair. -/
theorem alignedPairCount_pathion_1_17 : alignedPairCount 5 1#5 17#5 = 0 := by decide

/-- The `A_5` operand `e_1 + e_26` has four aligned pairs. -/
theorem alignedPairCount_pathion_1_26 : alignedPairCount 5 1#5 26#5 = 4 := by decide

/-- The `A_5` operand `e_2 + e_27` has four aligned pairs. -/
theorem alignedPairCount_pathion_2_27 : alignedPairCount 5 2#5 27#5 = 4 := by decide

/-- A zero divisor of `A_5` over every ring: `(e_1 + e_18)(e_5 + e_22) = 0`. -/
theorem pathion_e1_add_e18_mul_e5_add_e22 :
    (e R 5 1#5 + e R 5 18#5) * (e R 5 5#5 + e R 5 22#5) = 0 :=
  two_term_mul_add_eq_zero 5 1#5 18#5 5#5 (by decide)

/-- A zero divisor of `A_5` over every ring: `(e_1 + e_18)(e_4 - e_23) = 0`. -/
theorem pathion_e1_add_e18_mul_e4_sub_e23 :
    (e R 5 1#5 + e R 5 18#5) * (e R 5 4#5 - e R 5 23#5) = 0 :=
  two_term_mul_sub_eq_zero 5 1#5 18#5 4#5 (by decide)

/-- A zero divisor of the sedenions over every ring:
`(e_1 + e_10)(e_5 + e_14) = 0`. -/
theorem sedenion_e1_add_e10_mul_e5_add_e14 :
    (e R 4 1#4 + e R 4 10#4) * (e R 4 5#4 + e R 4 14#4) = 0 :=
  two_term_mul_add_eq_zero 4 1#4 10#4 5#4 (by decide)

end Tower

end CayleyDickson
