/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AssociatorSpace
public import GororobaMath.CayleyDickson.SignLaws

/-!
# The associator phase of three basis elements

Convention: `Tower R k` and its basis `Tower.e R k p` are those of
`GororobaMath.CayleyDickson.Tower`: the index `p : BitVec k` has its most
significant bit outermost, so `BitVec.cons P p` is the index of level `k + 1`
whose top bit `P` selects the second half of the last double, and
`e k p * e k q = -e k (p ^^^ q)` exactly when `Tower.negSign k p q` holds. A Bool
phase reads `true` as the sign `-1`.

`Tower.assocPhase p q x` is `true` when `e p * (e q * e x)` and
`(e p * e q) * e x` carry opposite signs. It is `!Tower.associates p x q`, since
`Tower.associates a b c` compares `(e a * e c) * e b` with `e a * (e c * e b)`,
middle argument last; as a sum of four signs it is
`negSign p q ^^ negSign (p ^^^ q) x ^^ negSign q x ^^ negSign p (q ^^^ x)`
(`Tower.assocPhase_eq`). `Tower.commPhase a b` is `true` when `e a` and `e b`
anticommute, which happens exactly for two distinct indices other than `0`
(`Tower.commPhase_eq`).

`Tower.assocPhase` mirrors `predict.associator_phase` of
`gororoba_quantum/predict.py` in gororoba-quantum: `associator_phase(2 ^ k, i, j)[x]`,
the product `cd_sign(i, j) * cd_sign(i ^ j, x) * cd_sign(j, x) * cd_sign(i, j ^ x)`
at level `k`, is `-1` exactly when `assocPhase i j x` holds, for the indices read
as `i.toNat`, `j.toNat` and `x.toNat`. `ci/compare_assoc_phase.sh` runs both sides,
and the Rocq `assoc` of `rocq/quantum/CdAssociatorAnf.v` on every triple at levels
1 to 5.

## Main results

* `Tower.e_mul_e_mul_e`: `e p * (e q * e x)` is `(e p * e q) * e x`, negated
  when `assocPhase p q x` holds, over every nonassociative star ring. The Rocq
  original is `assoc_basis` of `rocq/quantum/CdAssociatorAnf.v`, over the integers,
  whose `assoc k p q x` is `assocPhase` at `p.toNat`, `q.toNat`, `x.toNat`.
* `Tower.negSign_cons_eq`: the sign of a product at level `k + 1` as the sign of
  the low parts, corrected by the commutation phase and the top bits, the Rocq
  `sign_doubling` of `rocq/open/theories/CDAssociatorDoubling.v`.
* `Tower.assocPhase_cons`: the associator phase at level `k + 1` is the phase of
  the low parts plus top-bit corrections built from indicators of nonzero indices
  and commutation phases; every product of two top bits cancels. The Rocq original
  is `associator_doubling` of `rocq/open/theories/CDAssociatorDoubling.v`,
  whose `associator_phase order l m r` (`schreier l m r` plus `sign_exponent l m`)
  is `assocPhase l m r`, with the cube pair `(x, high)` read as `BitVec.cons high x`
  and `sign_exponent` as `negSign`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

/-- `true` when `e p * (e q * e x)` and `(e p * e q) * e x` carry opposite signs. -/
def assocPhase {k : ℕ} (p q x : BitVec k) : Bool := !associates p x q

/-- `true` when `e a * e b` and `e b * e a` carry opposite signs. -/
def commPhase {k : ℕ} (a b : BitVec k) : Bool := negSign k a b ^^ negSign k b a

/-- The associator phase is the sum of the four signs of the two bracketings. -/
theorem assocPhase_eq {k : ℕ} (p q x : BitVec k) :
    assocPhase p q x =
      (negSign k p q ^^ negSign k (p ^^^ q) x ^^ negSign k q x ^^ negSign k p (q ^^^ x)) := by
  unfold assocPhase associates
  cases negSign k p q <;> cases negSign k (p ^^^ q) x <;> cases negSign k q x <;>
    cases negSign k p (q ^^^ x) <;> rfl

/-- Two basis elements anticommute exactly when they are distinct and neither is `1`. -/
theorem commPhase_eq {k : ℕ} (a b : BitVec k) :
    commPhase a b = decide (a ≠ 0#k ∧ b ≠ 0#k ∧ a ≠ b) := by
  unfold commPhase
  rw [negSign_swap_xor k a b]
  cases negSign k a b <;> simp

/-- The sign of a product at level `k + 1`: the sign of the low parts, the
commutation phase of the low parts when the right factor has its top bit, the
indicator of a nonzero right low part when the left factor has its top bit, and
the product of the two top bits. The Rocq original is `sign_doubling` of
`rocq/open/theories/CDAssociatorDoubling.v`. -/
theorem negSign_cons_eq (k : ℕ) (P Q : Bool) (p q : BitVec k) :
    negSign (k + 1) (BitVec.cons P p) (BitVec.cons Q q) =
      (negSign k p q ^^ (Q && commPhase p q) ^^ (P && decide (q ≠ 0#k)) ^^ (P && Q)) := by
  rw [negSign_cons, commPhase_eq]
  generalize negSign k p q = s
  generalize decide (q ≠ 0#k) = d
  generalize decide (p ≠ 0#k ∧ q ≠ 0#k ∧ p ≠ q) = c
  revert P Q s d c
  decide

section Ring

variable {R : Type u} [NonAssocRing R] [StarRing R]

/-- `e p * (e q * e x) = ±(e p * e q) * e x`, negated exactly when
`assocPhase p q x` holds. The Rocq original is `assoc_basis` of
`rocq/quantum/CdAssociatorAnf.v`. -/
theorem e_mul_e_mul_e {k : ℕ} (p q x : BitVec k) :
    e R k p * (e R k q * e R k x) =
      if assocPhase p q x then -(e R k p * e R k q * e R k x)
      else e R k p * e R k q * e R k x := by
  have hx : p ^^^ (q ^^^ x) = p ^^^ q ^^^ x := (BitVec.xor_assoc _ _ _).symm
  rw [assocPhase_eq, e_mul_e k q x, e_mul_e k p q]
  cases h1 : negSign k q x <;> cases h2 : negSign k p q <;>
    simp only [Bool.false_eq_true, ↓reduceIte, mul_neg, neg_mul, neg_neg, e_mul_e, hx] <;>
    cases negSign k p (q ^^^ x) <;> cases negSign k (p ^^^ q) x <;> simp

end Ring

/-- The associator phase at level `k + 1`. The products of two top bits cancel
among the four signs; what remains is the phase of the low parts, the left top
bit times the indicators of the nonzero indices among `m`, `r`, `m ^^^ r`, and the
middle and right top bits times sums of commutation phases. The Rocq original is
`associator_doubling` of `rocq/open/theories/CDAssociatorDoubling.v`. -/
theorem assocPhase_cons {k : ℕ} (L M N : Bool) (l m r : BitVec k) :
    assocPhase (BitVec.cons L l) (BitVec.cons M m) (BitVec.cons N r) =
      (assocPhase l m r ^^
        (L && (decide (m ≠ 0#k) ^^ decide (r ≠ 0#k) ^^ decide (m ^^^ r ≠ 0#k))) ^^
        (M && (commPhase l m ^^ commPhase l (m ^^^ r))) ^^
        (N && (commPhase (l ^^^ m) r ^^ commPhase m r ^^ commPhase l (m ^^^ r)))) := by
  rw [assocPhase_eq, assocPhase_eq, BitVec.cons_xor_cons, BitVec.cons_xor_cons,
    negSign_cons_eq, negSign_cons_eq, negSign_cons_eq, negSign_cons_eq]
  generalize negSign k l m = s1
  generalize negSign k (l ^^^ m) r = s2
  generalize negSign k m r = s3
  generalize negSign k l (m ^^^ r) = s4
  generalize commPhase l m = c1
  generalize commPhase (l ^^^ m) r = c2
  generalize commPhase m r = c3
  generalize commPhase l (m ^^^ r) = c4
  generalize decide (m ≠ 0#k) = d1
  generalize decide (r ≠ 0#k) = d2
  generalize decide (m ^^^ r ≠ 0#k) = d3
  revert L M N s1 s2 s3 s4 c1 c2 c3 c4 d1 d2 d3
  decide

/-- The quaternion units `e 1` and `e 2` associate with every unit, the Rocq
example `quaternion_pair_zero`. -/
example : ∀ r : BitVec 2, assocPhase 1#2 2#2 r = false := by decide

/-- In the octonions the phase of `e 1`, `e 2` and `e r` is the top bit of `r`,
the Rocq example `octonion_pair_parity`. -/
example : ∀ r : BitVec 3, assocPhase 1#3 2#3 r = r.msb := by decide

/-- A basis triple with a zero member, a repeated member or `r = l ^^^ m` associates: the
associator phase vanishes. The Rocq original is `dependent_basis_triple_associates` of
`rocq/open/theories/CDAssociatorCensus.v`, whose `associator_phase` is `assocPhase l m r`
through `cube_encode`. -/
theorem assocPhase_eq_false_of_dependent {k : ℕ} {l m r : BitVec k}
    (h : l = 0#k ∨ m = 0#k ∨ r = 0#k ∨ l = m ∨ l = r ∨ m = r ∨ l ^^^ m = r) :
    assocPhase l m r = false := by
  have e1 : ∀ a b : BitVec k, (a ^^^ b = 0#k) ↔ a = b := fun a b => BitVec.xor_eq_zero_iff
  have e2 : ∀ a b : BitVec k, (a = a ^^^ b) ↔ b = 0#k := fun a b =>
    eq_comm.trans xor_left_eq_self_iff
  rw [assocPhase_eq]
  rcases h with h | h | h | h | h | h | h
  · rw [h]
    simp [negSign_zero_left]
  · rw [h]
    simp [negSign_zero_left, negSign_zero_right]
  · rw [h]
    simp [negSign_zero_right]
  · rw [← h, BitVec.xor_self, negSign_xor_right, negSign_self_eq, negSign_zero_left]
    cases negSign k l r <;> cases decide (l ≠ 0#k) <;> simp
  · rw [← h, BitVec.xor_comm m l, negSign_xor_right, negSign_swap_xor k l (l ^^^ m),
      negSign_swap_xor k l m, negSign_xor_right]
    simp only [ne_eq, e1, e2]
    by_cases hl : l = 0#k <;> by_cases hm : m = 0#k <;> by_cases hlm : l = m <;>
      simp_all [negSign_zero_right]
  · rw [← h, BitVec.xor_self]
    by_cases hm : m = 0#k
    · simp [hm, negSign_zero_right]
    · have key := negSign_xor_left_right l m hm
      simp only [negSign_zero_right, negSign_self_eq, Bool.xor_false, key, Bool.true_xor]
      simp [hm]
  · have h3 : m ^^^ (m ^^^ l) = l := by rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    have hml : m = l ↔ l = m := eq_comm
    have h0l : 0#k = l ↔ l = 0#k := eq_comm
    rw [← h, BitVec.xor_comm l m, h3]
    simp only [negSign_self_eq]
    rw [negSign_xor_right k m l, negSign_swap_xor k l m]
    simp only [ne_eq, e1]
    by_cases hl : l = 0#k <;> by_cases hm : m = 0#k <;> by_cases hlm : l = m <;>
      simp [hl, hm, hlm, hml, h0l]

/-- The associator phase vanishes when `p = 0`, `q = 0` or `p = q`. The Rocq original is
`assoc_degenerate` of `rocq/quantum/CdAssociatorAnf.v`. -/
theorem assocPhase_eq_false_of_degenerate {k : ℕ} {p q : BitVec k}
    (h : p = 0#k ∨ q = 0#k ∨ p = q) (x : BitVec k) : assocPhase p q x = false := by
  rcases h with h | h | h
  · exact assocPhase_eq_false_of_dependent (Or.inl h)
  · exact assocPhase_eq_false_of_dependent (Or.inr (Or.inl h))
  · exact assocPhase_eq_false_of_dependent (Or.inr (Or.inr (Or.inr (Or.inl h))))

/-- Every basis triple of the quaternions associates. The Rocq original is
`quaternion_associator_all` of `rocq/open/theories/CDPhaseDegree.v`. -/
theorem assocPhase_two (p q x : BitVec 2) : assocPhase p q x = false := by
  revert p q x
  decide

/-- For distinct nonzero `l` and `r` the pair coefficient is `1`. The Rocq original is
`independent_pair_coefficient` of `rocq/open/theories/CDAssociatorDoubling.v`. -/
theorem pairCoeff_eq_true {k : ℕ} {l r : BitVec k} (hl : l ≠ 0#k) (hr : r ≠ 0#k) (hlr : l ≠ r) :
    (decide (l ≠ 0#k) ^^ decide (r ≠ 0#k) ^^ decide (l ^^^ r ≠ 0#k)) = true := by
  have h : l ^^^ r ≠ 0#k := fun h => hlr (BitVec.xor_eq_zero_iff.1 h)
  simp [hl, hr, h]

end Tower

end CayleyDickson
