/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AssociatorSpace

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

end Tower

end CayleyDickson
