/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Tower

/-!
# Sign laws of the basis products

Convention: `Tower.negSign k p q` (`GororobaMath.CayleyDickson.Tower`) is the Boolean sign of the
product of the basis units `e p * e q = ± e (p ^^^ q)` of level `k`, with indices `p q : BitVec k`
whose top bit selects the outer half of the double, and `Tower.sign k p q` is the same sign as
`1` or `-1`. A `true` value is the sign `-1`.

## Main results

* `Tower.negSign_xor_left_right`: for `b ≠ 0`, the signs of `(a, b)` and `(a ^^^ b, b)` differ, so
  right multiplication by `e b` twice negates every basis unit. The Rocq original is
  `sigma_right_involution` of `rocq/quantum/CdTowerBasisSign.v`.
* `Tower.amExponent_eq`: the cochain recursion of Albuquerque and Majid, by the top bit, gives
  `negSign k b a`. The Rocq original is `am_sign` of `rocq/quantum/CdTowerBasisSign.v`
  (Corollary 4.3).
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

theorem xor_eq_zero_iff_eq {k : ℕ} (a b : BitVec k) : a ^^^ b = 0#k ↔ a = b := by
  constructor
  · intro h
    calc a = (a ^^^ b) ^^^ b := by rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
      _ = b := by rw [h, BitVec.zero_xor]
  · rintro rfl
    exact BitVec.xor_self

/-- For `b ≠ 0`, the signs of `e a * e b` and `e (a ^^^ b) * e b` differ: right multiplication by
`e b` twice negates every basis unit. The Rocq original is `sigma_right_involution` of
`rocq/quantum/CdTowerBasisSign.v`. -/
theorem negSign_xor_left_right {k : ℕ} (a b : BitVec k) (hb : b ≠ 0#k) :
    (negSign k a b ^^ negSign k (a ^^^ b) b) = true := by
  have h1 := negSign_swap_xor k b (a ^^^ b)
  have h2 := negSign_xor_right k b a
  have h3 := negSign_swap_xor k a b
  rw [BitVec.xor_comm b a] at h2
  rw [h1, h2, h3]
  have hx1 : (a ^^^ b = 0#k) ↔ a = b := xor_eq_zero_iff_eq a b
  have hx2 : (b = a ^^^ b) ↔ a = 0#k := by
    constructor
    · intro h
      calc a = (a ^^^ b) ^^^ b := by rw [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
        _ = 0#k := by rw [← h]; exact BitVec.xor_self
    · rintro rfl
      simp
  by_cases ha : a = 0#k
  · subst ha
    simp [hb]
  · by_cases hab : a = b
    · subst hab
      simp [hb]
    · simp [hb, ha, hab, hx1, hx2]

/-- The cochain recursion of Albuquerque and Majid, by the top bit of each index. -/
def amExponent : (k : ℕ) → BitVec k → BitVec k → Bool
  | 0, _, _ => false
  | k + 1, x, y =>
    xor (if x.msb then amExponent k (y.setWidth k) (x.setWidth k)
        else amExponent k (x.setWidth k) (y.setWidth k))
      (xor (y.msb && amExponent k (x.setWidth k) (x.setWidth k)) (x.msb && y.msb))

theorem amExponent_cons (k : ℕ) (P Q : Bool) (p q : BitVec k) :
    amExponent (k + 1) (BitVec.cons P p) (BitVec.cons Q q) =
      xor (if P then amExponent k q p else amExponent k p q)
        (xor (Q && amExponent k p p) (P && Q)) := by
  simp [amExponent]

/-- The recursion of Albuquerque and Majid (Corollary 4.3) gives `negSign k b a`. The Rocq original
is `am_sign` of `rocq/quantum/CdTowerBasisSign.v`, whose `am_exponent k a b` is
`amExponent k a b`. -/
theorem amExponent_eq : ∀ (k : ℕ) (a b : BitVec k), amExponent k a b = negSign k b a
  | 0, _, _ => rfl
  | k + 1, a, b => by
    obtain ⟨P, p, rfl⟩ : ∃ P p, a = BitVec.cons P p :=
      ⟨a.msb, a.setWidth k, (BitVec.cons_msb_setWidth a).symm⟩
    obtain ⟨Q, q, rfl⟩ : ∃ Q q, b = BitVec.cons Q q :=
      ⟨b.msb, b.setWidth k, (BitVec.cons_msb_setWidth b).symm⟩
    rw [amExponent_cons, amExponent_eq k, amExponent_eq k, amExponent_eq k, negSign_cons,
      negSign_self_eq, negSign_swap_xor k q p]
    generalize negSign k q p = s
    generalize decide (p ≠ 0#k) = d1
    generalize decide (q ≠ 0#k ∧ p ≠ 0#k ∧ q ≠ p) = d2
    cases P <;> cases Q <;> cases s <;> cases d1 <;> cases d2 <;> rfl

end Tower

end CayleyDickson
