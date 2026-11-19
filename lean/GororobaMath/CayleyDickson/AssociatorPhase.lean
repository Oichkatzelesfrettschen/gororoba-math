/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AssociatorSpace
public import GororobaMath.CayleyDickson.BooleanAnf
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
* `Tower.anfDegree_assocPhase`: for `3 ≤ k` and distinct nonzero `p`, `q` the phase
  `assocPhase p q` has algebraic degree `max 1 (Nat.log2 (max p.toNat q.toNat) - 1)`, the Rocq
  `assoc_degree_is` of `rocq/quantum/CdAssociatorAnf.v` and `associator_phase_degree` of
  `rocq/open/theories/CDPhaseDegree.v`.
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

section Degree

theorem commPhase_eq_xor {k : ℕ} (a b : BitVec k) :
    commPhase a b = (decide (a ≠ 0#k) ^^ decide (b = 0#k) ^^ decide (b = a)) := by
  rw [commPhase_eq]
  by_cases ha : a = 0#k
  · subst ha
    simp
  · by_cases hb : b = 0#k
    · subst hb
      simp [ha, Ne.symm ha]
    · by_cases hba : b = a
      · subst hba
        simp [ha]
      · simp [ha, hb, hba, Ne.symm hba]

theorem commPhase_eq_cst {k : ℕ} (a b : BitVec k) :
    commPhase a b = (decide (a ≠ 0#k) ^^ decide (b ≠ 0#k) ^^ decide (a ^^^ b ≠ 0#k)) := by
  rw [commPhase_eq]
  have e : (a ^^^ b = 0#k) ↔ a = b := BitVec.xor_eq_zero_iff
  by_cases ha : a = 0#k
  · subst ha
    simp
  · by_cases hb : b = 0#k
    · subst hb
      simp [ha]
    · by_cases hab : a = b
      · subst hab
        simp [ha]
      · simp [ha, hb, hab, e]

/-- The coefficient of the top bit of the third index in `assocPhase_cons` is the constant
`[l ≠ 0] + [m ≠ 0] + [l ^^^ m ≠ 0]`, whatever the low part `r` is. -/
theorem commPhase_xor_triple {k : ℕ} (l m r : BitVec k) :
    (commPhase (l ^^^ m) r ^^ commPhase m r ^^ commPhase l (m ^^^ r)) =
      (decide (l ≠ 0#k) ^^ decide (m ≠ 0#k) ^^ decide (l ^^^ m ≠ 0#k)) := by
  rw [commPhase_eq_cst, commPhase_eq_cst, commPhase_eq_cst, ← BitVec.xor_assoc]
  generalize decide (l ^^^ m ≠ 0#k) = d1
  generalize decide (r ≠ 0#k) = d2
  generalize decide (l ^^^ m ^^^ r ≠ 0#k) = d3
  generalize decide (m ≠ 0#k) = d4
  generalize decide (m ^^^ r ≠ 0#k) = d5
  generalize decide (l ≠ 0#k) = d6
  revert d1 d2 d3 d4 d5 d6
  decide

theorem decide_xor_eq_zero {n : ℕ} (m y : BitVec n) : decide (m ^^^ y = 0#n) = decide (y = m) := by
  have e : (m ^^^ y = 0#n) ↔ (y = m) := by
    rw [BitVec.xor_eq_zero_iff]
    exact eq_comm
  exact decide_eq_decide.2 e

theorem decide_xor_eq {n : ℕ} (q y p : BitVec n) : decide (q ^^^ y = p) = decide (y = q ^^^ p) := by
  have e : (q ^^^ y = p) ↔ (y = q ^^^ p) := by
    constructor
    · intro h
      rw [← h, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
    · intro h
      rw [h, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  exact decide_eq_decide.2 e

/-- A function of positive degree has a monomial of that degree. -/
theorem exists_anfCoeff_weight_eq {k : ℕ} {f : BitVec k → Bool} (h : 1 ≤ anfDegree f) :
    ∃ s, anfCoeff f s = true ∧ weight s = anfDegree f := by
  by_cases hne : (Finset.univ.filter fun s => anfCoeff f s = true).Nonempty
  · obtain ⟨s, hs, h'⟩ := Finset.exists_mem_eq_sup _ hne weight
    exact ⟨s, (Finset.mem_filter.1 hs).2, h'.symm⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    unfold anfDegree at h
    rw [hne] at h
    simp at h

/-- A function whose half with top bit `false` is `A` and whose half with top bit `true` differs
from it by a constant has the degree of `A`, when that is positive. -/
theorem anfDegree_lift {k : ℕ} {g : BitVec (k + 1) → Bool} {A : BitVec k → Bool} (c : Bool)
    (hd : 1 ≤ anfDegree A) (h0 : ∀ y, g (BitVec.cons false y) = A y)
    (h1 : ∀ y, g (BitVec.cons true y) = (g (BitVec.cons false y) ^^ c)) :
    anfDegree g = anfDegree A := by
  have hA : (fun q => g (BitVec.cons false q)) = A := funext h0
  have hc : (fun q => g (BitVec.cons true q) ^^ g (BitVec.cons false q)) = fun _ => c := by
    funext q
    rw [h1]
    cases c <;> cases g (BitVec.cons false q) <;> rfl
  apply le_antisymm
  · apply anfDegree_cons_le
    · intro s hs
      rw [hA] at hs
      exact le_anfDegree hs
    · intro s hs
      rw [hc] at hs
      cases c
      · rw [anfCoeff_false] at hs
        exact absurd hs (by simp)
      · rw [anfCoeff_true] at hs
        have : s = 0#k := by simpa using hs
        subst this
        rw [weight_zero]
        omega
  · obtain ⟨s, hs, hw⟩ := exists_anfCoeff_weight_eq hd
    have := le_anfDegree_cons_false (f := g) (s := s) (by rw [hA]; exact hs)
    omega

/-- The function that is `false` on the lower half and `true` on the upper half has degree `1`. -/
theorem anfDegree_lift_zero {k : ℕ} {g : BitVec (k + 1) → Bool}
    (h0 : ∀ y, g (BitVec.cons false y) = false) (h1 : ∀ y, g (BitVec.cons true y) = true) :
    anfDegree g = 1 := by
  have hA : (fun q => g (BitVec.cons false q)) = fun _ => false := funext h0
  have hc : (fun q => g (BitVec.cons true q) ^^ g (BitVec.cons false q)) = fun _ => true := by
    funext q
    rw [h1, h0]
    rfl
  apply le_antisymm
  · apply anfDegree_cons_le
    · intro s hs
      rw [hA, anfCoeff_false] at hs
      exact absurd hs (by simp)
    · intro s hs
      rw [hc, anfCoeff_true] at hs
      have : s = 0#k := by simpa using hs
      subst this
      rw [weight_zero]
  · have := le_anfDegree_cons_true (f := g) (s := 0#k) (by rw [hc, anfCoeff_true]; simp)
    rw [weight_zero] at this
    exact this

/-- Adding terms of lower degree keeps a positive degree. -/
theorem anfDegree_xor_lower {k : ℕ} {F G : BitVec k → Bool} {d e : ℕ} (hF : anfDegree F = d)
    (hd : 1 ≤ d) (hG : ∀ s, anfCoeff G s = true → weight s ≤ e) (he : e < d) :
    anfDegree (fun x => F x ^^ G x) = d := by
  obtain ⟨s0, hs0, hw0⟩ := exists_anfCoeff_weight_eq (f := F) (by omega)
  apply le_antisymm
  · apply anfDegree_le
    intro s hs
    rw [anfCoeff_xor] at hs
    cases hFs : anfCoeff F s
    · rw [hFs] at hs
      have hGs : anfCoeff G s = true := by simpa using hs
      have := hG s hGs
      omega
    · rw [← hF]
      exact le_anfDegree hFs
  · have hGs : anfCoeff G s0 = false := by
      by_contra hne
      have := hG s0 (by simpa using hne)
      omega
    have : anfCoeff (fun x => F x ^^ G x) s0 = true := by
      rw [anfCoeff_xor, hs0, hGs]
      rfl
    have := le_anfDegree this
    omega

/-- Two point indicators over a lower-degree function have degree `n - 1`. -/
theorem anfDegree_point_pair {n : ℕ} (hn : 2 ≤ n) {G g : BitVec n → Bool} {u v : BitVec n}
    (huv : u ≠ v) (c0 : Bool) (hG : ∀ s, anfCoeff G s = true → weight s ≤ n - 2)
    (hg : ∀ y, g y = (G y ^^ (decide (y = u) ^^ decide (y = v)) ^^ c0)) :
    anfDegree g = n - 1 := by
  have hg' : g = fun y => (decide (y = u) ^^ decide (y = v)) ^^ (G y ^^ c0) := by
    funext y
    rw [hg]
    cases G y <;> cases c0 <;> cases decide (y = u) <;> cases decide (y = v) <;> rfl
  rw [hg']
  refine anfDegree_xor_lower (F := fun y => decide (y = u) ^^ decide (y = v))
    (G := fun y => G y ^^ c0) (e := n - 2) (anfDegree_two_point huv) (by omega) ?_ (by omega)
  intro s hs
  have hx : anfCoeff (fun y => G y ^^ c0) s = (anfCoeff G s ^^ anfCoeff (fun _ => c0) s) :=
    anfCoeff_xor G (fun _ => c0) s
  rw [hx] at hs
  by_cases hGs : anfCoeff G s = true
  · exact hG s hGs
  · have hGs' : anfCoeff G s = false := by simpa using hGs
    rw [hGs'] at hs
    cases c0
    · rw [anfCoeff_false] at hs
      exact absurd hs (by simp)
    · rw [anfCoeff_true] at hs
      have : s = 0#n := by simpa using hs
      subst this
      rw [weight_zero]
      omega

end Degree

section DegreeSteps

/-- The degree of the associator phase of two nonzero distinct indices, as a function of their
integer values: `max 1 (bitlen (max p q) - 2)`, with `bitlen n - 2 = Nat.log2 n - 1` for `n ≥ 1`. -/
def assocDegree (p q : ℕ) : ℕ := max 1 (Nat.log2 (max p q) - 1)

/-- The degree statement at level `n`. -/
def AssocDegreeAt (n : ℕ) : Prop :=
  ∀ a b : BitVec n, a ≠ 0#n → b ≠ 0#n → a ≠ b →
    anfDegree (assocPhase a b) = assocDegree a.toNat b.toNat

theorem assocDegree_le {n : ℕ} (hn : 3 ≤ n) {a b : BitVec n} (ha : a ≠ 0#n) :
    assocDegree a.toNat b.toNat ≤ n - 2 := by
  have ha' : a.toNat ≠ 0 := fun h => ha (BitVec.eq_of_toNat_eq (by simpa using h))
  have hm : max a.toNat b.toNat < 2 ^ n := max_lt a.isLt b.isLt
  have hm0 : max a.toNat b.toNat ≠ 0 := by
    intro h
    exact ha' (by omega)
  have := (Nat.log2_lt hm0).2 hm
  unfold assocDegree
  omega

theorem coeff_weight_le {n : ℕ} (hn : 2 ≤ n) (ih : n = 2 ∨ (3 ≤ n ∧ AssocDegreeAt n))
    (a b : BitVec n) (s : BitVec n) (hs : anfCoeff (assocPhase a b) s = true) :
    weight s ≤ n - 2 := by
  by_cases hdeg : a = 0#n ∨ b = 0#n ∨ a = b
  · have : assocPhase a b = fun _ => false := funext (assocPhase_eq_false_of_degenerate hdeg)
    rw [this, anfCoeff_false] at hs
    exact absurd hs (by simp)
  · simp only [not_or] at hdeg
    obtain ⟨ha, hb, hab⟩ := hdeg
    rcases ih with rfl | ⟨h3, ih⟩
    · have : assocPhase a b = fun _ => false := funext (assocPhase_two a b)
      rw [this, anfCoeff_false] at hs
      exact absurd hs (by simp)
    · have h1 := le_anfDegree hs
      rw [ih a b ha hb hab] at h1
      have := assocDegree_le h3 (b := b) ha
      omega

/-- A pair whose top bits are not both clear: the phase of the low parts plus two point
indicators and a constant has degree `n - 1`. -/
theorem anfDegree_assocPhase_top {n : ℕ} (hn : 2 ≤ n) (ih : n = 2 ∨ (3 ≤ n ∧ AssocDegreeAt n))
    (L M : Bool) (l m u v : BitVec n) (huv : u ≠ v) (c0 : Bool)
    (hform : ∀ y, (assocPhase l m y ^^
        (L && (decide (m ≠ 0#n) ^^ decide (y ≠ 0#n) ^^ decide (m ^^^ y ≠ 0#n))) ^^
        (M && (commPhase l m ^^ commPhase l (m ^^^ y)))) =
      (assocPhase l m y ^^ (decide (y = u) ^^ decide (y = v)) ^^ c0)) :
    anfDegree (assocPhase (BitVec.cons L l) (BitVec.cons M m)) = n - 1 := by
  set A : BitVec n → Bool := fun y =>
    assocPhase l m y ^^ (L && (decide (m ≠ 0#n) ^^ decide (y ≠ 0#n) ^^ decide (m ^^^ y ≠ 0#n))) ^^
      (M && (commPhase l m ^^ commPhase l (m ^^^ y))) with hAdef
  have hA : anfDegree A = n - 1 :=
    anfDegree_point_pair hn huv c0 (coeff_weight_le hn ih l m) hform
  have h0 : ∀ y, assocPhase (BitVec.cons L l) (BitVec.cons M m) (BitVec.cons false y) = A y := by
    intro y
    rw [assocPhase_cons]
    simp [hAdef]
  have h1 : ∀ y, assocPhase (BitVec.cons L l) (BitVec.cons M m) (BitVec.cons true y) =
      (assocPhase (BitVec.cons L l) (BitVec.cons M m) (BitVec.cons false y) ^^
        (decide (l ≠ 0#n) ^^ decide (m ≠ 0#n) ^^ decide (l ^^^ m ≠ 0#n))) := by
    intro y
    rw [assocPhase_cons, assocPhase_cons, commPhase_xor_triple]
    simp
  rw [anfDegree_lift _ (by rw [hA]; omega) h0 h1, hA]



theorem cons_false_ne_zero {n : ℕ} {x : BitVec n} (h : BitVec.cons false x ≠ 0#(n + 1)) :
    x ≠ 0#n := by
  intro hx
  apply h
  subst hx
  simp

theorem ne_xor_of_ne_zero {n : ℕ} {a b : BitVec n} (hb : b ≠ 0#n) : a ≠ a ^^^ b := by
  intro h
  apply hb
  have key : a ^^^ (a ^^^ b) = b := by
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  rw [← h, BitVec.xor_self] at key
  exact key.symm

theorem assocDegree_step {n : ℕ} (hn : 2 ≤ n) (ih : n = 2 ∨ (3 ≤ n ∧ AssocDegreeAt n)) :
    AssocDegreeAt (n + 1) := by
  intro a b ha hb hab
  obtain ⟨P, p, rfl⟩ : ∃ P p', a = BitVec.cons P p' :=
    ⟨_, _, (BitVec.cons_msb_setWidth a).symm⟩
  obtain ⟨Q, q, rfl⟩ : ∃ Q q', b = BitVec.cons Q q' :=
    ⟨_, _, (BitVec.cons_msb_setWidth b).symm⟩
  cases P <;> cases Q
  · have hp := cons_false_ne_zero ha
    have hq := cons_false_ne_zero hb
    have hpq : p ≠ q := fun h => hab (by rw [h])
    have hdeg : assocDegree (BitVec.cons false p).toNat (BitVec.cons false q).toNat =
        assocDegree p.toNat q.toNat := by
      simp [assocDegree]
    rw [hdeg]
    rcases ih with rfl | ⟨h3, ih⟩
    · have hp' : p.toNat ≠ 0 := fun h => hp (BitVec.eq_of_toNat_eq (by simpa using h))
      have hm : max p.toNat q.toNat < 4 := max_lt p.isLt q.isLt
      have hm0 : max p.toNat q.toNat ≠ 0 := by omega
      have hl := (Nat.log2_lt hm0).2 (show max p.toNat q.toNat < 2 ^ 2 from hm)
      have hd : assocDegree p.toNat q.toNat = 1 := by
        unfold assocDegree
        omega
      rw [hd]
      refine anfDegree_lift_zero (fun y => ?_) (fun y => ?_)
      · rw [assocPhase_cons]
        simp [assocPhase_two]
      · rw [assocPhase_cons, commPhase_xor_triple, pairCoeff_eq_true hp hq hpq]
        simp [assocPhase_two]
    · have hd1 : 1 ≤ anfDegree (assocPhase p q) := by
        rw [ih p q hp hq hpq]
        exact le_max_left _ _
      refine (anfDegree_lift true hd1 (fun y => ?_) (fun y => ?_)).trans (ih p q hp hq hpq)
      · rw [assocPhase_cons]
        simp
      · rw [assocPhase_cons, assocPhase_cons, commPhase_xor_triple, pairCoeff_eq_true hp hq hpq]
        simp
  · have hp := cons_false_ne_zero ha
    have hle : (BitVec.cons false p).toNat ≤ (BitVec.cons true q).toNat := by
      rw [toNat_cons_false', toNat_cons_true']
      have := p.isLt
      omega
    have hdeg : assocDegree (BitVec.cons false p).toNat (BitVec.cons true q).toNat = n - 1 := by
      unfold assocDegree
      rw [max_eq_right hle, log2_cons_true]
      omega
    rw [hdeg]
    refine anfDegree_assocPhase_top hn ih false true p q q (q ^^^ p)
      (ne_xor_of_ne_zero hp) (decide (q = 0#n) ^^ decide (q = p)) fun y => ?_
    have hp' : decide (p ≠ 0#n) = true := decide_eq_true hp
    simp only [Bool.false_and, Bool.true_and, Bool.xor_false, commPhase_eq_xor, decide_xor_eq_zero,
      hp']
    simp only [decide_xor_eq]
    generalize assocPhase p q y = g
    generalize decide (q = 0#n) = a1
    generalize decide (q = p) = a2
    generalize decide (y = q) = a3
    generalize decide (y = q ^^^ p) = a4
    revert g a1 a2 a3 a4
    decide
  · have hq := cons_false_ne_zero hb
    have hle : (BitVec.cons false q).toNat ≤ (BitVec.cons true p).toNat := by
      rw [toNat_cons_false', toNat_cons_true']
      have := q.isLt
      omega
    have hdeg : assocDegree (BitVec.cons true p).toNat (BitVec.cons false q).toNat = n - 1 := by
      unfold assocDegree
      rw [max_eq_left hle, log2_cons_true]
      omega
    rw [hdeg]
    refine anfDegree_assocPhase_top hn ih true false p q 0#n q hq.symm true fun y => ?_
    have hq' : decide (q = 0#n) = false := decide_eq_false hq
    simp only [Bool.false_and, Bool.true_and, Bool.xor_false, ne_eq, decide_not,
      decide_xor_eq_zero, hq']
    generalize assocPhase p q y = g
    generalize decide (y = 0#n) = a1
    generalize decide (y = q) = a2
    revert g a1 a2
    decide
  · have hpq : p ≠ q := fun h => hab (by rw [h])
    have hdeg : assocDegree (BitVec.cons true p).toNat (BitVec.cons true q).toNat = n - 1 := by
      unfold assocDegree
      have hl : Nat.log2 (max (BitVec.cons true p).toNat (BitVec.cons true q).toNat) = n := by
        rcases le_total (BitVec.cons true p).toNat (BitVec.cons true q).toNat with h | h
        · rw [max_eq_right h, log2_cons_true]
        · rw [max_eq_left h, log2_cons_true]
      rw [hl]
      omega
    rw [hdeg]
    have hv : (0#n) ≠ q ^^^ p := fun h => hpq (BitVec.xor_eq_zero_iff.1 h.symm).symm
    refine anfDegree_assocPhase_top hn ih true true p q 0#n (q ^^^ p) hv
      (true ^^ decide (q = p)) fun y => ?_
    simp only [Bool.true_and, ne_eq, decide_not, commPhase_eq_xor, decide_xor_eq_zero]
    simp only [decide_xor_eq]
    generalize assocPhase p q y = g
    generalize decide (p = 0#n) = a0
    generalize decide (q = 0#n) = a1
    generalize decide (q = p) = a2
    generalize decide (y = 0#n) = a3
    generalize decide (y = q) = a4
    generalize decide (y = q ^^^ p) = a5
    revert g a0 a1 a2 a3 a4 a5
    decide

theorem assocDegreeAt_of_le {k : ℕ} (hk : 3 ≤ k) : AssocDegreeAt k := by
  induction k, hk using Nat.le_induction with
  | base => exact assocDegree_step (le_refl 2) (Or.inl rfl)
  | succ n hn ih => exact assocDegree_step (by omega) (Or.inr ⟨hn, ih⟩)

end DegreeSteps

/-- For `k ≥ 3` and distinct nonzero `p`, `q` the associator phase has algebraic degree
`max 1 (bitlen (max p q) - 2)`, independent of `k`, where `bitlen n - 2 = Nat.log2 n - 1` for
`n ≥ 1`. The Rocq original is `assoc_degree_is` of `rocq/quantum/CdAssociatorAnf.v`
(`degree_is k (assoc k p q) (assoc_degree p q)`, whose `assoc k p q x` is `assocPhase` at
`p.toNat`, `q.toNat`, `x.toNat`). The proof inducts on the level: a pair in the low half keeps the
degree of the level below, since the top bit of `x` adds a constant; a pair reaching the top
half adds two distinct point indicators, of degree `k - 2`, to the phase of the low parts, whose
degree is at most `k - 3`. -/
theorem anfDegree_assocPhase {k : ℕ} (hk : 3 ≤ k) {p q : BitVec k} (hp : p ≠ 0#k) (hq : q ≠ 0#k)
    (hpq : p ≠ q) :
    anfDegree (assocPhase p q) = max 1 (Nat.log2 (max p.toNat q.toNat) - 1) :=
  assocDegreeAt_of_le hk p q hp hq hpq

end Tower

end CayleyDickson
