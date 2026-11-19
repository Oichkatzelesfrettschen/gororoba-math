/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Tower
public import GororobaMath.CayleyDickson.AssociatorPhase

/-!
# The Schreier exponent as a coboundary of the sign cochain

Convention: `Tower.negSign k p q` (`GororobaMath.CayleyDickson.Tower`) is the Boolean sign of
`e p * e q = ± e (p ^^^ q)` with indices `p q : BitVec k`, `true` meaning `-1`; the indices form
the group `BitVec k` under `^^^`. `Tower.schreier l r x` is the exponent that the three products
`e l * (e r * e x)`, `(e l * e r) * e x` share beyond the sign of `e l * e r`: the sum of
`negSign r x`, `negSign l (r ^^^ x)` and `negSign (l ^^^ r) x`.

`Tower.signSpan k` is the span over `ZMod 2` of the functions `x ↦ [schreier l r x]` of
`BitVec k → ZMod 2`, where `[b]` is `1` for `b = true` and `0` otherwise (`Tower.boolInd`).

## Main results

* `Tower.mem_signSpan_iff`: at order `k + 3` a function lies in `Tower.signSpan` exactly when it is
  an even-weight function of the `k + 2` low bits plus a multiple of the top bit. The Rocq original
  is `schreier_span_characterization` of `rocq/open/theories/SchreierSignCode.v`, whose
  `sign_span` is the same span as an inductive predicate on Boolean functions closed under
  pointwise xor.
* `Tower.schreier_xor_schreier_zero`: the exponent normalized at `x = 0` is the group coboundary
  `negSign r x + negSign l (r ^^^ x) + negSign (l ^^^ r) x + negSign l r` of the sign cochain
  over the XOR group. The Rocq original is `normalized_schreier_is_coboundary` of
  `rocq/open/theories/BooleanCochainFiltration.v`, which proves it in a section over any group
  and any cochain normalized at the identity; Lean states the instance of the tower cochain on
  `BitVec k`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

/-- The Schreier exponent of the triple `(l, r, x)`. -/
def schreier {k : ℕ} (l r x : BitVec k) : Bool :=
  negSign k r x ^^ negSign k l (r ^^^ x) ^^ negSign k (l ^^^ r) x

/-- The Schreier exponent normalized at `x = 0` is the coboundary of the sign cochain. The Rocq
original is `normalized_schreier_is_coboundary` of
`rocq/open/theories/BooleanCochainFiltration.v`. -/
theorem schreier_xor_schreier_zero {k : ℕ} (l r x : BitVec k) :
    (schreier l r x ^^ schreier l r 0#k) =
      (negSign k r x ^^ negSign k l (r ^^^ x) ^^ negSign k (l ^^^ r) x ^^ negSign k l r) := by
  unfold schreier
  rw [BitVec.xor_zero, negSign_zero_right, negSign_zero_right, Bool.xor_false, Bool.false_xor]

/-! ### Parity of sums over the cube

`Tower.boolInd b` reads a sign `b` as the element `1` of `ZMod 2` when `b` is `true`. Sums of
the signs of a product over one factor are even once the level is at least `2`. -/

/-- The element of `ZMod 2` that a sign `b : Bool` stands for. -/
def boolInd (b : Bool) : ZMod 2 := if b then 1 else 0

theorem boolInd_xor (a b : Bool) : boolInd (a ^^ b) = boolInd a + boolInd b := by
  cases a <;> cases b <;> decide

theorem boolInd_and (a b : Bool) : boolInd (a && b) = boolInd a * boolInd b := by
  cases a <;> cases b <;> decide

theorem boolInd_false : boolInd false = 0 := rfl

theorem boolInd_true : boolInd true = 1 := rfl

/-- A sum over `BitVec (n + 1)` splits by the top bit. -/
theorem sum_bitVec_succ {M : Type*} [AddCommMonoid M] (n : ℕ) (F : BitVec (n + 1) → M) :
    ∑ y, F y = ∑ x : BitVec n, (F (BitVec.cons false x) + F (BitVec.cons true x)) := by
  rw [← (consEquiv n).sum_comp, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [consEquiv, add_comm]

/-- Translation by `m` is a bijection of `BitVec n`. -/
def xorEquiv {n : ℕ} (m : BitVec n) : BitVec n ≃ BitVec n where
  toFun x := m ^^^ x
  invFun x := m ^^^ x
  left_inv x := by simp
  right_inv x := by simp

theorem sum_xor_left {M : Type*} [AddCommMonoid M] {n : ℕ} (m : BitVec n) (F : BitVec n → M) :
    ∑ x, F (m ^^^ x) = ∑ x, F x :=
  (xorEquiv m).sum_comp F

theorem two_nsmul_zmod_two (c : ZMod 2) : 2 • c = 0 := by
  revert c
  decide

/-- A constant summed over `BitVec (n + 1)` is an even multiple of itself. -/
theorem sum_const_succ {n : ℕ} (c : ZMod 2) : ∑ _x : BitVec (n + 1), c = 0 := by
  rw [Finset.sum_const, Finset.card_univ, card_bitVec, pow_succ, mul_comm, mul_smul,
    two_nsmul_zmod_two]

theorem sum_delta {n : ℕ} (u : BitVec n) : ∑ x : BitVec n, boolInd (decide (x = u)) = 1 := by
  simp [boolInd]

theorem sum_ne {n : ℕ} (u : BitVec (n + 1)) :
    ∑ x : BitVec (n + 1), boolInd (decide (x ≠ u)) = 1 := by
  have h : ∀ x : BitVec (n + 1), boolInd (decide (x ≠ u)) = 1 + boolInd (decide (x = u)) := by
    intro x
    simp only [ne_eq, decide_not]
    generalize decide (x = u) = b
    revert b
    decide
  simp_rw [h]
  rw [Finset.sum_add_distrib, sum_delta, sum_const_succ, zero_add]

/-- Over a cube of dimension at least `1` the commutation phases of `a` with every index sum to
an even number. -/
theorem sum_commPhase_even {n : ℕ} (a : BitVec (n + 1)) :
    ∑ x : BitVec (n + 1), boolInd (commPhase a x) = 0 := by
  simp_rw [commPhase_eq_xor, boolInd_xor]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_const_succ, sum_delta, sum_delta]
  decide

/-- Every row of the sign table of level `n + 2` has an even number of negative signs. The Rocq
original is `sign_row_even` of `rocq/open/theories/SchreierSignCode.v`. -/
theorem sum_negSign_even {n : ℕ} (v : BitVec (n + 2)) :
    ∑ x : BitVec (n + 2), boolInd (negSign (n + 2) v x) = 0 := by
  obtain ⟨P, v', rfl⟩ : ∃ P v', v = BitVec.cons P v' :=
    ⟨_, _, (BitVec.cons_msb_setWidth v).symm⟩
  rw [sum_bitVec_succ]
  have h : ∀ x : BitVec (n + 1),
      boolInd (negSign (n + 2) (BitVec.cons P v') (BitVec.cons false x)) +
        boolInd (negSign (n + 2) (BitVec.cons P v') (BitVec.cons true x)) =
      boolInd (commPhase v' x) + boolInd P := by
    intro x
    rw [negSign_cons_eq, negSign_cons_eq]
    simp only [boolInd_xor, boolInd_and, Bool.false_and, Bool.and_false, Bool.and_true,
      boolInd_false, Bool.true_and]
    generalize boolInd (negSign (n + 1) v' x) = a
    generalize boolInd (commPhase v' x) = b
    generalize boolInd (decide (x ≠ 0#(n + 1))) = c
    generalize boolInd P = d
    revert a b c d
    decide
  simp_rw [h]
  rw [Finset.sum_add_distrib, sum_commPhase_even, sum_const_succ, add_zero]

theorem sum_assocPhase_even {n : ℕ} (l m : BitVec (n + 2)) :
    ∑ x : BitVec (n + 2), boolInd (assocPhase l m x) = 0 := by
  simp_rw [assocPhase_eq, boolInd_xor]
  simp only [Finset.sum_add_distrib]
  rw [sum_const_succ, sum_negSign_even, sum_negSign_even,
    sum_xor_left m (fun y => boolInd (negSign (n + 2) l y)), sum_negSign_even]
  decide

theorem schreier_eq_assocPhase {k : ℕ} (l r x : BitVec k) :
    schreier l r x = (assocPhase l r x ^^ negSign k l r) := by
  rw [assocPhase_eq]
  unfold schreier
  generalize negSign k r x = a
  generalize negSign k l (r ^^^ x) = b
  generalize negSign k (l ^^^ r) x = c
  generalize negSign k l r = d
  revert a b c d
  decide

/-- The coefficient of the top bit of `x` in `schreier l r x`: the constant
`[l' ≠ 0] + [m' ≠ 0] + [l' ^^^ m' ≠ 0]` of the two low parts. -/
def topCoeff {k : ℕ} (l r : BitVec (k + 1)) : Bool :=
  decide (l.setWidth k ≠ 0#k) ^^ decide (r.setWidth k ≠ 0#k) ^^
    decide (l.setWidth k ^^^ r.setWidth k ≠ 0#k)

/-- The Schreier exponent at order `k + 1` changes with the top bit of `x` by a constant of
`l` and `r`. -/
theorem schreier_cons_top {k : ℕ} (l r : BitVec (k + 1)) (N : Bool) (x : BitVec k) :
    schreier l r (BitVec.cons N x) =
      (schreier l r (BitVec.cons false x) ^^ (N && topCoeff l r)) := by
  obtain ⟨L, l', rfl⟩ : ∃ L l', l = BitVec.cons L l' := ⟨_, _, (BitVec.cons_msb_setWidth l).symm⟩
  obtain ⟨M, m', rfl⟩ : ∃ M m', r = BitVec.cons M m' := ⟨_, _, (BitVec.cons_msb_setWidth r).symm⟩
  rw [schreier_eq_assocPhase, schreier_eq_assocPhase, assocPhase_cons, assocPhase_cons,
    topCoeff, commPhase_xor_triple]
  simp only [BitVec.setWidth_cons, ne_eq, decide_not]
  generalize assocPhase l' m' x = e1
  generalize negSign (k + 1) (BitVec.cons L l') (BitVec.cons M m') = s
  generalize commPhase l' m' = e2
  generalize commPhase l' (m' ^^^ x) = e3
  generalize decide (m' = 0#k) = b
  generalize decide (x = 0#k) = e4
  generalize decide (m' ^^^ x = 0#k) = e5
  generalize decide (l' = 0#k) = a
  generalize decide (l' ^^^ m' = 0#k) = e6
  revert L M N e1 s e2 e3 b e4 e5 a e6
  decide

/-- Over the lower half of the cube the Schreier exponent has an even number of negative signs.
The Rocq original is `schreier_low_even` of `rocq/open/theories/SchreierSignCode.v`. -/
theorem sum_schreier_low_even {n : ℕ} (l r : BitVec (n + 3)) :
    ∑ x : BitVec (n + 2), boolInd (schreier l r (BitVec.cons false x)) = 0 := by
  obtain ⟨L, l', rfl⟩ : ∃ L l', l = BitVec.cons L l' := ⟨_, _, (BitVec.cons_msb_setWidth l).symm⟩
  obtain ⟨M, m', rfl⟩ : ∃ M m', r = BitVec.cons M m' := ⟨_, _, (BitVec.cons_msb_setWidth r).symm⟩
  simp_rw [schreier_eq_assocPhase, assocPhase_cons, boolInd_xor, boolInd_and]
  have hx : ∑ x : BitVec (n + 2), boolInd (decide (m' ^^^ x ≠ 0#(n + 2))) = 1 := by
    rw [sum_xor_left m' (fun y => boolInd (decide (y ≠ 0#(n + 2))))]
    exact sum_ne _
  have hc : ∑ x : BitVec (n + 2), boolInd (commPhase l' (m' ^^^ x)) = 0 := by
    rw [sum_xor_left m' (fun y => boolInd (commPhase l' y))]
    exact sum_commPhase_even _
  simp only [boolInd_xor, Finset.sum_add_distrib, ← Finset.mul_sum, sum_assocPhase_even,
    sum_const_succ, hx, hc, sum_ne, boolInd_false, zero_mul, Finset.sum_const_zero]
  generalize boolInd L = a
  generalize boolInd M = b
  revert a b
  decide

theorem assocPhase_zero_left {k : ℕ} (t x : BitVec k) : assocPhase (0#k) t x = false := by
  rw [assocPhase_eq, BitVec.zero_xor, negSign_zero_left, negSign_zero_left]
  cases negSign k t x <;> rfl

/-- The Schreier exponent of `e (cons true 0)`, `e (cons false t)` and `e (cons h i)` does not
depend on `h`: it is the indicator of `i = 0` plus that of `i = t`. The Rocq original is
`schreier_delta_pair` of `rocq/open/theories/SchreierSignCode.v`. -/
theorem schreier_delta {w : ℕ} (t i : BitVec w) (h : Bool) :
    schreier (BitVec.cons true (0#w)) (BitVec.cons false t) (BitVec.cons h i) =
      (decide (i = 0#w) ^^ decide (i = t)) := by
  rw [schreier_eq_assocPhase, assocPhase_cons, negSign_cons_eq, assocPhase_zero_left,
    BitVec.zero_xor, commPhase_eq]
  have h2 : decide (t ^^^ i = 0#w) = decide (i = t) := decide_xor_eq_zero t i
  simp only [ne_eq, decide_not, h2, negSign_zero_left, Bool.false_and, Bool.true_and,
    commPhase_eq, not_true_eq_false, false_and, decide_false, Bool.false_xor, Bool.xor_false]
  generalize decide (t = 0#w) = a
  generalize decide (i = 0#w) = b
  generalize decide (i = t) = c
  generalize decide (¬t = 0#w ∧ ¬i = 0#w ∧ ¬t = i) = e
  revert a b c e h
  decide

/-- The Schreier sign span of order `k`: the `ZMod 2`-span of the functions `x ↦ schreier l r x`.
The Rocq original is `sign_span` of `rocq/open/theories/SchreierSignCode.v`, an inductive
predicate on Boolean functions closed under pointwise xor. -/
def signSpan (k : ℕ) : Submodule (ZMod 2) (BitVec k → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range fun lr : BitVec k × BitVec k =>
    fun x => if schreier lr.1 lr.2 x then (1 : ZMod 2) else 0)

/-- The functions of order `k + 3` that are an even-weight function of the low bits plus a
multiple of the top bit. -/
def signCode (k : ℕ) : Submodule (ZMod 2) (BitVec (k + 3) → ZMod 2) where
  carrier := {f | ∃ (g : BitVec (k + 2) → ZMod 2) (c : ZMod 2), ∑ y, g y = 0 ∧
    ∀ x, f x = g (x.setWidth (k + 2)) + c * (if x.msb then 1 else 0)}
  zero_mem' := ⟨0, 0, by simp, fun x => by simp⟩
  add_mem' := by
    rintro f₁ f₂ ⟨g₁, c₁, h₁, e₁⟩ ⟨g₂, c₂, h₂, e₂⟩
    refine ⟨g₁ + g₂, c₁ + c₂, by simp [Finset.sum_add_distrib, h₁, h₂], fun x => ?_⟩
    simp only [Pi.add_apply, e₁, e₂]
    ring
  smul_mem' := by
    rintro a f ⟨g, c, h, e⟩
    refine ⟨a • g, a * c, ?_, fun x => ?_⟩
    · simp [← Finset.mul_sum, h]
    · simp only [Pi.smul_apply, smul_eq_mul, e]
      ring

theorem mem_signCode {k : ℕ} {f : BitVec (k + 3) → ZMod 2} :
    f ∈ signCode k ↔ ∃ (g : BitVec (k + 2) → ZMod 2) (c : ZMod 2), ∑ y, g y = 0 ∧
      ∀ x, f x = g (x.setWidth (k + 2)) + c * (if x.msb then 1 else 0) := Iff.rfl

theorem schreier_generator_mem_signCode {k : ℕ} (l r : BitVec (k + 3)) :
    (fun x => if schreier l r x then (1 : ZMod 2) else 0) ∈ signCode k := by
  refine ⟨fun x' => boolInd (schreier l r (BitVec.cons false x')), boolInd (topCoeff l r),
    sum_schreier_low_even l r, fun x => ?_⟩
  have h := schreier_cons_top l r x.msb (x.setWidth (k + 2))
  rw [BitVec.cons_msb_setWidth] at h
  change boolInd (schreier l r x) = _
  rw [h, boolInd_xor, boolInd_and]
  generalize x.msb = N
  cases N <;> simp [boolInd]

theorem signSpan_le_signCode (k : ℕ) : signSpan (k + 3) ≤ signCode k :=
  Submodule.span_le.2 (by
    rintro _ ⟨lr, rfl⟩
    exact schreier_generator_mem_signCode lr.1 lr.2)

/-- An even-weight function of the low bits is in the span: it is the sum of the generators
`schreier (cons true 0) (cons false t)` weighted by its values. The Rocq original is
`even_lower_in_span` of `rocq/open/theories/SchreierSignCode.v`. -/
theorem lowFunction_mem_signSpan {k : ℕ} (g : BitVec (k + 2) → ZMod 2) (hg : ∑ y, g y = 0) :
    (fun x : BitVec (k + 3) => g (x.setWidth (k + 2))) ∈ signSpan (k + 3) := by
  have hsum : (fun x : BitVec (k + 3) => g (x.setWidth (k + 2))) =
      ∑ t, g t • (fun x : BitVec (k + 3) => if schreier (BitVec.cons true (0#(k + 2)))
        (BitVec.cons false t) x then (1 : ZMod 2) else 0) := by
    funext x
    have h := fun t => schreier_delta t (x.setWidth (k + 2)) x.msb
    simp only [BitVec.cons_msb_setWidth] at h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h]
    have e : ∀ t : BitVec (k + 2), g t * (if (decide (x.setWidth (k + 2) = 0#(k + 2)) ^^
        decide (x.setWidth (k + 2) = t)) then (1 : ZMod 2) else 0) =
        boolInd (decide (x.setWidth (k + 2) = 0#(k + 2))) * g t +
          (if x.setWidth (k + 2) = t then g t else 0) := by
      intro t
      generalize decide (x.setWidth (k + 2) = 0#(k + 2)) = a
      by_cases ht : x.setWidth (k + 2) = t
      · cases a <;> simp [boolInd, ht, CharTwo.add_self_eq_zero]
      · cases a <;> simp [boolInd, ht]
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, hg, mul_zero, zero_add,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hsum]
  exact Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _
    (Submodule.subset_span ⟨(BitVec.cons true (0#(k + 2)), BitVec.cons false t), rfl⟩)

theorem msb_mem_signSpan (k : ℕ) :
    (fun x : BitVec (k + 3) => if x.msb then (1 : ZMod 2) else 0) ∈ signSpan (k + 3) := by
  -- two nonzero distinct low parts give the top-bit coefficient `1`
  set l' : BitVec (k + 2) := BitVec.cons true (0#(k + 1)) with hl'
  set m' : BitVec (k + 2) := BitVec.cons false (BitVec.cons true (0#k)) with hm'
  have hl0 : l' ≠ 0#(k + 2) := by
    intro h
    have := congrArg BitVec.msb h
    simp [hl'] at this
  have hm0 : m' ≠ 0#(k + 2) := by
    intro h
    have := congrArg (BitVec.setWidth (k + 1)) h
    simp [hm'] at this
  have hlm : l' ≠ m' := by
    intro h
    have := congrArg BitVec.msb h
    simp [hl', hm'] at this
  set l : BitVec (k + 3) := BitVec.cons false l'
  set r : BitVec (k + 3) := BitVec.cons false m'
  have hc : topCoeff l r = true := by
    simp only [topCoeff, l, r, BitVec.setWidth_cons]
    exact pairCoeff_eq_true hl0 hm0 hlm
  have hg : (fun x : BitVec (k + 3) =>
      boolInd (schreier l r (BitVec.cons false (x.setWidth (k + 2))))) ∈ signSpan (k + 3) :=
    lowFunction_mem_signSpan _ (sum_schreier_low_even l r)
  have hs : (fun x : BitVec (k + 3) => if schreier l r x then (1 : ZMod 2) else 0) ∈
      signSpan (k + 3) := Submodule.subset_span ⟨(l, r), rfl⟩
  have hsum := Submodule.add_mem _ hs hg
  convert hsum using 1
  funext x
  have h := schreier_cons_top l r x.msb (x.setWidth (k + 2))
  rw [BitVec.cons_msb_setWidth, hc] at h
  change _ = boolInd (schreier l r x) +
    boolInd (schreier l r (BitVec.cons false (x.setWidth (k + 2))))
  rw [h, boolInd_xor, boolInd_and]
  generalize x.msb = N
  generalize boolInd (schreier l r (BitVec.cons false (x.setWidth (k + 2)))) = a
  cases N <;> revert a <;> decide

theorem signCode_le_signSpan (k : ℕ) : signCode k ≤ signSpan (k + 3) := by
  rintro f ⟨g, c, hg, hf⟩
  have hfun : f = (fun x : BitVec (k + 3) => g (x.setWidth (k + 2))) +
      c • (fun x : BitVec (k + 3) => if x.msb then (1 : ZMod 2) else 0) := by
    funext x
    simp [hf x]
  rw [hfun]
  exact Submodule.add_mem _ (lowFunction_mem_signSpan g hg)
    (Submodule.smul_mem _ _ (msb_mem_signSpan k))

theorem signSpan_eq_signCode (k : ℕ) : signSpan (k + 3) = signCode k :=
  le_antisymm (signSpan_le_signCode k) (signCode_le_signSpan k)

/-- At order `k + 3` the Schreier sign span is the set of even-weight functions of the lower
bits plus a multiple of the top bit. The Rocq original is `schreier_span_characterization` of
`rocq/open/theories/SchreierSignCode.v`, whose `sign_span` is the same span as an inductive
predicate on Boolean functions. -/
theorem mem_signSpan_iff {k : ℕ} (f : BitVec (k + 3) → ZMod 2) :
    f ∈ signSpan (k + 3) ↔ ∃ (g : BitVec (k + 2) → ZMod 2) (c : ZMod 2), ∑ y, g y = 0 ∧
      ∀ x, f x = g (x.setWidth (k + 2)) + c * (if x.msb then 1 else 0) := by
  rw [signSpan_eq_signCode]
  exact mem_signCode

section Cardinality

open Module

/-- The map `(g, c) ↦ (x ↦ g (x.setWidth (k + 2)) + c * [x.msb])` of the code parameters to the
functions of order `k + 3`. -/
def codeMap (k : ℕ) : ((BitVec (k + 2) → ZMod 2) × ZMod 2) →ₗ[ZMod 2] (BitVec (k + 3) → ZMod 2) :=
  (LinearMap.funLeft (ZMod 2) (ZMod 2) (fun x : BitVec (k + 3) => x.setWidth (k + 2))).comp
      (LinearMap.fst (ZMod 2) _ _) +
    (LinearMap.toSpanSingleton (ZMod 2) (BitVec (k + 3) → ZMod 2)
      (fun x => if x.msb then (1 : ZMod 2) else 0)).comp (LinearMap.snd (ZMod 2) _ _)

theorem codeMap_apply {k : ℕ} (p : (BitVec (k + 2) → ZMod 2) × ZMod 2) (x : BitVec (k + 3)) :
    codeMap k p x = p.1 (x.setWidth (k + 2)) + p.2 * (if x.msb then 1 else 0) := by
  simp [codeMap]

/-- The values of a function of the low bits at `0` and its sum. -/
def valueSum (k : ℕ) : (BitVec (k + 2) → ZMod 2) →ₗ[ZMod 2] ZMod 2 × ZMod 2 :=
  (LinearMap.proj (0#(k + 2))).prod (∑ y, LinearMap.proj y)

theorem valueSum_apply {k : ℕ} (g : BitVec (k + 2) → ZMod 2) :
    valueSum k g = (g 0#(k + 2), ∑ y, g y) := by
  simp [valueSum]

theorem valueSum_surjective (k : ℕ) : Function.Surjective (valueSum k) := by
  have he : BitVec.cons true (0#(k + 1)) ≠ 0#(k + 2) := by
    intro h
    have := congrArg BitVec.msb h
    simp at this
  rintro ⟨a, b⟩
  refine ⟨Pi.single 0#(k + 2) a + Pi.single (BitVec.cons true (0#(k + 1))) (b - a), ?_⟩
  rw [valueSum_apply]
  simp [Finset.sum_add_distrib, Pi.single_apply]

theorem finrank_ker_valueSum (k : ℕ) :
    finrank (ZMod 2) (LinearMap.ker (valueSum k)) = 2 ^ (k + 2) - 2 := by
  have h := LinearMap.finrank_range_add_finrank_ker (valueSum k)
  rw [LinearMap.range_eq_top.2 (valueSum_surjective k), finrank_top, Module.finrank_prod,
    Module.finrank_self, Module.finrank_fintype_fun_eq_card, card_bitVec] at h
  omega

theorem codeMap_injective (k : ℕ) : Function.Injective (codeMap k) := by
  intro p q h
  have h1 : ∀ x' : BitVec (k + 2), p.1 x' = q.1 x' := fun x' => by
    have := congrFun h (BitVec.cons false x')
    simpa [codeMap_apply] using this
  have h2 := congrFun h (BitVec.cons true (0#(k + 2)))
  simp only [codeMap_apply, BitVec.setWidth_cons, BitVec.msb_cons, ite_true, mul_one] at h2
  rw [h1] at h2
  exact Prod.ext (funext h1) (add_left_cancel h2)

/-- The normalized Schreier span of order `k + 3` has `2 ^ (2 ^ (k + 2) - 1)` elements. The Rocq
original is `normalized_code_cardinality` of `rocq/open/theories/SignCodeCardinality.v`, which
counts a duplicate-free list of tables; Lean counts the elements of the submodule with
`Nat.card`. -/
theorem card_normalizedSignSpan (k : ℕ) :
    Nat.card (signSpan (k + 3) ⊓
      LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : BitVec (k + 3) => ZMod 2)
        0#(k + 3)) : Submodule (ZMod 2) (BitVec (k + 3) → ZMod 2)) = 2 ^ (2 ^ (k + 2) - 1) := by
  set S : Submodule (ZMod 2) (BitVec (k + 3) → ZMod 2) := signSpan (k + 3) ⊓
    LinearMap.ker (LinearMap.proj (R := ZMod 2) (φ := fun _ : BitVec (k + 3) => ZMod 2) 0#(k + 3))
    with hS
  let Γ : (LinearMap.ker (valueSum k) × ZMod 2) →ₗ[ZMod 2] (BitVec (k + 3) → ZMod 2) :=
    (codeMap k).comp ((LinearMap.ker (valueSum k)).subtype.prodMap LinearMap.id)
  have hinj : Function.Injective Γ := by
    intro a b h
    have := codeMap_injective k h
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 this
    exact Prod.ext (Subtype.ext h1) h2
  have hrange : LinearMap.range Γ = S := by
    ext f
    simp only [hS, LinearMap.mem_range, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply]
    constructor
    · rintro ⟨⟨⟨g, hg⟩, c⟩, rfl⟩
      rw [LinearMap.mem_ker, valueSum_apply, Prod.mk_eq_zero] at hg
      refine ⟨(mem_signSpan_iff _).2 ⟨g, c, hg.2, fun x => codeMap_apply _ x⟩, ?_⟩
      simp [Γ, codeMap_apply, hg.1]
    · rintro ⟨hs, h0⟩
      obtain ⟨g, c, hsum, hf⟩ := (mem_signSpan_iff f).1 hs
      have hg0 : g 0#(k + 2) = 0 := by
        have := hf 0#(k + 3)
        simpa [h0] using this.symm
      refine ⟨⟨⟨g, ?_⟩, c⟩, ?_⟩
      · rw [LinearMap.mem_ker, valueSum_apply, hg0, hsum]
        rfl
      · funext x
        simp [Γ, codeMap_apply, hf x]
  have hfin : Module.finrank (ZMod 2) S = 2 ^ (k + 2) - 1 := by
    rw [← hrange, LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_self,
      finrank_ker_valueSum]
    have : 4 ≤ 2 ^ (k + 2) := by
      rw [pow_add]
      have := Nat.one_le_two_pow (n := k)
      omega
    omega
  have : Fintype S := Fintype.ofFinite S
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := S), hfin,
    ZMod.card]

end Cardinality

end Tower

end CayleyDickson
