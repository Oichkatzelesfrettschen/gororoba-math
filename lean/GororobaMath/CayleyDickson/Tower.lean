/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Basic

/-!
# The Cayley-Dickson tower and its basis signs

`Tower R k` is the `k`-fold Cayley-Dickson double of `R`, with the `2 ^ k`
basis elements `Tower.e R k p`: `Tower R 2` is the quaternion algebra, `Tower R 3` the octonions,
`Tower R 4` the sedenions and `Tower R 5` the 32-dimensional algebra that
gororoba-quantum calls `A_5` (`CayleyDickson.Pathion`).

The basis element `e k p` is indexed by a bit vector `p : BitVec k`, most
significant bit outermost: bit `k` of the index selects the second half of
the `(k + 1)`-st double. `p.toNat` is the integer index of `cd_core.cd_sign`
and `BitVec.toNat_xor` carries the index law below to integers.

## Main results

* `Tower.e_mul_e`: `e k p * e k q = ± e k (p ^^^ q)` with the sign
  `Tower.negSign k p q`, the recursion of `cd_core.cd_sign` on the top bit.
* `Tower.star_e`: `star (e k p)` is `e k p` for `p = 0` and `-e k p`
  otherwise.
* `Tower.e_mul_self`: `e k p * e k p = -1` for `p ≠ 0`.
* `Tower.negSign_xor_right`: the sign of `e k p * e k (p ^^^ q)` is that of
  `e k p * e k q`, reversed for `p ≠ 0`, the basis form of
  `e p * (e p * e q) = -e q`; `Tower.negSign_swap_xor` gives the sign of the
  reversed product, and `Tower.negSign_cons` writes every sign of level
  `k + 1` as a sign of level `k` with top-bit corrections.
-/

@[expose] public section

namespace CayleyDickson

universe u

/-- The `k`-fold Cayley-Dickson double of `R`. -/
def Tower (R : Type u) : ℕ → Type u
  | 0 => R
  | k + 1 => CayleyDickson (Tower R k)

namespace Tower

variable (R : Type u) [NonAssocRing R] [StarRing R]

/-- The ring and star structures of every level, built together because the
star structure of level `k + 1` is stated over the ring structure of
level `k`. -/
def levelStructure : (k : ℕ) → Σ' _ : NonAssocRing (Tower R k), StarRing (Tower R k)
  | 0 => ⟨inferInstanceAs (NonAssocRing R), inferInstanceAs (StarRing R)⟩
  | k + 1 =>
    ⟨@CayleyDickson.instNonAssocRing _ (levelStructure k).1 (levelStructure k).2,
      @CayleyDickson.instStarRing _ (levelStructure k).1 (levelStructure k).2⟩

instance instNonAssocRing (k : ℕ) : NonAssocRing (Tower R k) := (levelStructure R k).1

instance instStarRing (k : ℕ) : StarRing (Tower R k) := (levelStructure R k).2

variable {R}

/-- The element `(a, b)` of level `k + 1`. -/
def mk {k : ℕ} (a b : Tower R k) : Tower R (k + 1) := CayleyDickson.mk a b

theorem mk_mul_mk {k : ℕ} (a b c d : Tower R k) :
    mk a b * mk c d = mk (a * c - star d * b) (d * a + b * star c) := rfl

theorem star_mk {k : ℕ} (a b : Tower R k) : star (mk a b) = mk (star a) (-b) := rfl

theorem neg_mk {k : ℕ} (a b : Tower R k) : -mk a b = mk (-a) (-b) := rfl

theorem one_eq_mk (k : ℕ) : (1 : Tower R (k + 1)) = mk 1 0 := rfl

theorem zero_eq_mk (k : ℕ) : (0 : Tower R (k + 1)) = mk 0 0 := rfl

omit [NonAssocRing R] [StarRing R] in
theorem mk_inj {k : ℕ} {a b c d : Tower R k} : mk a b = mk c d ↔ a = c ∧ b = d :=
  CayleyDickson.ext_iff

variable (R) in
/-- The basis element of index `p`. The top bit of `p` selects the half of
the outermost double; the remaining bits index the level below. -/
def e : (k : ℕ) → BitVec k → Tower R k
  | 0, _ => (1 : Tower R 0)
  | k + 1, p =>
    if p.msb then mk 0 (e k (p.setWidth k)) else mk (e k (p.setWidth k)) 0

/-- `true` when `e k p * e k q = -e k (p ^^^ q)`. The four branches are the
four top-bit cases of `cd_core.cd_sign`. -/
def negSign : (k : ℕ) → BitVec k → BitVec k → Bool
  | 0, _, _ => false
  | k + 1, p, q =>
    match p.msb, q.msb with
    | false, false => negSign k (p.setWidth k) (q.setWidth k)
    | false, true => negSign k (q.setWidth k) (p.setWidth k)
    | true, false =>
      xor (decide (q.setWidth k ≠ 0#k)) (negSign k (p.setWidth k) (q.setWidth k))
    | true, true =>
      if q.setWidth k = 0#k then true else negSign k (q.setWidth k) (p.setWidth k)

/-- The sign of `e k p * e k q` as an integer, `cd_core.cd_sign`. -/
def sign (k : ℕ) (p q : BitVec k) : ℤ := if negSign k p q then -1 else 1

@[simp] theorem e_zero_level (p : BitVec 0) : e R 0 p = 1 := rfl

theorem e_succ_of_msb {k : ℕ} {p : BitVec (k + 1)} (h : p.msb = true) :
    e R (k + 1) p = mk 0 (e R k (p.setWidth k)) := by
  simp [e, h]

theorem e_succ_of_not_msb {k : ℕ} {p : BitVec (k + 1)} (h : p.msb = false) :
    e R (k + 1) p = mk (e R k (p.setWidth k)) 0 := by
  simp [e, h]

/-- The basis element of index `0` is `1`. -/
@[simp] theorem e_zero : ∀ k : ℕ, e R k 0#k = 1
  | 0 => rfl
  | k + 1 => by
    rw [e_succ_of_not_msb (by simp), BitVec.setWidth_zero, e_zero k, one_eq_mk]

theorem setWidth_eq_zero_iff {k : ℕ} {p : BitVec (k + 1)} (h : p.msb = false) :
    p.setWidth k = 0#k ↔ p = 0#(k + 1) := by
  constructor
  · intro hz
    rw [← BitVec.cons_msb_setWidth p, h, hz]
    apply BitVec.eq_of_toNat_eq
    simp
  · rintro rfl
    simp

theorem ne_zero_of_msb {k : ℕ} {p : BitVec (k + 1)} (h : p.msb = true) : p ≠ 0#(k + 1) := by
  rintro rfl
  simp at h

theorem negSign_of_not_msb_of_not_msb {k : ℕ} {p q : BitVec (k + 1)}
    (hp : p.msb = false) (hq : q.msb = false) :
    negSign (k + 1) p q = negSign k (p.setWidth k) (q.setWidth k) := by
  simp [negSign, hp, hq]

theorem negSign_of_not_msb_of_msb {k : ℕ} {p q : BitVec (k + 1)}
    (hp : p.msb = false) (hq : q.msb = true) :
    negSign (k + 1) p q = negSign k (q.setWidth k) (p.setWidth k) := by
  simp [negSign, hp, hq]

theorem negSign_of_msb_of_not_msb {k : ℕ} {p q : BitVec (k + 1)}
    (hp : p.msb = true) (hq : q.msb = false) :
    negSign (k + 1) p q =
      xor (decide (q.setWidth k ≠ 0#k)) (negSign k (p.setWidth k) (q.setWidth k)) := by
  simp [negSign, hp, hq]

theorem negSign_of_msb_of_msb {k : ℕ} {p q : BitVec (k + 1)}
    (hp : p.msb = true) (hq : q.msb = true) :
    negSign (k + 1) p q =
      if q.setWidth k = 0#k then true else negSign k (q.setWidth k) (p.setWidth k) := by
  simp [negSign, hp, hq]

/-- Right multiplication by `1 = e k 0` carries no sign. -/
theorem negSign_zero_right : ∀ (k : ℕ) (p : BitVec k), negSign k p 0#k = false
  | 0, _ => rfl
  | k + 1, p => by
    have hq : (0#(k + 1)).msb = false := by simp
    have hz : BitVec.setWidth k 0#(k + 1) = 0#k := by simp
    cases hp : p.msb
    · rw [negSign_of_not_msb_of_not_msb hp hq, hz, negSign_zero_right k]
    · rw [negSign_of_msb_of_not_msb hp hq, hz, negSign_zero_right k]
      simp

/-- Left multiplication by `1 = e k 0` carries no sign. -/
theorem negSign_zero_left : ∀ (k : ℕ) (q : BitVec k), negSign k 0#k q = false
  | 0, _ => rfl
  | k + 1, q => by
    have hp : (0#(k + 1)).msb = false := by simp
    have hz : BitVec.setWidth k 0#(k + 1) = 0#k := by simp
    cases hq : q.msb
    · rw [negSign_of_not_msb_of_not_msb hp hq, hz, negSign_zero_left k]
    · rw [negSign_of_not_msb_of_msb hp hq, hz, negSign_zero_right k]

/-- Conjugation fixes `e k 0 = 1` and negates every other basis element. -/
theorem star_e : ∀ (k : ℕ) (p : BitVec k),
    star (e R k p) = if p = 0#k then e R k p else -e R k p
  | 0, p => by
    have hp : p = 0#0 := Subsingleton.elim _ _
    simp [hp]
  | k + 1, p => by
    cases h : p.msb
    · rw [e_succ_of_not_msb h, star_mk, star_e k, neg_zero]
      simp only [setWidth_eq_zero_iff h]
      split_ifs
      · rfl
      · rw [neg_mk, neg_zero]
    · have hne := ne_zero_of_msb h
      rw [e_succ_of_msb h, star_mk, star_zero]
      simp [hne, neg_mk]

/-- The product of two basis elements is a basis element up to sign: the
index is the bitwise exclusive or and the sign is `negSign`. -/
theorem e_mul_e : ∀ (k : ℕ) (p q : BitVec k),
    e R k p * e R k q = if negSign k p q then -e R k (p ^^^ q) else e R k (p ^^^ q)
  | 0, p, q => by simp [negSign]
  | k + 1, p, q => by
    have hx : (p ^^^ q).setWidth k = p.setWidth k ^^^ q.setWidth k := BitVec.setWidth_xor
    cases hp : p.msb <;> cases hq : q.msb
    · have hm : (p ^^^ q).msb = false := by simp [hp, hq]
      rw [e_succ_of_not_msb hp, e_succ_of_not_msb hq, e_succ_of_not_msb hm, hx, mk_mul_mk,
        negSign_of_not_msb_of_not_msb hp hq, e_mul_e k]
      simp only [star_zero, zero_mul, mul_zero, sub_zero, add_zero]
      split_ifs
      · rw [neg_mk, neg_zero]
      · rfl
    · have hm : (p ^^^ q).msb = true := by simp [hp, hq]
      rw [e_succ_of_not_msb hp, e_succ_of_msb hq, e_succ_of_msb hm, hx, mk_mul_mk,
        negSign_of_not_msb_of_msb hp hq, e_mul_e k, BitVec.xor_comm (q.setWidth k)]
      simp only [star_zero, mul_zero, sub_zero, add_zero]
      split_ifs
      · rw [neg_mk, neg_zero]
      · rfl
    · have hm : (p ^^^ q).msb = true := by simp [hp, hq]
      rw [e_succ_of_msb hp, e_succ_of_not_msb hq, e_succ_of_msb hm, hx, mk_mul_mk,
        negSign_of_msb_of_not_msb hp hq, star_e k]
      simp only [star_zero, zero_mul, mul_zero, sub_zero, zero_add]
      by_cases hz : q.setWidth k = 0#k
      · simp [hz, negSign_zero_right]
      · simp only [hz, ↓reduceIte, mul_neg, e_mul_e k, ne_eq, not_false_eq_true, decide_true,
          Bool.true_xor]
        cases negSign k (p.setWidth k) (q.setWidth k)
        · simp [neg_mk]
        · simp
    · have hm : (p ^^^ q).msb = false := by simp [hp, hq]
      rw [e_succ_of_msb hp, e_succ_of_msb hq, e_succ_of_not_msb hm, hx, mk_mul_mk,
        negSign_of_msb_of_msb hp hq, star_e k]
      simp only [star_zero, mul_zero, zero_sub, add_zero]
      by_cases hz : q.setWidth k = 0#k
      · simp [hz, neg_mk]
      · simp only [hz, ↓reduceIte, neg_mul, neg_neg, e_mul_e k,
          BitVec.xor_comm (q.setWidth k)]
        split_ifs
        · rw [neg_mk, neg_zero]
        · rfl

/-- `e k p * e k q` as a signed basis element, in the form of
`cd_core.cd_sign`. -/
theorem e_mul_e_sign (k : ℕ) (p q : BitVec k) :
    e R k p * e R k q = sign k p q • e R k (p ^^^ q) := by
  rw [e_mul_e, sign]
  split_ifs <;> simp

/-- A basis element other than `1` has a negative square sign. -/
theorem negSign_self : ∀ (k : ℕ) (p : BitVec k), p ≠ 0#k → negSign k p p = true
  | 0, p, h => absurd (Subsingleton.elim p 0#0) h
  | k + 1, p, h => by
    cases hp : p.msb
    · rw [negSign_of_not_msb_of_not_msb hp hp]
      exact negSign_self k _ (fun hz => h ((setWidth_eq_zero_iff hp).1 hz))
    · rw [negSign_of_msb_of_msb hp hp]
      split_ifs with hz
      · rfl
      · exact negSign_self k _ hz

/-- Every basis element other than `1` squares to `-1`. -/
theorem e_mul_self (k : ℕ) {p : BitVec k} (h : p ≠ 0#k) : e R k p * e R k p = -1 := by
  rw [e_mul_e, negSign_self k p h, BitVec.xor_self, e_zero]
  rfl

/-- Two distinct basis elements other than `1` have opposite product
signs in the two orders. -/
theorem negSign_swap : ∀ (k : ℕ) (p q : BitVec k), p ≠ 0#k → q ≠ 0#k → p ≠ q →
    negSign k q p = !negSign k p q
  | 0, p, _, h, _, _ => absurd (Subsingleton.elim p 0#0) h
  | k + 1, p, q, hp0, hq0, hpq => by
    have hne : p.msb = q.msb → p.setWidth k ≠ q.setWidth k := fun hm hs =>
      hpq (by rw [← BitVec.cons_msb_setWidth p, ← BitVec.cons_msb_setWidth q, hm, hs])
    cases hp : p.msb <;> cases hq : q.msb
    · rw [negSign_of_not_msb_of_not_msb hq hp, negSign_of_not_msb_of_not_msb hp hq]
      exact negSign_swap k _ _ (fun hz => hp0 ((setWidth_eq_zero_iff hp).1 hz))
        (fun hz => hq0 ((setWidth_eq_zero_iff hq).1 hz)) (hne (hp.trans hq.symm))
    · rw [negSign_of_msb_of_not_msb hq hp, negSign_of_not_msb_of_msb hp hq]
      have hz : p.setWidth k ≠ 0#k := fun hz => hp0 ((setWidth_eq_zero_iff hp).1 hz)
      simp [hz]
    · rw [negSign_of_not_msb_of_msb hq hp, negSign_of_msb_of_not_msb hp hq]
      have hz : q.setWidth k ≠ 0#k := fun hz => hq0 ((setWidth_eq_zero_iff hq).1 hz)
      simp [hz]
    · rw [negSign_of_msb_of_msb hq hp, negSign_of_msb_of_msb hp hq]
      have hs := hne (hp.trans hq.symm)
      by_cases hpz : p.setWidth k = 0#k
      · have hqz : q.setWidth k ≠ 0#k := fun hz => hs (hpz.trans hz.symm)
        simp [hpz, hqz, negSign_zero_right]
      · by_cases hqz : q.setWidth k = 0#k
        · simp [hpz, hqz, negSign_zero_right]
        · simp only [hpz, hqz, ↓reduceIte]
          exact negSign_swap k _ _ hqz hpz (Ne.symm hs)

/-- The square sign of a basis element is negative exactly when the element
is not `1`. -/
theorem negSign_self_eq (k : ℕ) (p : BitVec k) : negSign k p p = decide (p ≠ 0#k) := by
  by_cases h : p = 0#k
  · subst h
    simp [negSign_zero_left]
  · simp [h, negSign_self k p h]

/-- Exchanging the two factors of a product of basis elements reverses its
sign exactly when both factors differ from `1` and from each other. -/
theorem negSign_swap_xor (k : ℕ) (p q : BitVec k) :
    negSign k q p = xor (negSign k p q) (decide (p ≠ 0#k ∧ q ≠ 0#k ∧ p ≠ q)) := by
  by_cases hp : p = 0#k
  · subst hp
    simp [negSign_zero_left, negSign_zero_right]
  by_cases hq : q = 0#k
  · subst hq
    simp [negSign_zero_left, negSign_zero_right]
  by_cases hpq : p = q
  · subst hpq
    simp
  · rw [negSign_swap k p q hp hq hpq]
    simp [hp, hq, hpq]

theorem cons_eq_zero_iff {k : ℕ} (b : Bool) (p : BitVec k) :
    BitVec.cons b p = 0#(k + 1) ↔ b = false ∧ p = 0#k := by
  constructor
  · intro h
    have hb := congrArg BitVec.msb h
    have hp := congrArg (BitVec.setWidth k) h
    simp only [BitVec.msb_cons, BitVec.setWidth_cons] at hb hp
    exact ⟨hb.trans (by simp), hp.trans (by simp)⟩
  · rintro ⟨rfl, rfl⟩
    apply BitVec.eq_of_toNat_eq
    simp

/-- The sign of a product at level `k + 1` is the sign of the product of
the low parts, corrected by the top bits: a transposition of the low
factors when the right factor lies in the second half, and the conjugation
signs of the left factor's second half. -/
theorem negSign_cons (k : ℕ) (P Q : Bool) (p q : BitVec k) :
    negSign (k + 1) (BitVec.cons P p) (BitVec.cons Q q) =
      ((negSign k p q ^^ (P && (decide (q ≠ 0#k) ^^ Q))) ^^
        (Q && decide (p ≠ 0#k ∧ q ≠ 0#k ∧ p ≠ q))) := by
  cases P <;> cases Q
  · rw [negSign_of_not_msb_of_not_msb (by simp) (by simp)]
    simp
  · rw [negSign_of_not_msb_of_msb (by simp) (by simp), BitVec.setWidth_cons,
      BitVec.setWidth_cons, negSign_swap_xor k p q]
    simp
  · rw [negSign_of_msb_of_not_msb (by simp) (by simp)]
    simp [Bool.xor_comm]
  · rw [negSign_of_msb_of_msb (by simp) (by simp), BitVec.setWidth_cons, BitVec.setWidth_cons]
    by_cases hq : q = 0#k
    · simp [hq, negSign_zero_right]
    · simp [hq, negSign_swap_xor k p q]

/-- Left multiplication by `e k p` applied twice: the sign of
`e k p * e k (p ^^^ q)` is that of `e k p * e k q`, reversed when `p ≠ 0`.
It is the basis form of `e p * (e p * e q) = -e q` for `p ≠ 0`. -/
theorem negSign_xor_right : ∀ (k : ℕ) (p q : BitVec k),
    negSign k p (p ^^^ q) = xor (decide (p ≠ 0#k)) (negSign k p q)
  | 0, p, q => by
    have hp : p = 0#0 := Subsingleton.elim _ _
    subst hp
    simp [negSign_zero_left]
  | k + 1, p, q => by
    obtain ⟨P, a, rfl⟩ : ∃ P a, p = BitVec.cons P a :=
      ⟨_, _, (BitVec.cons_msb_setWidth p).symm⟩
    obtain ⟨Q, c, rfl⟩ : ∃ Q c, q = BitVec.cons Q c :=
      ⟨_, _, (BitVec.cons_msb_setWidth q).symm⟩
    rw [BitVec.cons_xor_cons, negSign_cons, negSign_cons, negSign_xor_right k a c]
    have h1 : (a ^^^ c = 0#k) ↔ a = c := BitVec.xor_eq_zero_iff
    have h2 : (a = a ^^^ c) ↔ c = 0#k := eq_comm.trans xor_left_eq_self_iff
    simp only [ne_eq, cons_eq_zero_iff, h1, h2]
    by_cases ha : a = 0#k <;> by_cases hc : c = 0#k <;> by_cases hac : a = c <;>
      cases P <;> cases Q <;> cases negSign k a c <;> simp_all

/-- The sign of `e k p * e k (p ^^^ q)` is opposite to that of
`e k p * e k q` for `p ≠ 0`. -/
theorem negSign_xor_right_of_ne_zero (k : ℕ) {p : BitVec k} (hp : p ≠ 0#k) (q : BitVec k) :
    negSign k p (p ^^^ q) = !negSign k p q := by
  rw [negSign_xor_right, decide_eq_true hp, Bool.true_xor]

/-- Two distinct basis elements other than `1` anticommute. -/
theorem e_mul_e_anticomm (k : ℕ) {p q : BitVec k} (hp : p ≠ 0#k) (hq : q ≠ 0#k)
    (hpq : p ≠ q) :
    e R k q * e R k p = -(e R k p * e R k q) := by
  rw [e_mul_e, e_mul_e, negSign_swap k p q hp hq hpq, BitVec.xor_comm q p]
  cases negSign k p q <;> simp

end Tower

/-- The 32-dimensional Cayley-Dickson algebra over `R`, gororoba-quantum's
`A_5`. -/
abbrev Pathion (R : Type u) : Type u := Tower R 5

/-- The 16-dimensional Cayley-Dickson algebra over `R`. -/
abbrev Sedenion (R : Type u) : Type u := Tower R 4

end CayleyDickson
