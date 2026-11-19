/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TowerModule

/-!
# The algebraic normal form of a Boolean function on the index cube

Convention: a Boolean function `f : BitVec k → Bool` is a truth table on the
`2 ^ k` basis indices of `GororobaMath.CayleyDickson.Tower`, bit `k - 1`
(`msb`) the top bit. A mask `t` lies under `s` when `t &&& s = t`. The
algebraic normal form writes `f` over the two-element field as a sum of monomials
`∏ i ∈ s, x i`, one for each mask `s` whose coefficient `Tower.anfCoeff f s` is
`true`. The coefficient is the Moebius transform of `f`: the parity of the
number of masks `t` under `s` with `f t`. `Tower.anfEval c x` evaluates the
sum of the monomials `c` selects at `x`: the parity of the number of masks `s`
under `x` with `c s`, since `∏ i ∈ s, x i` is `1` exactly when `s` lies under
`x`.

Both maps are the same transform (`Tower.anfEval_eq_anfCoeff`), so the inversion
`anfEval (anfCoeff f) = f` says that the transform is an involution, and it is one
because between two masks `t` under `x` lie `2 ^ (weight of x - weight of t)`
masks, an odd count exactly when `t = x` (`Tower.sum_between`). The counting runs in
`ZMod 2` and splits `BitVec (k + 1)` by its top bit (`Tower.sumEquiv`).

The definitions mirror two functions of `gororoba_quantum/boolean_anf.py` in
gororoba-quantum. `anf_coefficients(truth_table)` is `Tower.anfCoeff`: it takes the
list of `2 ^ k` entries in `{0, 1}` with `truth_table[x] = 1` exactly when `f x`
(`x` read as `x.toNat`) and returns the tuple of the masks `s` with coefficient one,
so `s` lies in the tuple exactly when `anfCoeff f s`. `evaluate_anf(masks, x)` is
`Tower.anfEval`: it returns `1` exactly when `anfEval c x` for the table `c` that
selects the masks of `masks`. `ci/compare_anf.sh` runs both sides, and the Rocq
`anf_coef` and `anf_eval` of `rocq/quantum/CdSignRowAnf.v`, on the same truth tables.

## Main results

* `Tower.anfEval_anfCoeff`: the Moebius transform over submasks recovers `f` from its
  coefficients. The Rocq original is `anf_inversion` of `rocq/quantum/CdSignRowAnf.v`,
  whose `anf_coef k f s` is `anfCoeff` at `s.toNat` on the indices `x < 2 ^ k`.
* `Tower.anfCoeff_unique`: a coefficient table whose normal form evaluates to `f` is
  `anfCoeff f`. The Rocq original is `canonical_anf_unique` of
  `rocq/open/theories/BooleanANFDegree.v`, over the cube `cube order`, a nested pair
  whose last component is the top bit, read here through `cube_encode = BitVec.toNat`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

/-- The coefficient of the monomial `∏ i ∈ s, x i` in the algebraic normal form of
`f`: the parity of the number of masks `t` under `s` with `f t`. -/
def anfCoeff {k : ℕ} (f : BitVec k → Bool) (s : BitVec k) : Bool :=
  decide (Odd (Finset.univ.filter fun t => t &&& s = t ∧ f t = true).card)

/-- The sum at `x` of the monomials that the table `c` selects: the parity of the
number of masks `s` under `x` with `c s`. -/
def anfEval {k : ℕ} (c : BitVec k → Bool) (x : BitVec k) : Bool :=
  decide (Odd (Finset.univ.filter fun s => s &&& x = s ∧ c s = true).card)

/-- Evaluation and the coefficient transform are the same map. -/
theorem anfEval_eq_anfCoeff {k : ℕ} (c : BitVec k → Bool) : anfEval c = anfCoeff c := rfl

/-- A Boolean as an element of `ZMod 2`. -/
def boolZMod (b : Bool) : ZMod 2 := if b then 1 else 0

theorem boolZMod_injective : Function.Injective boolZMod := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem boolZMod_decide_odd (n : ℕ) : boolZMod (decide (Odd n)) = (n : ZMod 2) := by
  rcases Nat.even_or_odd n with h | h
  · rw [ZMod.natCast_eq_zero_iff_even.2 h, decide_eq_false (Nat.not_odd_iff_even.2 h)]
    rfl
  · rw [ZMod.natCast_eq_one_iff_odd.2 h, decide_eq_true h]
    rfl

/-- The parity of a filtered count, in `ZMod 2`. -/
theorem boolZMod_parity {k : ℕ} (p : BitVec k → Prop) [DecidablePred p] (g : BitVec k → Bool) :
    boolZMod (decide (Odd (Finset.univ.filter fun t => p t ∧ g t = true).card)) =
      ∑ t, if p t then boolZMod (g t) else 0 := by
  rw [boolZMod_decide_odd, Finset.natCast_card_filter]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hp : p t <;> cases g t <;> simp [hp, boolZMod]

theorem cons_eq_cons_iff {k : ℕ} (a b : Bool) (x y : BitVec k) :
    BitVec.cons a x = BitVec.cons b y ↔ a = b ∧ x = y := by
  constructor
  · intro h
    have ha := congrArg BitVec.msb h
    have hx := congrArg (BitVec.setWidth k) h
    simp only [BitVec.msb_cons, BitVec.setWidth_cons] at ha hx
    exact ⟨ha, hx⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A sum over `BitVec (k + 1)` splits by the top bit. -/
theorem sum_cons {M : Type*} [AddCommMonoid M] {k : ℕ} (g : BitVec (k + 1) → M) :
    ∑ s, g s = ∑ s : BitVec k, (g (BitVec.cons false s) + g (BitVec.cons true s)) := by
  rw [← Equiv.sum_comp (sumEquiv k), Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  rfl

/-- The number of masks between `t` and `x` is odd exactly when `t = x`. -/
theorem sum_between : ∀ {k : ℕ} (t x : BitVec k),
    (∑ s, if t &&& s = t ∧ s &&& x = s then (1 : ZMod 2) else 0) = if t = x then 1 else 0
  | 0, t, x => by
    rw [Fintype.sum_subsingleton _ x]
    have h1 : t = x := Subsingleton.elim _ _
    subst h1
    simp only [BitVec.and_self, and_self, ↓reduceIte]
  | k + 1, t, x => by
    obtain ⟨T, t, rfl⟩ : ∃ T t', t = BitVec.cons T t' :=
      ⟨_, _, (BitVec.cons_msb_setWidth t).symm⟩
    obtain ⟨X, x, rfl⟩ : ∃ X x', x = BitVec.cons X x' :=
      ⟨_, _, (BitVec.cons_msb_setWidth x).symm⟩
    rw [sum_cons]
    simp only [BitVec.cons_and_cons, cons_eq_cons_iff]
    have ih := sum_between t x
    cases T <;> cases X <;> simp [ih, CharTwo.add_self_eq_zero]

/-- Moebius inversion: the normal form with the coefficients `anfCoeff f` evaluates
to `f`. The Rocq original is `anf_inversion` of `rocq/quantum/CdSignRowAnf.v`. -/
theorem anfEval_anfCoeff {k : ℕ} (f : BitVec k → Bool) (x : BitVec k) :
    anfEval (anfCoeff f) x = f x := by
  apply boolZMod_injective
  unfold anfEval
  rw [boolZMod_parity]
  have hc : ∀ s, boolZMod (anfCoeff f s) = ∑ t, if t &&& s = t then boolZMod (f t) else 0 :=
    fun s => boolZMod_parity _ f
  simp only [hc]
  calc
    (∑ s, if s &&& x = s then ∑ t, (if t &&& s = t then boolZMod (f t) else 0) else 0) =
        ∑ s, ∑ t, boolZMod (f t) * if t &&& s = t ∧ s &&& x = s then 1 else 0 := by
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases hs : s &&& x = s
      · simp only [hs, ↓reduceIte, and_true]
        refine Finset.sum_congr rfl fun t _ => ?_
        split_ifs
        · simp only [mul_one]
        · simp only [mul_zero]
      · simp only [hs, ↓reduceIte, and_false, mul_zero, Finset.sum_const_zero]
    _ = ∑ t, boolZMod (f t) * ∑ s, if t &&& s = t ∧ s &&& x = s then 1 else 0 := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ = boolZMod (f x) := by
      simp only [sum_between, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
        ↓reduceIte]

/-- The transform is an involution. -/
theorem anfCoeff_anfCoeff {k : ℕ} (f : BitVec k → Bool) : anfCoeff (anfCoeff f) = f :=
  funext (anfEval_anfCoeff f)

/-- A coefficient table whose normal form evaluates to `f` is the canonical one. The
Rocq original is `canonical_anf_unique` of `rocq/open/theories/BooleanANFDegree.v`. -/
theorem anfCoeff_unique {k : ℕ} (f c : BitVec k → Bool) (h : ∀ x, anfEval c x = f x) :
    c = anfCoeff f := by
  have hf : anfEval c = f := funext h
  rw [← hf, anfEval_eq_anfCoeff, anfCoeff_anfCoeff]

/-- A mask as the set of its set bits has `weight s` elements. -/
def weight {k : ℕ} (s : BitVec k) : ℕ := (Finset.univ.filter fun i : Fin k => s.getLsbD i).card

/-- The algebraic degree of `f`: the largest weight of a monomial with coefficient `true`; the
zero function has degree `0`. -/
def anfDegree {k : ℕ} (f : BitVec k → Bool) : ℕ :=
  (Finset.univ.filter fun s => anfCoeff f s = true).sup weight

theorem le_anfDegree {k : ℕ} {f : BitVec k → Bool} {s : BitVec k} (h : anfCoeff f s = true) :
    weight s ≤ anfDegree f :=
  Finset.le_sup (f := weight) (Finset.mem_filter.2 ⟨Finset.mem_univ s, h⟩)

theorem anfDegree_le {k : ℕ} {f : BitVec k → Bool} {d : ℕ}
    (h : ∀ s, anfCoeff f s = true → weight s ≤ d) : anfDegree f ≤ d :=
  Finset.sup_le fun s hs => h s (Finset.mem_filter.1 hs).2

theorem weight_cons {k : ℕ} (b : Bool) (s : BitVec k) :
    weight (BitVec.cons b s) = weight s + if b then 1 else 0 := by
  unfold weight
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [BitVec.getElem_cons, Nat.ne_of_lt i.isLt]
  · simp [BitVec.getElem_cons]

theorem boolZMod_xor (a b : Bool) : boolZMod (a ^^ b) = boolZMod a + boolZMod b := by
  cases a <;> cases b <;> decide

theorem anfCoeff_cons_false {k : ℕ} (f : BitVec (k + 1) → Bool) (s : BitVec k) :
    anfCoeff f (BitVec.cons false s) = anfCoeff (fun q => f (BitVec.cons false q)) s := by
  apply boolZMod_injective
  unfold anfCoeff
  rw [boolZMod_parity, boolZMod_parity, sum_cons]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp [BitVec.cons_and_cons, cons_eq_cons_iff]

theorem anfCoeff_cons_true {k : ℕ} (f : BitVec (k + 1) → Bool) (s : BitVec k) :
    anfCoeff f (BitVec.cons true s) =
      anfCoeff (fun q => f (BitVec.cons true q) ^^ f (BitVec.cons false q)) s := by
  apply boolZMod_injective
  unfold anfCoeff
  rw [boolZMod_parity, boolZMod_parity, sum_cons]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [BitVec.cons_and_cons, cons_eq_cons_iff, Bool.and_true, boolZMod_xor]
  by_cases hq : q &&& s = q <;> simp [hq, add_comm]

/-- The coefficient of the sum of two point indicators at a mask: the sum of the two submask
tests. -/
theorem anfCoeff_two_point {k : ℕ} (a b s : BitVec k) :
    anfCoeff (fun x => decide (x = a) ^^ decide (x = b)) s =
      (decide (a &&& s = a) ^^ decide (b &&& s = b)) := by
  apply boolZMod_injective
  unfold anfCoeff
  rw [boolZMod_parity, boolZMod_xor]
  have key : ∀ a' : BitVec k, (∑ t, if t &&& s = t then boolZMod (decide (t = a')) else 0) =
      boolZMod (decide (a' &&& s = a')) := fun a' => by
    rw [Finset.sum_eq_single a']
    · simp [boolZMod]
    · intro t _ ht
      simp [boolZMod, ht]
    · simp
  have e : ∀ t, boolZMod (decide (t = a) ^^ decide (t = b)) =
      boolZMod (decide (t = a)) + boolZMod (decide (t = b)) := fun t => boolZMod_xor _ _
  simp only [e]
  rw [← key a, ← key b, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp

theorem submask_iff {k : ℕ} (a s : BitVec k) :
    a &&& s = a ↔ ∀ i, i < k → a.getLsbD i = true → s.getLsbD i = true := by
  constructor
  · intro h i _ hi
    have := congrArg (fun v => v.getLsbD i) h
    simp only [BitVec.getLsbD_and, hi, Bool.true_and] at this
    exact this
  · intro h
    refine BitVec.eq_of_getLsbD_eq fun i hik => ?_
    rw [BitVec.getLsbD_and]
    cases ha : a.getLsbD i
    · exact Bool.false_and _
    · rw [h i hik ha]
      rfl

theorem weight_le {k : ℕ} (s : BitVec k) : weight s ≤ k := by
  unfold weight
  calc _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_filter_le _ _
    _ = k := by simp

theorem getLsbD_of_weight_eq {k : ℕ} {s : BitVec k} (h : weight s = k) (i : Fin k) :
    s.getLsbD i = true := by
  unfold weight at h
  have h' : (Finset.univ.filter fun i : Fin k => s.getLsbD i).card =
      (Finset.univ : Finset (Fin k)).card := by simpa using h
  exact (Finset.card_filter_eq_iff.1 h') i (Finset.mem_univ i)

/-- The mask with every bit set except bit `i`. -/
def clearBit {k : ℕ} (i : Fin k) : BitVec k := ~~~BitVec.twoPow k i

theorem getLsbD_clearBit {k : ℕ} (i : Fin k) (j : ℕ) :
    (clearBit i).getLsbD j = (decide (j < k) && decide (j ≠ i.val)) := by
  have hi : decide ((i : ℕ) < k) = true := decide_eq_true i.isLt
  unfold clearBit
  rw [BitVec.getLsbD_not, BitVec.getLsbD_twoPow, hi, Bool.true_and]
  by_cases h : (i : ℕ) = j
  · simp [h]
  · simp [h, Ne.symm h]

theorem weight_clearBit {k : ℕ} (i : Fin k) : weight (clearBit i) = k - 1 := by
  unfold weight
  have : (Finset.univ.filter fun j : Fin k => (clearBit i).getLsbD j) = Finset.univ.erase i := by
    ext j
    rw [Finset.mem_filter, Finset.mem_erase, getLsbD_clearBit]
    simp [Fin.ext_iff]
  rw [this, Finset.card_erase_of_mem (Finset.mem_univ i)]
  simp

theorem submask_clearBit_iff {k : ℕ} (i : Fin k) (c : BitVec k) :
    c &&& clearBit i = c ↔ c.getLsbD i = false := by
  rw [submask_iff]
  constructor
  · intro h
    by_contra hc
    have hc' : c.getLsbD i = true := by simpa using hc
    have := h i i.isLt hc'
    rw [getLsbD_clearBit] at this
    simp at this
  · intro h j hj hcj
    rw [getLsbD_clearBit]
    by_cases hji : j = i.val
    · rw [hji] at hcj
      rw [h] at hcj
      exact absurd hcj (by simp)
    · simp [hj, hji]


theorem anfCoeff_point {k : ℕ} (a s : BitVec k) :
    anfCoeff (fun x => decide (x = a)) s = decide (a &&& s = a) := by
  apply boolZMod_injective
  unfold anfCoeff
  rw [boolZMod_parity, Finset.sum_eq_single a]
  · by_cases h : a &&& s = a <;> simp [boolZMod, h]
  · intro t _ ht
    simp [boolZMod, ht]
  · simp

theorem anfCoeff_xor {k : ℕ} (f g : BitVec k → Bool) (s : BitVec k) :
    anfCoeff (fun x => f x ^^ g x) s = (anfCoeff f s ^^ anfCoeff g s) := by
  apply boolZMod_injective
  rw [boolZMod_xor]
  unfold anfCoeff
  rw [boolZMod_parity, boolZMod_parity, boolZMod_parity, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> simp [boolZMod_xor]

theorem anfCoeff_true {k : ℕ} (s : BitVec k) :
    anfCoeff (fun _ => true) s = decide (s = 0#k) := by
  apply boolZMod_injective
  unfold anfCoeff
  rw [boolZMod_parity]
  have h := sum_between (0#k) s
  simp only [BitVec.zero_and, true_and] at h
  by_cases hs : s = 0#k
  · subst hs
    simp [boolZMod]
  · have hs' : ¬ (0#k = s) := fun h => hs h.symm
    simpa [boolZMod, hs, hs'] using h

theorem anfCoeff_xor_true {k : ℕ} (f : BitVec k → Bool) (s : BitVec k) :
    anfCoeff (fun x => f x ^^ true) s = (anfCoeff f s ^^ decide (s = 0#k)) := by
  rw [← anfCoeff_true]
  exact anfCoeff_xor f (fun _ => true) s

theorem weight_zero {k : ℕ} : weight (0#k) = 0 := by
  simp [weight]

theorem weight_allOnes {k : ℕ} : weight (BitVec.allOnes k) = k := by
  simp [weight]

theorem anfDegree_cons_le {k : ℕ} (f : BitVec (k + 1) → Bool) {d : ℕ}
    (h0 : ∀ s, anfCoeff (fun q => f (BitVec.cons false q)) s = true → weight s ≤ d)
    (h1 : ∀ s, anfCoeff (fun q => f (BitVec.cons true q) ^^ f (BitVec.cons false q)) s = true →
      weight s + 1 ≤ d) : anfDegree f ≤ d := by
  apply anfDegree_le
  intro s hs
  obtain ⟨S, s, rfl⟩ : ∃ S s', s = BitVec.cons S s' :=
    ⟨_, _, (BitVec.cons_msb_setWidth s).symm⟩
  rw [weight_cons]
  cases S
  · rw [anfCoeff_cons_false] at hs
    simpa using h0 s hs
  · rw [anfCoeff_cons_true] at hs
    simpa using h1 s hs

theorem le_anfDegree_cons_false {k : ℕ} {f : BitVec (k + 1) → Bool} {s : BitVec k}
    (h : anfCoeff (fun q => f (BitVec.cons false q)) s = true) : weight s ≤ anfDegree f := by
  have := le_anfDegree (f := f) (s := BitVec.cons false s) (by rwa [anfCoeff_cons_false])
  simpa [weight_cons] using this

theorem le_anfDegree_cons_true {k : ℕ} {f : BitVec (k + 1) → Bool} {s : BitVec k}
    (h : anfCoeff (fun q => f (BitVec.cons true q) ^^ f (BitVec.cons false q)) s = true) :
    weight s + 1 ≤ anfDegree f := by
  have := le_anfDegree (f := f) (s := BitVec.cons true s) (by rwa [anfCoeff_cons_true])
  simpa [weight_cons] using this

theorem weight_succ_le_of_anfCoeff_two_point {k : ℕ} {a b s : BitVec k}
    (hs : anfCoeff (fun x => decide (x = a) ^^ decide (x = b)) s = true) : weight s + 1 ≤ k := by
  rw [anfCoeff_two_point] at hs
  by_contra hlt
  have hw : weight s = k := by
    have := weight_le s
    omega
  have hall := getLsbD_of_weight_eq hw
  have ha : a &&& s = a := (submask_iff a s).2 fun i hi _ => hall ⟨i, hi⟩
  have hb : b &&& s = b := (submask_iff b s).2 fun i hi _ => hall ⟨i, hi⟩
  simp [ha, hb] at hs

theorem exists_anfCoeff_two_point {k : ℕ} {a b : BitVec k} (h : a ≠ b) :
    ∃ s, weight s + 1 = k ∧ anfCoeff (fun x => decide (x = a) ^^ decide (x = b)) s = true := by
  obtain ⟨i, hi⟩ : ∃ i : Fin k, a.getLsbD i ≠ b.getLsbD i := by
    by_contra hc
    exact h (BitVec.eq_of_getLsbD_eq fun i hik =>
      by_contra fun hne => hc ⟨⟨i, hik⟩, hne⟩)
  refine ⟨clearBit i, ?_, ?_⟩
  · rw [weight_clearBit]
    have := i.isLt
    omega
  · simp only [anfCoeff_two_point, submask_clearBit_iff]
    rcases Bool.eq_false_or_eq_true (a.getLsbD i) with ha | ha <;>
      rcases Bool.eq_false_or_eq_true (b.getLsbD i) with hb | hb <;>
        (simp only [ha, hb] at hi ⊢; first | exact absurd rfl hi | decide)

/-- The sum of the indicators of two distinct points has degree `k - 1`. The Rocq original is
`two_point_indicator_degree` of `rocq/open/theories/BooleanANFDegree.v`. -/
theorem anfDegree_two_point {k : ℕ} {a b : BitVec k} (h : a ≠ b) :
    anfDegree (fun x => decide (x = a) ^^ decide (x = b)) = k - 1 := by
  obtain ⟨s, hs, hc⟩ := exists_anfCoeff_two_point h
  apply le_antisymm
  · apply anfDegree_le
    intro t ht
    have := weight_succ_le_of_anfCoeff_two_point ht
    omega
  · have := le_anfDegree hc
    omega

theorem comm_eq_of_ne_zero {K : ℕ} {p : BitVec K} (hp : p ≠ 0#K) (q : BitVec K) :
    decide (p ≠ 0#K ∧ q ≠ 0#K ∧ p ≠ q) = ((decide (q = 0#K) ^^ decide (q = p)) ^^ true) := by
  by_cases h0 : q = 0#K
  · subst h0
    simp [hp, Ne.symm hp]
  · by_cases hqp : q = p
    · subst hqp
      simp [h0]
    · have : p ≠ q := fun h => hqp h.symm
      simp [hp, h0, hqp, this]

/-- Every nonzero left sign row of level `k` at least `2` has algebraic degree `k - 1`. The Rocq
originals are `sign_row_degree` of `rocq/open/theories/CDPhaseDegree.v` and
`sign_row_degree_is` of `rocq/quantum/CdSignRowAnf.v`, whose left sign row
`sign_row k m x = am_exponent k x m` is `negSign k m x`. -/
theorem anfDegree_negSign_left {k : ℕ} (hk : 2 ≤ k) {m : BitVec k} (hm : m ≠ 0#k) :
    anfDegree (negSign k m) = k - 1 := by
  obtain ⟨K, rfl⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
  rcases Nat.lt_or_ge K 2 with hK | hK
  · obtain rfl : K = 1 := by omega
    revert m
    decide
  obtain ⟨P, p, rfl⟩ : ∃ P p, m = BitVec.cons P p :=
    ⟨_, _, (BitVec.cons_msb_setWidth m).symm⟩
  have hd : ∀ q : BitVec K, decide (q ≠ 0#K) = !decide (q = 0#K) := by intro q; simp
  cases P
  · -- the top bit of m is clear: the second half of x adds the commutation phase of (p, q)
    have hp : p ≠ 0#K := fun h => hm (by rw [h]; exact (cons_eq_zero_iff false 0#K).2 ⟨rfl, rfl⟩)
    have e0 : ∀ q, negSign (K + 1) (BitVec.cons false p) (BitVec.cons false q) =
        negSign K p q := by
      intro q
      rw [negSign_cons]
      simp
    have e1 : ∀ q, (negSign (K + 1) (BitVec.cons false p) (BitVec.cons true q) ^^
        negSign (K + 1) (BitVec.cons false p) (BitVec.cons false q)) =
        ((decide (q = 0#K) ^^ decide (q = p)) ^^ true) := by
      intro q
      rw [negSign_cons, negSign_cons, comm_eq_of_ne_zero hp q, hd]
      generalize negSign K p q = s
      generalize decide (q = 0#K) = u
      generalize decide (q = p) = v
      revert s u v
      decide
    apply le_antisymm
    · apply anfDegree_cons_le (d := K)
      · intro s _
        exact weight_le s
      · intro s hs
        simp only [e1, anfCoeff_xor_true] at hs
        by_cases h0 : s = 0#K
        · subst h0
          rw [weight_zero]
          omega
        · simp only [h0, decide_false, Bool.xor_false] at hs
          exact weight_succ_le_of_anfCoeff_two_point hs
    · obtain ⟨s, hs, hc⟩ := exists_anfCoeff_two_point (a := 0#K) (b := p) (fun h => hp h.symm)
      have hs0 : s ≠ 0#K := by
        rintro rfl
        rw [weight_zero] at hs
        omega
      have := le_anfDegree_cons_true (f := negSign (K + 1) (BitVec.cons false p)) (s := s)
        (by simp only [e1, anfCoeff_xor_true, hs0, decide_false, Bool.xor_false]; exact hc)
      omega
  · by_cases hp : p = 0#K
    · subst hp
      have e0 : ∀ q, negSign (K + 1) (BitVec.cons true 0#K) (BitVec.cons false q) =
          (decide (q = 0#K) ^^ true) := by
        intro q
        rw [negSign_cons, hd]
        simp [negSign_zero_left]
      have e1 : ∀ q, (negSign (K + 1) (BitVec.cons true 0#K) (BitVec.cons true q) ^^
          negSign (K + 1) (BitVec.cons true 0#K) (BitVec.cons false q)) = true := by
        intro q
        rw [negSign_cons, negSign_cons, hd]
        simp only [negSign_zero_left, ne_eq, not_true_eq_false, false_and, decide_false]
        generalize decide (q = 0#K) = u
        revert u
        decide
      apply le_antisymm
      · apply anfDegree_cons_le (d := K)
        · intro s _
          exact weight_le s
        · intro s hs
          simp only [e1, anfCoeff_true] at hs
          have := of_decide_eq_true hs
          subst this
          rw [weight_zero]
          omega
      · have hz : BitVec.allOnes K ≠ 0#K := by
          intro h
          have := congrArg weight h
          rw [weight_allOnes, weight_zero] at this
          omega
        have := le_anfDegree_cons_false (f := negSign (K + 1) (BitVec.cons true 0#K))
          (s := BitVec.allOnes K)
          (by
            simp only [e0, anfCoeff_xor_true, anfCoeff_point, hz, decide_false, Bool.xor_false]
            simp)
        rw [weight_allOnes] at this
        omega
    · have e1 : ∀ q, (negSign (K + 1) (BitVec.cons true p) (BitVec.cons true q) ^^
          negSign (K + 1) (BitVec.cons true p) (BitVec.cons false q)) =
          (decide (q = 0#K) ^^ decide (q = p)) := by
        intro q
        rw [negSign_cons, negSign_cons, comm_eq_of_ne_zero hp q, hd]
        generalize negSign K p q = s
        generalize decide (q = 0#K) = u
        generalize decide (q = p) = v
        revert s u v
        decide
      apply le_antisymm
      · apply anfDegree_cons_le (d := K)
        · intro s _
          exact weight_le s
        · intro s hs
          simp only [e1] at hs
          exact weight_succ_le_of_anfCoeff_two_point hs
      · obtain ⟨s, hs, hc⟩ := exists_anfCoeff_two_point (a := 0#K) (b := p) (fun h => hp h.symm)
        have := le_anfDegree_cons_true (f := negSign (K + 1) (BitVec.cons true p)) (s := s)
          (by simp only [e1]; exact hc)
        omega

theorem anfCoeff_false {k : ℕ} (s : BitVec k) : anfCoeff (fun _ => false) s = false := by
  simp [anfCoeff]

theorem anfDegree_cons_false_le {k : ℕ} (f : BitVec (k + 1) → Bool) :
    anfDegree (fun q => f (BitVec.cons false q)) ≤ anfDegree f := by
  apply anfDegree_le
  intro s hs
  exact le_anfDegree_cons_false hs

/-- The degree of a right sign row as a function of the integer index of the row. -/
def rightRowDegree (n : ℕ) : ℕ := if n = 2 ^ Nat.log2 n then 1 else max 1 (Nat.log2 n - 1)

theorem one_le_rightRowDegree (n : ℕ) : 1 ≤ rightRowDegree n := by
  unfold rightRowDegree
  split_ifs <;> omega

theorem toNat_cons_false' {k : ℕ} (μ : BitVec k) : (BitVec.cons false μ).toNat = μ.toNat := by
  rw [BitVec.toNat_cons']
  simp

theorem toNat_cons_true' {k : ℕ} (μ : BitVec k) :
    (BitVec.cons true μ).toNat = 2 ^ k + μ.toNat := by
  rw [BitVec.toNat_cons']
  simp [Nat.shiftLeft_eq]

theorem log2_cons_true {k : ℕ} (μ : BitVec k) : Nat.log2 (BitVec.cons true μ).toNat = k := by
  rw [toNat_cons_true']
  have := μ.isLt
  rw [Nat.log2_eq_iff (by positivity)]
  constructor
  · omega
  · rw [pow_succ]
    omega

theorem rightRowDegree_cons_true_zero (k : ℕ) :
    rightRowDegree (BitVec.cons true (0#k)).toNat = 1 := by
  unfold rightRowDegree
  rw [log2_cons_true, toNat_cons_true']
  simp

theorem rightRowDegree_cons_true {k : ℕ} {μ : BitVec k} (hμ : μ ≠ 0#k) :
    rightRowDegree (BitVec.cons true μ).toNat = max 1 (k - 1) := by
  unfold rightRowDegree
  rw [log2_cons_true]
  have : μ.toNat ≠ 0 := fun h => hμ (BitVec.eq_of_toNat_eq (by simpa using h))
  have h2 : (BitVec.cons true μ).toNat ≠ 2 ^ k := by
    rw [toNat_cons_true']
    omega
  simp only [h2, ↓reduceIte]

theorem anfDegree_negSign_right_aux : ∀ (k : ℕ) (m : BitVec k), m ≠ 0#k →
    anfDegree (fun x => negSign k x m) = rightRowDegree m.toNat
  | 0, m, hm => absurd (Subsingleton.elim m 0#0) hm
  | k + 1, m, hm => by
    obtain ⟨M, μ, rfl⟩ : ∃ M μ, m = BitVec.cons M μ :=
      ⟨_, _, (BitVec.cons_msb_setWidth m).symm⟩
    cases M
    · have hμ : μ ≠ 0#k := fun h => hm (by rw [h]; exact (cons_eq_zero_iff false 0#k).2 ⟨rfl, rfl⟩)
      have hμ' : decide (μ ≠ 0#k) = true := by simp [hμ]
      have e0 : ∀ q, negSign (k + 1) (BitVec.cons false q) (BitVec.cons false μ) =
          negSign k q μ := by
        intro q
        rw [negSign_cons]
        simp
      have e1 : ∀ q, (negSign (k + 1) (BitVec.cons true q) (BitVec.cons false μ) ^^
          negSign (k + 1) (BitVec.cons false q) (BitVec.cons false μ)) = true := by
        intro q
        rw [negSign_cons, negSign_cons, hμ']
        generalize negSign k q μ = s
        generalize decide (q ≠ 0#k ∧ μ ≠ 0#k ∧ q ≠ μ) = c
        revert s c
        decide
      have ih := anfDegree_negSign_right_aux k μ hμ
      rw [toNat_cons_false']
      apply le_antisymm
      · apply anfDegree_cons_le (f := fun x => negSign (k + 1) x (BitVec.cons false μ))
        · intro s hs
          simp only [e0] at hs
          have := le_anfDegree hs
          omega
        · intro s hs
          simp only [e1, anfCoeff_true] at hs
          have := of_decide_eq_true hs
          subst this
          rw [weight_zero]
          have := one_le_rightRowDegree μ.toNat
          omega
      · have := anfDegree_cons_false_le (fun x => negSign (k + 1) x (BitVec.cons false μ))
        simp only [e0] at this
        omega
    · by_cases hμ : μ = 0#k
      · subst hμ
        have e0 : ∀ q, negSign (k + 1) (BitVec.cons false q) (BitVec.cons true 0#k) = false := by
          intro q
          rw [negSign_cons]
          simp [negSign_zero_right]
        have e1 : ∀ q, (negSign (k + 1) (BitVec.cons true q) (BitVec.cons true 0#k) ^^
            negSign (k + 1) (BitVec.cons false q) (BitVec.cons true 0#k)) = true := by
          intro q
          rw [negSign_cons, negSign_cons]
          simp [negSign_zero_right]
        rw [rightRowDegree_cons_true_zero]
        apply le_antisymm
        · apply anfDegree_cons_le (f := fun x => negSign (k + 1) x (BitVec.cons true 0#k))
          · intro s hs
            simp only [e0, anfCoeff_false] at hs
            exact absurd hs (by simp)
          · intro s hs
            simp only [e1, anfCoeff_true] at hs
            have := of_decide_eq_true hs
            subst this
            rw [weight_zero]
        · have := le_anfDegree_cons_true (f := fun x => negSign (k + 1) x (BitVec.cons true 0#k))
            (s := 0#k) (by simp only [e1, anfCoeff_true]; simp)
          rw [weight_zero] at this
          omega
      · have hμ' : decide (μ ≠ 0#k) = true := by simp [hμ]
        have e0 : ∀ q, negSign (k + 1) (BitVec.cons false q) (BitVec.cons true μ) =
            negSign k μ q := by
          intro q
          rw [negSign_cons, negSign_swap_xor k q μ]
          simp
        have e1 : ∀ q, (negSign (k + 1) (BitVec.cons true q) (BitVec.cons true μ) ^^
            negSign (k + 1) (BitVec.cons false q) (BitVec.cons true μ)) = false := by
          intro q
          rw [negSign_cons, negSign_cons, hμ']
          generalize negSign k q μ = s
          generalize decide (q ≠ 0#k ∧ μ ≠ 0#k ∧ q ≠ μ) = c
          revert s c
          decide
        rw [rightRowDegree_cons_true hμ]
        have hL : anfDegree (fun q => negSign k μ q) = max 1 (k - 1) := by
          rcases Nat.lt_or_ge k 2 with hk | hk
          · obtain rfl : k = 1 := by
              rcases Nat.eq_zero_or_pos k with h0 | h0
              · subst h0
                exact absurd (Subsingleton.elim μ 0#0) hμ
              · omega
            revert μ
            decide
          · have := anfDegree_negSign_left hk hμ
            show anfDegree (negSign k μ) = _
            omega
        apply le_antisymm
        · apply anfDegree_cons_le (f := fun x => negSign (k + 1) x (BitVec.cons true μ))
          · intro s hs
            simp only [e0] at hs
            have := le_anfDegree hs
            omega
          · intro s hs
            simp only [e1, anfCoeff_false] at hs
            exact absurd hs (by simp)
        · have := anfDegree_cons_false_le (fun x => negSign (k + 1) x (BitVec.cons true μ))
          simp only [e0] at this
          omega

/-- The right sign row `x ↦ negSign k x m` has degree `1` when `m` is a power of two and
`max 1 (log2 m - 1)` otherwise. The Rocq original is `right_row_degree` of
`rocq/quantum/CdSignRowAnf.v`. -/
theorem anfDegree_negSign_right {k : ℕ} {m : BitVec k} (hm : m ≠ 0#k) :
    anfDegree (fun x => negSign k x m) =
      if m.toNat = 2 ^ Nat.log2 m.toNat then 1 else max 1 (Nat.log2 m.toNat - 1) :=
  anfDegree_negSign_right_aux k m hm

/-- The normal form of `x ↦ x₀ ∧ x₁` on two bits is the single monomial `x₀ x₁`. -/
example :
    anfCoeff (fun x : BitVec 2 => x.getLsbD 0 && x.getLsbD 1) = fun s => decide (s = 3#2) := by
  decide

end Tower

end CayleyDickson
