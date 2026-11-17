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
    simp
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
        split_ifs <;> simp
      · simp [hs]
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

/-- The normal form of `x ↦ x₀ ∧ x₁` on two bits is the single monomial `x₀ x₁`. -/
example :
    anfCoeff (fun x : BitVec 2 => x.getLsbD 0 && x.getLsbD 1) = fun s => decide (s = 3#2) := by
  decide

end Tower

end CayleyDickson
