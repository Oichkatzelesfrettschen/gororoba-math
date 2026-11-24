/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.NormMultiplicative
public import GororobaMath.CayleyDickson.ScaledPairAnnihilator
public import GororobaMath.CayleyDickson.SingularKernel

/-!
# The zero divisors of the sedenions

Convention: the product of `Tower F k` is the Cayley-Dickson product of
`GororobaMath.CayleyDickson.Tower`, `(a, b) (c, d) = (a c - star d b, d a + b star c)`, and
`Tower.mk` builds a pair; `Tower.re` is the coordinate of `1` and `Tower.dot` the trace form.
Biss, Dugger and Isaksen, Large annihilators in Cayley-Dickson algebras (arXiv:math/0511691,
2005), Proposition 12.1, describe the zero divisors of `A_4 = Tower ℝ 4`; their `Ann x` is the
kernel of left multiplication by `x`, the library's `LinearMap.ker (Tower.mulLeft F k x)`.
The hypotheses are those of `GororobaMath.CayleyDickson.ScaledPairAnnihilator`: a field `F` whose
star is the identity, with a partial order compatible with addition in which every square is
nonnegative (`hsq`); the reals are the instance `hsq := mul_self_nonneg`. A left zero divisor
is a nonzero `z` with `z * x = 0` for some `x ≠ 0`.

Proposition 12.1 reads here as the criterion on the halves `a`, `b` of `mk a b`: both halves are
imaginary, they are orthogonal, and their squared norms agree and are nonzero. The "only if"
direction takes a product `mk a b * mk c d = 0` of nonzero elements, whose four halves are
imaginary (Lemma 9.5). A vanishing half of `mk a b` would put the element in the scaled-pair form
of Theorem 10.1 over the octonions, which have no zero divisors, so `a` and `b` are nonzero. The
product gives `a c = -(d b)` and `d a = b c`; norm multiplicativity at level 3 turns them into
`|a|² |c|² = |d|² |b|²` and `|d|² |a|² = |b|² |c|²`, whence `|a|² = |b|²`. The alternative laws
give `(d b) c = |c|² a` and `d (b c) = -(|d|² a)`, so `(|c|² + |d|²) a` is the associator of
`d`, `b`, `c`, which is orthogonal to `b`, and `a` is orthogonal to `b`. The "if" direction is the
nonzero kernel of `GororobaMath.CayleyDickson.SingularKernel`.

## Main results

* `Tower.eq_zero_of_mul_eq_zero_of_le_three`: the levels up to 3 have no left zero divisors.
* `Tower.criterion_of_mk_mul_mk_eq_zero`: a vanishing product of nonzero elements `mk a b`,
  `mk c d` at level 4 satisfies the criterion.
* `Tower.mk_isLeftZeroDivisor_iff`: Proposition 12.1 of the paper.
* `Tower.finrank_ker_mulLeft_mk_eq_four_iff`, `Tower.finrank_ker_mulLeft_mk_eq_zero_or_four`: the
  kernel of left multiplication by a nonzero sedenion has dimension 0 or 4, and 4 exactly under
  the criterion.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

open Module

section Criterion

variable {F : Type u} [Field F] [StarRing F] [TrivialStar F] [PartialOrder F]
  [IsOrderedAddMonoid F]

/-- A product of two elements of level at most `3` vanishes only when a factor does: the norm
`dot (x * y) (x * y)` factors. -/
theorem eq_zero_or_eq_zero_of_mul_eq_zero_of_le_three (hsq : ∀ x : F, 0 ≤ x * x) {k : ℕ}
    (hk : k ≤ 3) {x y : Tower F k} (h : x * y = 0) : x = 0 ∨ y = 0 := by
  have h1 := dot_mul_self_of_le_three hk x y
  rw [h, dot_zero_left] at h1
  rcases mul_eq_zero.1 h1.symm with h2 | h2
  · exact Or.inl (eq_zero_of_dot_self_eq_zero hsq h2)
  · exact Or.inr (eq_zero_of_dot_self_eq_zero hsq h2)

/-- The levels up to `3` have no left zero divisors. -/
theorem eq_zero_of_mul_eq_zero_of_le_three (hsq : ∀ x : F, 0 ≤ x * x) {k : ℕ} (hk : k ≤ 3)
    {x y : Tower F k} (hx : x ≠ 0) (h : x * y = 0) : y = 0 :=
  (eq_zero_or_eq_zero_of_mul_eq_zero_of_le_three hsq hk h).resolve_left hx

omit [StarRing F] [TrivialStar F] in
/-- Two is nonzero when every square is nonnegative: `1 + 1 = 0` forces `1 = 0`. -/
theorem two_ne_zero_of_sq_nonneg (hsq : ∀ x : F, 0 ≤ x * x) : (2 : F) ≠ 0 := by
  intro h
  have h1 : (1 : F) + 1 = 0 := by rw [one_add_one_eq_two]; exact h
  have h0 : (0 : F) ≤ 1 := by simpa using hsq 1
  exact one_ne_zero ((add_eq_zero_iff_of_nonneg h0 h0).1 h1).1

/-- A zero divisor of the sedenions satisfies the criterion of Proposition 12.1: the halves of
`mk a b` are imaginary, orthogonal, and of equal nonzero squared norm. -/
theorem criterion_of_mk_mul_mk_eq_zero (hsq : ∀ x : F, 0 ≤ x * x) {a b c d : Tower F 3}
    (hu : (mk a b : Tower F 4) ≠ 0) (hw : (mk c d : Tower F 4) ≠ 0)
    (h : mk a b * mk c d = 0) :
    re 3 a = 0 ∧ re 3 b = 0 ∧ dot 3 a b = 0 ∧ dot 3 a a = dot 3 b b ∧ dot 3 a a ≠ 0 := by
  obtain ⟨ra, rb, rc, rd⟩ := re_halves_eq_zero_of_mk_mul_eq_zero hsq h hu hw
  have pc := star_eq_neg_of_re_eq_zero rc
  have pd := star_eq_neg_of_re_eq_zero rd
  have hcd : c = 0 → d = 0 → False := fun hc hd => hw (by rw [hc, hd]; rfl)
  have ha : a ≠ 0 := by
    rintro rfl
    have hb : b ≠ 0 := fun hb => hu (by rw [hb]; rfl)
    have h' : mk ((0 : F) • b) ((1 : F) • b) * mk c d = 0 := by
      rw [zero_smul, one_smul]; exact h
    have h'' := (mk_smul_mul_eq_zero_iff hsq b c d (α := (0 : F)) (β := 1) (by norm_num)).1 h'
    exact hcd (eq_zero_of_mul_eq_zero_of_le_three hsq (le_refl 3) hb h''.1)
      (eq_zero_of_mul_eq_zero_of_le_three hsq (le_refl 3) hb h''.2)
  have hb : b ≠ 0 := by
    rintro rfl
    have h' : mk ((1 : F) • a) ((0 : F) • a) * mk c d = 0 := by
      rw [zero_smul, one_smul]; exact h
    have h'' := (mk_smul_mul_eq_zero_iff hsq a c d (α := (1 : F)) (β := 0) (by norm_num)).1 h'
    exact hcd (eq_zero_of_mul_eq_zero_of_le_three hsq (le_refl 3) ha h''.1)
      (eq_zero_of_mul_eq_zero_of_le_three hsq (le_refl 3) ha h''.2)
  have h0 := h
  rw [mk_mul_mk, zero_eq_mk, mk_inj] at h0
  obtain ⟨h1, h2⟩ := h0
  rw [pd] at h1
  rw [pc] at h2
  have e1 : a * c = -(d * b) := by
    have h3 : a * c - -d * b = 0 := h1
    rw [neg_mul, sub_neg_eq_add] at h3
    exact eq_neg_of_add_eq_zero_left h3
  have e2 : d * a = b * c := by
    have h3 : d * a + b * -c = 0 := h2
    rw [mul_neg, ← sub_eq_add_neg] at h3
    exact sub_eq_zero.1 h3
  have hc : c ≠ 0 := by
    intro hc0
    rw [hc0, mul_zero, eq_comm, neg_eq_zero] at e1
    rcases eq_zero_or_eq_zero_of_mul_eq_zero_of_le_three hsq (le_refl 3) e1 with hd | hb0
    · exact hcd hc0 hd
    · exact hb hb0
  have hd : d ≠ 0 := by
    intro hd0
    rw [hd0, zero_mul, neg_zero] at e1
    exact hc (eq_zero_of_mul_eq_zero_of_le_three hsq (le_refl 3) ha e1)
  have hA := dot_self_ne_zero hsq ha
  have hB := dot_self_ne_zero hsq hb
  have hC := dot_self_ne_zero hsq hc
  have hD := dot_self_ne_zero hsq hd
  have n1 : dot 3 (a * c) (a * c) = dot 3 (d * b) (d * b) := by
    rw [e1]
    simp only [dot_neg_left, dot_neg_right, neg_neg]
  have n2 : dot 3 (d * a) (d * a) = dot 3 (b * c) (b * c) := by rw [e2]
  rw [dot_mul_self_of_le_three (le_refl 3), dot_mul_self_of_le_three (le_refl 3)] at n1 n2
  have hAB : dot 3 a a = dot 3 b b := by
    have key : (dot 3 a a - dot 3 b b) * (dot 3 a a + dot 3 b b) * (dot 3 c c * dot 3 d d) = 0 := by
      linear_combination (dot 3 d d * dot 3 a a) * n1 + (dot 3 d d * dot 3 b b) * n2
    have hs : dot 3 a a + dot 3 b b ≠ 0 := fun h0 =>
      hA ((add_eq_zero_iff_of_nonneg (dot_self_nonneg hsq 3 a) (dot_self_nonneg hsq 3 b)).1 h0).1
    rcases mul_eq_zero.1 key with k1 | k1
    · rcases mul_eq_zero.1 k1 with k2 | k2
      · exact sub_eq_zero.1 k2
      · exact absurd k2 hs
    · exact absurd k1 (mul_ne_zero hC hD)
  have f1 : dot 3 c c • a = d * b * c := by
    have h3 : a * c * c = a * (c * c) := right_alternative_of_le_three (le_refl 3) c a
    rw [e1, mul_self_eq_neg_smul_of_re_eq_zero rc] at h3
    simp only [mul_neg, mul_smul_comm', mul_one, neg_mul] at h3
    exact (neg_inj.1 h3).symm
  have f2 : dot 3 d d • a = -(d * (b * c)) := by
    have h4 : d * (d * a) = d * d * a := left_alternative_of_le_three (le_refl 3) d a
    rw [e2, mul_self_eq_neg_smul_of_re_eq_zero rd] at h4
    simp only [neg_mul, smul_mul_assoc', one_mul] at h4
    rw [h4, neg_neg]
  have f3 : (dot 3 c c + dot 3 d d) • a = associator d b c := by
    rw [add_smul, f1, f2]
    unfold associator
    abel
  have f4 : (dot 3 c c + dot 3 d d) * dot 3 a b = 0 := by
    rw [← dot_smul_left, f3]
    exact dot_associator_mid d b c
  have hCD : dot 3 c c + dot 3 d d ≠ 0 := fun h0 =>
    hC ((add_eq_zero_iff_of_nonneg (dot_self_nonneg hsq 3 c) (dot_self_nonneg hsq 3 d)).1 h0).1
  exact ⟨ra, rb, (mul_eq_zero.1 f4).resolve_left hCD, hAB, hA⟩

/-- The nonzero kernel of `SingularKernel` makes `mk a b` a left zero divisor when the criterion
holds. -/
theorem exists_ne_zero_mul_eq_zero_of_criterion (hsq : ∀ x : F, 0 ≤ x * x) {a b : Tower F 3}
    (ha : re 3 a = 0) (hb : re 3 b = 0) (hab : dot 3 a b = 0) (hAB : dot 3 a a = dot 3 b b)
    (hν : dot 3 a a ≠ 0) :
    (mk a b : Tower F 4) ≠ 0 ∧ ∃ x : Tower F 4, x ≠ 0 ∧ mk a b * x = 0 := by
  have hfr := finrank_ker_mulLeft_mk (two_ne_zero_of_sq_nonneg hsq) ha hb hab rfl hAB.symm hν
  refine ⟨fun h => hν ?_, ?_⟩
  · have h' : (mk a b : Tower F 4) = mk 0 0 := h
    rw [(mk_inj.1 h').1, dot_zero_left]
  · by_contra hcon
    have hbot : LinearMap.ker (mulLeft F 4 (mk a b)) = ⊥ :=
      LinearMap.ker_eq_bot'.2 fun y hy => by
        by_contra hy0
        exact hcon ⟨y, hy0, hy⟩
    rw [hbot, finrank_bot] at hfr
    omega

/-- Proposition 12.1 of Biss, Dugger and Isaksen: `mk a b` is a nonzero left zero divisor of the
sedenions exactly when `a` and `b` are imaginary, orthogonal, and of equal nonzero squared norm. -/
theorem mk_isLeftZeroDivisor_iff (hsq : ∀ x : F, 0 ≤ x * x) (a b : Tower F 3) :
    ((mk a b : Tower F 4) ≠ 0 ∧ ∃ x : Tower F 4, x ≠ 0 ∧ mk a b * x = 0) ↔
      re 3 a = 0 ∧ re 3 b = 0 ∧ dot 3 a b = 0 ∧ dot 3 a a = dot 3 b b ∧ dot 3 a a ≠ 0 := by
  constructor
  · rintro ⟨hz, x, hx, hzx⟩
    obtain ⟨c, d, rfl⟩ : ∃ c d : Tower F 3, x = mk c d := ⟨_, _, rfl⟩
    exact criterion_of_mk_mul_mk_eq_zero hsq hz hx hzx
  · rintro ⟨ha, hb, hab, hAB, hν⟩
    exact exists_ne_zero_mul_eq_zero_of_criterion hsq ha hb hab hAB hν

/-- The kernel of left multiplication by a nonzero sedenion has dimension 4 exactly under the
criterion. -/
theorem finrank_ker_mulLeft_mk_eq_four_iff (hsq : ∀ x : F, 0 ≤ x * x) {a b : Tower F 3}
    (hz : (mk a b : Tower F 4) ≠ 0) :
    finrank F (LinearMap.ker (mulLeft F 4 (mk a b))) = 4 ↔
      re 3 a = 0 ∧ re 3 b = 0 ∧ dot 3 a b = 0 ∧ dot 3 a a = dot 3 b b ∧ dot 3 a a ≠ 0 := by
  constructor
  · intro h
    have hne : LinearMap.ker (mulLeft F 4 (mk a b)) ≠ ⊥ := fun hb => by
      rw [hb, finrank_bot] at h
      omega
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hne
    exact (mk_isLeftZeroDivisor_iff hsq a b).1 ⟨hz, x, hx0, LinearMap.mem_ker.1 hx⟩
  · rintro ⟨ha, hb, hab, hAB, hν⟩
    exact finrank_ker_mulLeft_mk (two_ne_zero_of_sq_nonneg hsq) ha hb hab rfl hAB.symm hν

/-- The kernel of left multiplication by a nonzero sedenion has dimension 0 or 4. -/
theorem finrank_ker_mulLeft_mk_eq_zero_or_four (hsq : ∀ x : F, 0 ≤ x * x) {a b : Tower F 3}
    (hz : (mk a b : Tower F 4) ≠ 0) :
    finrank F (LinearMap.ker (mulLeft F 4 (mk a b))) = 0 ∨
      finrank F (LinearMap.ker (mulLeft F 4 (mk a b))) = 4 := by
  by_cases h : re 3 a = 0 ∧ re 3 b = 0 ∧ dot 3 a b = 0 ∧ dot 3 a a = dot 3 b b ∧ dot 3 a a ≠ 0
  · exact Or.inr ((finrank_ker_mulLeft_mk_eq_four_iff hsq hz).2 h)
  · left
    have hbot : LinearMap.ker (mulLeft F 4 (mk a b)) = ⊥ :=
      LinearMap.ker_eq_bot'.2 fun y hy => by
        by_contra hy0
        exact h ((mk_isLeftZeroDivisor_iff hsq a b).1 ⟨hz, y, hy0, hy⟩)
    rw [hbot, finrank_bot]

end Criterion

end Tower

end CayleyDickson
