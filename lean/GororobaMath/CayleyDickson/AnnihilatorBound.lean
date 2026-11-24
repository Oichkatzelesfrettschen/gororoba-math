/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.ScaledPairAnnihilator
public import GororobaMath.CayleyDickson.MorenoKernel
public import GororobaMath.CayleyDickson.NormMultiplicative

/-!
# The dimension bound for annihilators of Cayley-Dickson elements

Convention: the product of `Tower R k` is the Cayley-Dickson product of
`GororobaMath.CayleyDickson.Tower`, `(a, b) (c, d) = (a c - star d b, d a + b star c)`, and
`Tower.mk` builds a pair. Biss, Dugger and Isaksen, Large annihilators in Cayley-Dickson
algebras (arXiv:math/0511691, 2005), write the same product; their `Ann x` is the kernel of
left multiplication by `x`, the library's `LinearMap.ker (Tower.mulLeft K k x)`, and their
`A_n` is `Tower ℝ n`. Their Lemma 9.9 for `a, b ∈ A_(n-1)` reads here with `a b` at level
`k = n - 1`, the pair `mk a b` at level `k + 1`, and `2 ^ k` for the dimension of `A_(n-1)`.
The ordered-field hypotheses are those of `GororobaMath.CayleyDickson.ScaledPairAnnihilator`; the
divisibility by four of `GororobaMath.CayleyDickson.MorenoKernel` fixes the reals for the final
bound.

## Main results

* `Tower.finrank_ker_mulLeft_mk_le`: Lemma 9.9 of the paper, before its parity step: for a
  nonzero pair, the kernel of `(a, b)` has dimension at most `2 ^ k - 1` plus the dimension of
  the common kernel of `a` and `b`.
* `Tower.four_dvd_finrank_ker_mulLeft_of_ne_zero`: for nonzero `x` at level `k + 1 ≥ 2` over the
  reals, the kernel of left multiplication has dimension divisible by four.
* `Tower.finrank_ker_mulLeft_add_le`: Proposition 9.10 of the paper: for nonzero `x` at level
  `n ≥ 2`, the kernel has dimension at most `2 ^ n - 4 n + 4`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

open Module

section Halves

variable (K : Type u) [Field K] [StarRing K] (k : ℕ)

/-- The first half of a pair of level `k + 1` as a linear map. -/
def reHalf : Tower K (k + 1) →ₗ[K] Tower K k where
  toFun x := CayleyDickson.re (A := Tower K k) x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The second half of a pair of level `k + 1` as a linear map. -/
def imHalf : Tower K (k + 1) →ₗ[K] Tower K k where
  toFun x := CayleyDickson.im (A := Tower K k) x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {K k}

theorem reHalf_mk (a b : Tower K k) : reHalf K k (mk a b) = a := rfl

theorem imHalf_mk (a b : Tower K k) : imHalf K k (mk a b) = b := rfl

theorem eq_mk_reHalf_imHalf (z : Tower K (k + 1)) : z = mk (reHalf K k z) (imHalf K k z) := rfl

theorem eq_mk_zero_of_imHalf_eq_zero {z : Tower K (k + 1)} (h : imHalf K k z = 0) :
    z = mk (reHalf K k z) 0 := by
  have e := eq_mk_reHalf_imHalf z
  rwa [h] at e

end Halves

section Field

variable {K : Type u} [Field K] [StarRing K] [TrivialStar K] [PartialOrder K]
  [IsOrderedAddMonoid K]

/-- A nonzero pair that kills `(c, 0)` puts `c` in the kernels of both halves: `c` is imaginary
(Lemma 9.5), so `b star c = - b c`. -/
theorem mul_eq_zero_of_mk_mul_mk_zero (hsq : ∀ x : K, 0 ≤ x * x) {k : ℕ} {a b c : Tower K k}
    (h : mk a b ≠ 0) (h0 : mk a b * mk c 0 = 0) : a * c = 0 ∧ b * c = 0 := by
  by_cases hc : c = 0
  · rw [hc, mul_zero, mul_zero]
    exact ⟨rfl, rfl⟩
  have hw : mk c 0 ≠ 0 := by
    intro h1
    rw [zero_eq_mk, mk_inj] at h1
    exact hc h1.1
  obtain ⟨-, -, rc, -⟩ := re_halves_eq_zero_of_mk_mul_eq_zero hsq h0 h hw
  have sc : star c = -c := star_eq_neg_of_re_eq_zero rc
  rw [mk_mul_mk, zero_eq_mk, mk_inj] at h0
  obtain ⟨h1, h2⟩ := h0
  rw [star_zero, zero_mul, sub_zero] at h1
  rw [zero_mul, zero_add, sc, mul_neg, neg_eq_zero] at h2
  exact ⟨h1, h2⟩

/-- The second half of a vector annihilated by a nonzero pair is imaginary (Lemma 9.5). -/
theorem re_snd_eq_zero_of_mk_mul_mk (hsq : ∀ x : K, 0 ≤ x * x) {k : ℕ} {a b c d : Tower K k}
    (h : mk a b ≠ 0) (h0 : mk a b * mk c d = 0) : re k d = 0 := by
  by_cases hw : mk c d = 0
  · rw [zero_eq_mk, mk_inj] at hw
    rw [hw.2]
    exact (dot_one_right k 0).symm.trans (dot_zero_left k 1)
  exact (re_halves_eq_zero_of_mk_mul_eq_zero hsq h0 h hw).2.2.2

/-- Lemma 9.9 of Biss, Dugger and Isaksen before its parity step: the map sending a vector
`(c, d)` of the kernel of a nonzero pair `(a, b)` to `d` has image among the imaginary vectors,
a hyperplane of dimension `2 ^ k - 1`, and kernel `{(c, 0)}`, which maps into the common kernel of
`a` and `b` through `(c, 0) ↦ c`. -/
theorem finrank_ker_mulLeft_mk_le (hsq : ∀ x : K, 0 ≤ x * x) {k : ℕ} {a b : Tower K k}
    (h : mk a b ≠ 0) :
    finrank K (LinearMap.ker (mulLeft K (k + 1) (mk a b))) ≤
      2 ^ k - 1 + finrank K (↥(LinearMap.ker (mulLeft K k a) ⊓ LinearMap.ker (mulLeft K k b) :
        Submodule K (Tower K k))) := by
  set N := LinearMap.ker (mulLeft K (k + 1) (mk a b)) with hN
  let φ : N →ₗ[K] Tower K k := imHalf K k ∘ₗ N.subtype
  let ρ : N →ₗ[K] Tower K k := reHalf K k ∘ₗ N.subtype
  let reLin : Tower K k →ₗ[K] K :=
    { toFun := fun x => dot k x 1
      map_add' := fun x y => dot_add_left k x y 1
      map_smul' := fun r x => by
        rw [dot_smul_left]
        rfl }
  have hfin : finrank K (Tower K k) = 2 ^ k := finrank_eq K k
  have : Nontrivial (Tower K k) := Module.nontrivial_of_finrank_pos (by rw [hfin]; positivity)
  have hrange : LinearMap.range φ ≤ LinearMap.ker reLin := by
    rintro _ ⟨x, rfl⟩
    have hx' : mk a b * mk (reHalf K k x.1) (imHalf K k x.1) = 0 := x.2
    change dot k (imHalf K k x.1) 1 = 0
    rw [dot_one_right]
    exact re_snd_eq_zero_of_mk_mul_mk hsq h hx'
  have hne : LinearMap.ker reLin ≠ ⊤ := by
    intro htop
    have h1 : (1 : Tower K k) ∈ LinearMap.ker reLin := by rw [htop]; trivial
    have h2 : dot k (1 : Tower K k) 1 = 0 := h1
    exact dot_self_ne_zero hsq one_ne_zero h2
  have h3 : finrank K (LinearMap.range φ) ≤ 2 ^ k - 1 := by
    have := Submodule.finrank_mono hrange
    have h4 := Submodule.finrank_lt hne
    omega
  let g : LinearMap.ker φ →ₗ[K] ↥(LinearMap.ker (mulLeft K k a) ⊓ LinearMap.ker (mulLeft K k b)) :=
    LinearMap.codRestrict _ (ρ ∘ₗ (LinearMap.ker φ).subtype) (by
      intro x
      have hd : imHalf K k x.1.1 = 0 := LinearMap.mem_ker.1 x.2
      have hx : mk a b * x.1.1 = 0 := x.1.2
      rw [eq_mk_zero_of_imHalf_eq_zero hd] at hx
      obtain ⟨h1, h2⟩ := mul_eq_zero_of_mk_mul_mk_zero hsq h hx
      exact ⟨LinearMap.mem_ker.2 h1, LinearMap.mem_ker.2 h2⟩)
  have hg : Function.Injective g := by
    intro x x' he
    have hc : reHalf K k x.1.1 = reHalf K k x'.1.1 := congrArg Subtype.val he
    have hd : imHalf K k x.1.1 = 0 := LinearMap.mem_ker.1 x.2
    have hd' : imHalf K k x'.1.1 = 0 := LinearMap.mem_ker.1 x'.2
    refine Subtype.ext (Subtype.ext ?_)
    rw [eq_mk_zero_of_imHalf_eq_zero hd, eq_mk_zero_of_imHalf_eq_zero hd', hc]
  have h5 := LinearMap.finrank_le_finrank_of_injective hg
  have h6 := LinearMap.finrank_range_add_finrank_ker φ
  omega

end Field

section Real

/-- Moreno's divisibility by four for every nonzero element of level `k + 1 ≥ 2`: a nonzero
element without annihilator has kernel dimension `0`, and a zero divisor has imaginary halves
(Lemma 9.5). -/
theorem four_dvd_finrank_ker_mulLeft_of_ne_zero {k : ℕ} (hk : 1 ≤ k) {x : Tower ℝ (k + 1)}
    (hx : x ≠ 0) : 4 ∣ finrank ℝ (LinearMap.ker (mulLeft ℝ (k + 1) x)) := by
  have hsq : ∀ y : ℝ, 0 ≤ y * y := fun y => mul_self_nonneg y
  obtain ⟨p, q, rfl⟩ : ∃ p q : Tower ℝ k, x = mk p q := ⟨_, _, rfl⟩
  by_cases hz : ∀ y : Tower ℝ (k + 1), mk p q * y = 0 → y = 0
  · have : LinearMap.ker (mulLeft ℝ (k + 1) (mk p q)) = ⊥ :=
      LinearMap.ker_eq_bot'.2 fun y hy => hz y hy
    rw [this, finrank_bot]
    exact dvd_zero 4
  · push Not at hz
    obtain ⟨y, hy, hy0⟩ := hz
    obtain ⟨y1, y2, rfl⟩ : ∃ y1 y2 : Tower ℝ k, y = mk y1 y2 := ⟨_, _, rfl⟩
    obtain ⟨rp, rq, -, -⟩ := re_halves_eq_zero_of_mk_mul_eq_zero hsq hy hx hy0
    exact four_dvd_finrank_ker_mulLeft_mk hk (star_eq_neg_of_re_eq_zero rp)
      (star_eq_neg_of_re_eq_zero rq)

/-- The levels up to `3` have no zero divisors: the kernel of a nonzero element is `0`. -/
theorem finrank_ker_mulLeft_eq_zero_of_le_three {k : ℕ} (hk : k ≤ 3) {x : Tower ℝ k}
    (hx : x ≠ 0) : finrank ℝ (LinearMap.ker (mulLeft ℝ k x)) = 0 := by
  have hsq : ∀ y : ℝ, 0 ≤ y * y := fun y => mul_self_nonneg y
  have : LinearMap.ker (mulLeft ℝ k x) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun y hy => ?_
    by_contra hy0
    have h1 := dot_mul_self_of_le_three hk x y
    have h2 : x * y = 0 := hy
    rw [h2, dot_zero_left] at h1
    exact mul_ne_zero (dot_self_ne_zero hsq hx) (dot_self_ne_zero hsq hy0) h1.symm
  rw [this, finrank_bot]

/-- Proposition 9.10 of Biss, Dugger and Isaksen: for nonzero `x` at level `n ≥ 2`, the kernel of
left multiplication has dimension at most `2 ^ n - 4 n + 4`, written without truncated
subtraction. Levels 2 and 3 have no zero divisors; a step from `k` to `k + 1` combines
Lemma 9.9 with the bound on whichever half is nonzero and the divisibility by four. -/
theorem finrank_ker_mulLeft_add_le {n : ℕ} (hn : 2 ≤ n) (x : Tower ℝ n) (hx : x ≠ 0) :
    finrank ℝ (LinearMap.ker (mulLeft ℝ n x)) + 4 * n ≤ 2 ^ n + 4 := by
  have hsq : ∀ y : ℝ, 0 ≤ y * y := fun y => mul_self_nonneg y
  induction n, hn using Nat.le_induction with
  | base =>
    have := finrank_ker_mulLeft_eq_zero_of_le_three (by norm_num : 2 ≤ 3) hx
    omega
  | succ n hn ih =>
    by_cases h3 : n + 1 ≤ 3
    · have := finrank_ker_mulLeft_eq_zero_of_le_three h3 hx
      have h4 : n ≤ 2 := by omega
      have h5 : n = 2 := by omega
      subst h5
      omega
    obtain ⟨a, b, rfl⟩ : ∃ a b : Tower ℝ n, x = mk a b := ⟨_, _, rfl⟩
    have h4 := finrank_ker_mulLeft_mk_le hsq hx
    have h5 := four_dvd_finrank_ker_mulLeft_of_ne_zero (by omega : 1 ≤ n) hx
    have h6 : 4 ∣ 2 ^ n := by
      have := pow_dvd_pow 2 hn
      simpa using this
    have h7 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have h8 : finrank ℝ (↥(LinearMap.ker (mulLeft ℝ n a) ⊓ LinearMap.ker (mulLeft ℝ n b) :
        Submodule ℝ (Tower ℝ n))) + 4 * n ≤
        2 ^ n + 4 := by
      by_cases ha : a = 0
      · have hb : b ≠ 0 := by
          intro hb
          apply hx
          rw [ha, hb]
          rfl
        have := ih b hb
        have hle : LinearMap.ker (mulLeft ℝ n a) ⊓ LinearMap.ker (mulLeft ℝ n b) ≤
            LinearMap.ker (mulLeft ℝ n b) := inf_le_right
        have := Submodule.finrank_mono hle
        omega
      · have := ih a ha
        have hle : LinearMap.ker (mulLeft ℝ n a) ⊓ LinearMap.ker (mulLeft ℝ n b) ≤
            LinearMap.ker (mulLeft ℝ n a) := inf_le_left
        have := Submodule.finrank_mono hle
        omega
    rw [pow_succ]
    omega

end Real

end Tower

end CayleyDickson
