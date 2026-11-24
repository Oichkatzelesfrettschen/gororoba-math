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
* `Tower.mk_mul_iota_mul_mk_iota_mul_eq_zero`, `Tower.mk_mul_iota_mul_mk_neg_iota_mul_eq_zero`:
  the two inclusions of Theorem 10.2: `(x, i x)` with `a x = 0` and `(y, -i y)` with `y`
  orthogonal to `1`, `i`, `a` and `i a` lie in the kernel of left multiplication by `(a, i a)`,
  `i = (0, 1)`; `Tower.mul_add_mul_of_star_eq_neg` is the polarization `u v + v u = -2 ⟨u, v⟩`
  of pure elements that the second one rests on.
* `Tower.two_pow_sub_four_add_finrank_ker_le`: the lower bound
  `2 ^ n - 4 + dim Ann a ≤ dim Ann (a, i a)` of the dimension count of Theorem 10.2.
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

section Isotropic

variable {K : Type u} [Field K] [StarRing K] [TrivialStar K] [PartialOrder K]
  [IsOrderedAddMonoid K]

omit [PartialOrder K] [IsOrderedAddMonoid K] in
/-- The square of a pure element is minus its norm times `1`. -/
theorem mul_self_of_star_eq_neg {j : ℕ} {u : Tower K j} (hu : star u = -u) :
    u * u = (-dot j u u) • (1 : Tower K j) := by
  have h := (mul_star_eq_dot j u).1
  rw [hu, mul_neg] at h
  rw [neg_smul, ← h, neg_neg]

omit [PartialOrder K] [IsOrderedAddMonoid K] in
/-- Polarization for pure elements: `u v + v u = -2 ⟨u, v⟩`, with no associativity. -/
theorem mul_add_mul_of_star_eq_neg {j : ℕ} {u v : Tower K j} (hu : star u = -u)
    (hv : star v = -v) : u * v + v * u = (-2 * dot j u v) • (1 : Tower K j) := by
  have hs : star (u + v) = -(u + v) := by rw [star_add, hu, hv, neg_add]
  have e : (u + v) * (u + v) = u * u + (u * v + v * u) + v * v := by
    rw [mul_add, add_mul, add_mul]
    abel
  calc u * v + v * u = (u + v) * (u + v) - u * u - v * v := by rw [e]; abel
    _ = (-dot j (u + v) (u + v)) • (1 : Tower K j) - (-dot j u u) • (1 : Tower K j) -
        (-dot j v v) • (1 : Tower K j) := by
      rw [mul_self_of_star_eq_neg hs, mul_self_of_star_eq_neg hu, mul_self_of_star_eq_neg hv]
    _ = (-2 * dot j u v) • (1 : Tower K j) := by
      rw [dot_add_left, dot_add_right, dot_add_right, dot_comm j v u]
      module

omit [PartialOrder K] [IsOrderedAddMonoid K] in
/-- The isotropic pair `(a, i a)` with `a = (p, q)` pure and the vector `(y, -i y)` with
`y = (y₁, y₂)` pure multiply to zero when `⟨y₁, p⟩ + ⟨y₂, q⟩ = 0` and `⟨y₁, q⟩ = ⟨y₂, p⟩`: every
component of the product is a sum of the polarized squares `u v + v u = -2 ⟨u, v⟩` of pure elements,
and the two orthogonality relations cancel those sums. -/
theorem mk_mk_mul_mk_mk_eq_zero {j : ℕ} {p q y1 y2 : Tower K j} (hp : star p = -p)
    (hq : star q = -q) (hy1 : star y1 = -y1) (hy2 : star y2 = -y2)
    (h1 : dot j y1 p + dot j y2 q = 0) (h2 : dot j y1 q = dot j y2 p) :
    mk (mk p q) (mk q (-p)) * mk (mk y1 y2) (mk (-y2) y1) = 0 := by
  simp only [mk_mul_mk, star_mk, star_neg, hp, hq, hy1, hy2, mul_neg, neg_mul, neg_neg,
    sub_neg_eq_add, sub_mk, add_mk, zero_eq_mk, mk_inj]
  refine ⟨⟨by abel, ?_⟩, ⟨by abel, ?_⟩⟩
  · have P1 := mul_add_mul_of_star_eq_neg hy2 hp
    have P2 := mul_add_mul_of_star_eq_neg hq hy1
    calc y2 * p + -(q * y1) - (-(p * y2) + y1 * q) = (y2 * p + p * y2) - (q * y1 + y1 * q) := by
          abel
      _ = 0 := by rw [P1, P2, dot_comm j q y1, ← h2, sub_self]
  · have P3 := mul_add_mul_of_star_eq_neg hq hy2
    have P4 := mul_add_mul_of_star_eq_neg hy1 hp
    have h3 : dot j y1 p = -dot j y2 q := eq_neg_of_add_eq_zero_left h1
    calc -(q * y2) + -(y1 * p) + (-(y2 * q) + -(p * y1))
        = -((q * y2 + y2 * q) + (y1 * p + p * y1)) := by abel
      _ = 0 := by
        rw [P3, P4, dot_comm j q y2, h3]
        module

omit [TrivialStar K] [PartialOrder K] [IsOrderedAddMonoid K] in
/-- Left multiplication by the adjoined unit `i = (0, 1)` on a pair of pure elements swaps and
negates its halves: `i (p, q) = (q, -p)`. -/
theorem iota_mul_mk_of_star_eq_neg {j : ℕ} {p q : Tower K j} (hp : star p = -p)
    (hq : star q = -q) : mk (0 : Tower K j) 1 * mk p q = mk q (-p) := by
  rw [mk_mul_mk, zero_mul, mul_one, zero_sub, hq, neg_neg, mul_zero, one_mul, zero_add, hp]

/-- The inclusion of Theorem 10.2 of Biss, Dugger and Isaksen for the vectors `(y, -i y)`: when
`a` is orthogonal to the complex line `⟨1, i⟩` and `y` is orthogonal to `1`, `i`, `a` and `i a`
(that is, to the quaternionic span of `a` and `i`), the pair `(y, -i y)` lies in the kernel of
left multiplication by `(a, i a)`, where `i = (0, 1)` is the adjoined unit of the level of `a`. -/
theorem mk_mul_iota_mul_mk_neg_iota_mul_eq_zero {j : ℕ} {a y : Tower K (j + 1)}
    (ha1 : dot (j + 1) a 1 = 0) (ha2 : dot (j + 1) a (mk (0 : Tower K j) 1) = 0)
    (hy1 : dot (j + 1) y 1 = 0) (hy2 : dot (j + 1) y (mk (0 : Tower K j) 1) = 0)
    (hya : dot (j + 1) y a = 0) (hyia : dot (j + 1) y (mk (0 : Tower K j) 1 * a) = 0) :
    mk a (mk (0 : Tower K j) 1 * a) * mk y (-(mk (0 : Tower K j) 1 * y)) = 0 := by
  obtain ⟨p, q, rfl⟩ : ∃ p q : Tower K j, a = mk p q := ⟨_, _, rfl⟩
  obtain ⟨y1, y2, rfl⟩ : ∃ y1 y2 : Tower K j, y = mk y1 y2 := ⟨_, _, rfl⟩
  rw [dot_one_right, re_mk] at ha1 hy1
  rw [dot_mk, dot_zero_right, zero_add, dot_one_right] at ha2 hy2
  have hp : star p = -p := star_eq_neg_of_re_eq_zero ha1
  have hq : star q = -q := star_eq_neg_of_re_eq_zero ha2
  have hy1' : star y1 = -y1 := star_eq_neg_of_re_eq_zero hy1
  have hy2' : star y2 = -y2 := star_eq_neg_of_re_eq_zero hy2
  rw [iota_mul_mk_of_star_eq_neg hp hq, dot_mk, dot_neg_right] at hyia
  rw [iota_mul_mk_of_star_eq_neg hp hq, iota_mul_mk_of_star_eq_neg hy1' hy2', neg_mk, neg_neg]
  rw [dot_mk] at hya
  exact mk_mk_mul_mk_mk_eq_zero hp hq hy1' hy2' hya (by linear_combination hyia)

/-- The inclusion of Theorem 10.2 of Biss, Dugger and Isaksen for the vectors `(x, i x)`: when
`a = (p, q)` has pure halves and `a x = 0`, the pair `(x, i x)` lies in the kernel of left
multiplication by `(a, i a)`. The theorem is the case `α = 1`, `β = i` of the inclusion of
Theorem 10.1 with scalars of the complex line, which holds although `α ^ 2 + β ^ 2 = 0`, with
`i x` in the kernel by Lemma 9.6. -/
theorem mk_mul_iota_mul_mk_iota_mul_eq_zero (hsq : ∀ x : K, 0 ≤ x * x) {j : ℕ} {p q : Tower K j}
    (hp : star p = -p) (hq : star q = -q) {x : Tower K (j + 1)} (hx : mk p q * x = 0) :
    mk (mk p q) (mk (0 : Tower K j) 1 * mk p q) * mk x (mk (0 : Tower K j) 1 * x) = 0 := by
  have hy : mk p q * (mk (0 : Tower K j) 1 * x) = 0 := by
    have := mul_cs_mul_eq_zero hp hq hx 0 1
    have hc : (cs 0 1 : Tower K (j + 1)) = mk (0 : Tower K j) 1 := by
      simp only [cs, zero_smul, zero_add, one_smul]
    rwa [hc] at this
  have := mk_cs_mul_eq_zero_of_mul_eq_zero hsq hx hy 1 0 0 1
  have hc0 : (cs 0 1 : Tower K (j + 1)) = mk (0 : Tower K j) 1 := by
    simp only [cs, zero_smul, zero_add, one_smul]
  have hc1 : (cs 1 0 : Tower K (j + 1)) = 1 := by
    simp only [cs, one_smul, zero_smul, add_zero]
  rwa [hc0, hc1, one_mul] at this

omit [TrivialStar K] [PartialOrder K] [IsOrderedAddMonoid K] in
/-- Left multiplication by the adjoined unit `i = (0, 1)` squares to minus the identity:
`i (i z) = -z`. -/
theorem iota_mul_iota_mul {j : ℕ} (z : Tower K (j + 1)) :
    mk (0 : Tower K j) 1 * (mk (0 : Tower K j) 1 * z) = -z := by
  obtain ⟨z1, z2, rfl⟩ : ∃ z1 z2 : Tower K j, z = mk z1 z2 := ⟨_, _, rfl⟩
  simp only [mk_mul_mk, zero_mul, mul_one, one_mul, mul_zero, zero_sub, zero_add, star_neg,
    star_star, neg_mk]

end Isotropic

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

/-- One half of the dimension count of Theorem 10.2 of Biss, Dugger and Isaksen: for `a`
orthogonal to the complex line, the kernel of left multiplication by `(a, i a)` has dimension at
least `2 ^ n - 4` plus the dimension of the kernel of `a` (`n` the level of `a`). The vectors
`(x + y, i (x - y))`, with `x` annihilated by `a` and `y` orthogonal to `1`, `i`, `a`, `i a`, are
annihilated by the pair (the two inclusions above) and determine `(x, y)`, since left
multiplication by `i` squares to `-1`; four linear conditions cut `y` from a space of dimension
`2 ^ n`. -/
theorem two_pow_sub_four_add_finrank_ker_le {j : ℕ} {a : Tower ℝ (j + 1)}
    (ha1 : dot (j + 1) a 1 = 0) (ha2 : dot (j + 1) a (mk (0 : Tower ℝ j) 1) = 0) :
    2 ^ (j + 1) - 4 + finrank ℝ (LinearMap.ker (mulLeft ℝ (j + 1) a)) ≤
      finrank ℝ (LinearMap.ker (mulLeft ℝ (j + 1 + 1) (mk a (mk (0 : Tower ℝ j) 1 * a)))) := by
  have hsq : ∀ y : ℝ, 0 ≤ y * y := fun y => mul_self_nonneg y
  let dotL : Tower ℝ (j + 1) → Tower ℝ (j + 1) →ₗ[ℝ] ℝ := fun v =>
    { toFun := fun y => dot (j + 1) y v
      map_add' := fun x y => dot_add_left (j + 1) x y v
      map_smul' := fun r x => by
        rw [dot_smul_left]
        rfl }
  let f : Tower ℝ (j + 1) →ₗ[ℝ] ℝ × ℝ × ℝ × ℝ :=
    (dotL 1).prod ((dotL (mk (0 : Tower ℝ j) 1)).prod
      ((dotL a).prod (dotL (mk (0 : Tower ℝ j) 1 * a))))
  let iL : Tower ℝ (j + 1) →ₗ[ℝ] Tower ℝ (j + 1) := mulLeft ℝ (j + 1) (mk (0 : Tower ℝ j) 1)
  let X := LinearMap.ker (mulLeft ℝ (j + 1) a)
  let Y := LinearMap.ker f
  let Φ : X × Y →ₗ[ℝ] Tower ℝ (j + 1 + 1) :=
    (CayleyDickson.linearEquivProd (Tower ℝ (j + 1)) ℝ).symm.toLinearMap ∘ₗ
      LinearMap.prod (X.subtype ∘ₗ LinearMap.fst ℝ X Y + Y.subtype ∘ₗ LinearMap.snd ℝ X Y)
        (iL ∘ₗ (X.subtype ∘ₗ LinearMap.fst ℝ X Y - Y.subtype ∘ₗ LinearMap.snd ℝ X Y))
  have hΦ : ∀ z : X × Y, Φ z = mk (z.1.1 + z.2.1) (mk (0 : Tower ℝ j) 1 * (z.1.1 - z.2.1)) :=
    fun z => rfl
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    rw [hΦ, zero_eq_mk, mk_inj] at hz
    obtain ⟨h1, h2⟩ := hz
    have h3 : z.1.1 - z.2.1 = 0 := by
      have := iota_mul_iota_mul (j := j) (z.1.1 - z.2.1)
      rw [h2, mul_zero] at this
      exact neg_eq_zero.1 this.symm
    have h4 : z.1.1 = z.2.1 := sub_eq_zero.1 h3
    have h5 : z.1.1 = 0 := by
      rw [← h4, ← two_smul ℝ z.1.1] at h1
      exact (smul_eq_zero.1 h1).resolve_left two_ne_zero
    refine Prod.ext (Subtype.ext h5) (Subtype.ext ?_)
    rw [← h4, h5]
    rfl
  obtain ⟨p, q, rfl⟩ : ∃ p q : Tower ℝ j, a = mk p q := ⟨_, _, rfl⟩
  have ha1' := ha1
  have ha2' := ha2
  rw [dot_one_right, re_mk] at ha1'
  rw [dot_mk, dot_zero_right, zero_add, dot_one_right] at ha2'
  have hp : star p = -p := star_eq_neg_of_re_eq_zero ha1'
  have hq : star q = -q := star_eq_neg_of_re_eq_zero ha2'
  have hle : LinearMap.range Φ ≤ LinearMap.ker (mulLeft ℝ (j + 1 + 1)
      (mk (mk p q) (mk (0 : Tower ℝ j) 1 * mk p q))) := by
    rintro _ ⟨⟨x, y⟩, rfl⟩
    have hy := LinearMap.mem_ker.1 y.2
    have hy1 : dot (j + 1) y.1 1 = 0 := congrArg Prod.fst hy
    have hy2 : dot (j + 1) y.1 (mk (0 : Tower ℝ j) 1) = 0 := congrArg (fun t => t.2.1) hy
    have hya : dot (j + 1) y.1 (mk p q) = 0 := congrArg (fun t => t.2.2.1) hy
    have hyia : dot (j + 1) y.1 (mk (0 : Tower ℝ j) 1 * mk p q) = 0 :=
      congrArg (fun t => t.2.2.2) hy
    have hx : mk p q * x.1 = 0 := x.2
    have e : mk (x.1 + y.1) (mk (0 : Tower ℝ j) 1 * (x.1 - y.1)) =
        mk x.1 (mk (0 : Tower ℝ j) 1 * x.1) + mk y.1 (-(mk (0 : Tower ℝ j) 1 * y.1)) := by
      rw [add_mk, mul_sub, sub_eq_add_neg]
    rw [LinearMap.mem_ker, mulLeft_apply, hΦ, e, mul_add,
      mk_mul_iota_mul_mk_iota_mul_eq_zero hsq hp hq hx,
      mk_mul_iota_mul_mk_neg_iota_mul_eq_zero ha1 ha2 hy1 hy2 hya hyia, add_zero]
  have h6 := Submodule.finrank_mono hle
  have h7 := LinearMap.finrank_range_of_inj hinj
  have h8 : finrank ℝ (X × Y) = finrank ℝ X + finrank ℝ Y := Module.finrank_prod
  have h9 := LinearMap.finrank_range_add_finrank_ker f
  have h10 : finrank ℝ (LinearMap.range f) ≤ 4 := by
    have := Submodule.finrank_le (LinearMap.range f)
    simpa [Module.finrank_prod] using this
  have hXg : finrank ℝ X = finrank ℝ (LinearMap.ker (mulLeft ℝ (j + 1) (mk p q))) := rfl
  have hYd : finrank ℝ Y = finrank ℝ (LinearMap.ker f) := rfl
  have h11 : finrank ℝ (Tower ℝ (j + 1)) = 2 ^ (j + 1) := finrank_eq ℝ (j + 1)
  omega

end Real

end Tower

end CayleyDickson
