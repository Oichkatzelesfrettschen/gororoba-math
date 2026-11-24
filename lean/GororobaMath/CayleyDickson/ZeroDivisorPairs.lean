/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TraceForm
public import GororobaMath.CayleyDickson.NormMultiplicative

/-!
# The identities of a sedenion pair with zero product

Convention: `Tower K k` is the tower of `GororobaMath.CayleyDickson.Tower` over a field `K` whose
star is the identity, with the product `(a, b) (c, d) = (a c - star d b, d a + b star c)`.
A sedenion is `mk p q` with `p` and `q` octonions (level 3), and `dot 3 x y` is the sum of the
products of the eight coordinates of `x` and `y`. For the pair `a = (p, q)`, `b = (c, d)` the
coordinate `a_0` is `re 3 p`, the coordinate `a_8` is `re 3 q`, `p_a = p`, `q_a = q`,
`p_b = c` and `q_b = d`. The quantities of the A5 strata are the real and imaginary parts of the
complex bilinear form on `x + i u` and `y + i v`: `cRe x u y v = x . y - u . v` and
`cIm x u y v = x . v + u . y`. With `z_a = p + i c` and `z_q = q + i d` they give
`U = z_a . z_a`, `V = z_q . z_q` and `W = z_a . z_q`, and `mu` is the pair `(a_8, b_8)`.

The kernel system `PairKer p q c d` is `p c + d q = 0` and `d p - q c = 0`, the product
`(p, q) (c, d) = 0` for pure `c` and `d`. The sedenion zero divisors satisfy `a_0 = a_8 = 0`
(Lemma 9.5 of Biss, Dugger and Isaksen), so the system applies to every pair `a b = 0` of nonzero
sedenions. Its solutions are closed under `(c, d) -> (d, -c)` and, with the roles of the two
operands exchanged, under `(p, q) -> (q, -p)`. Polarizing the norm law of the octonions along
these rotations gives the identities below. The identities need an order on `K`.

## Main results

* `Tower.sedenion_pair_identities`: for nonzero sedenions `a b = 0` over an ordered field,
  `a_0 = a_8 = b_0 = b_8 = 0`, `U - V = 0`, `W = 0`, `Im U = 0` and `Im V = 0`, with
  `Re U = |p_a|^2 - |p_b|^2` by definition.
* `Tower.dot_eq_iff_cRe_eq_zero`: `|a| = |b|` exactly when `Re U = 0`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

section Kernel

variable {K : Type u} [Field K] [StarRing K] [TrivialStar K]

/-- The kernel system of `(p, q) (c, d) = 0` for pure `c` and `d`. -/
def PairKer {k : ℕ} (p q c d : Tower K k) : Prop :=
  p * c + d * q = 0 ∧ d * p - q * c = 0

omit [TrivialStar K] in
/-- The real coordinate of `1` of `-x` is the negative of that of `x`. -/
theorem re_neg_eq (k : ℕ) (x : Tower K k) : re k (-x) = -re k x := by
  rw [← dot_one_right, ← dot_one_right, dot_neg_left]

omit [TrivialStar K] in
/-- The real coordinate of `1` of `0` vanishes. -/
theorem re_zero_eq (k : ℕ) : re k (0 : Tower K k) = 0 := by
  rw [← dot_one_right, dot_zero_left]

/-- For pure `y`, the coordinate of `1` of `x * y` is `-dot x y`. -/
theorem re_mul_of_star_eq_neg {k : ℕ} (x : Tower K k) {y : Tower K k} (hy : star y = -y) :
    re k (x * y) = -dot k x y := by
  have h := re_mul_star x y
  rw [hy, mul_neg, re_neg_eq] at h
  linear_combination -h

/-- For orthogonal pure `x` and `y`, the product anticommutes. -/
theorem mul_comm_neg_of_dot_eq_zero {k : ℕ} {x y : Tower K k} (hx : star x = -x)
    (hy : star y = -y) (h : dot k x y = 0) : y * x = -(x * y) := by
  have h1 := star_add_self k (x * y)
  rw [star_mul, hx, hy, neg_mul_neg, re_mul_of_star_eq_neg x hy, h, neg_zero, mul_zero,
    zero_smul] at h1
  exact eq_neg_of_add_eq_zero_left h1

omit [TrivialStar K] in
/-- `(p, q) (c, d) = 0` for pure `c` and `d` exactly when the kernel system holds. -/
theorem mk_mul_mk_eq_zero_iff_pairKer {k : ℕ} {p q c d : Tower K k} (hc : star c = -c)
    (hd : star d = -d) : mk p q * mk c d = 0 ↔ PairKer p q c d := by
  rw [mk_mul_mk, zero_eq_mk, mk_inj, hc, hd]
  simp only [PairKer, neg_mul, mul_neg, sub_neg_eq_add, ← sub_eq_add_neg]

omit [TrivialStar K] in
/-- The conjugate of the kernel system, for pure entries. -/
theorem pairKer_star {k : ℕ} {p q c d : Tower K k} (hp : star p = -p) (hq : star q = -q)
    (hc : star c = -c) (hd : star d = -d) (h : PairKer p q c d) :
    c * p + q * d = 0 ∧ p * d - c * q = 0 := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · have := congrArg star h1
    rw [star_add, star_mul, star_mul, hp, hq, hc, hd, star_zero, neg_mul_neg,
      neg_mul_neg] at this
    exact this
  · have := congrArg star h2
    rw [star_sub, star_mul, star_mul, hp, hq, hc, hd, star_zero, neg_mul_neg,
      neg_mul_neg] at this
    exact this

omit [TrivialStar K] in
/-- The kernel system is symmetric in the two operands. -/
theorem pairKer_swap {k : ℕ} {p q c d : Tower K k} (hp : star p = -p) (hq : star q = -q)
    (hc : star c = -c) (hd : star d = -d) (h : PairKer p q c d) : PairKer c d p q :=
  ⟨(pairKer_star hp hq hc hd h).1, sub_eq_zero.2 (sub_eq_zero.1 h.2).symm⟩

omit [TrivialStar K] in
/-- The solutions of the kernel system are closed under `(c, d) -> (d, -c)`. -/
theorem pairKer_rot {k : ℕ} {p q c d : Tower K k} (hp : star p = -p) (hq : star q = -q)
    (hc : star c = -c) (hd : star d = -d) (h : PairKer p q c d) : PairKer p q d (-c) := by
  obtain ⟨e1, e2⟩ := pairKer_star hp hq hc hd h
  refine ⟨?_, ?_⟩
  · rw [neg_mul, ← sub_eq_add_neg]
    exact e2
  · have : -c * p - q * d = -(c * p + q * d) := by rw [neg_mul]; abel
    rw [this, e1, neg_zero]

omit [TrivialStar K] in
/-- The solutions of the kernel system are closed under addition of the two operands. -/
theorem pairKer_add {k : ℕ} {p q c d c' d' : Tower K k} (h : PairKer p q c d)
    (h' : PairKer p q c' d') : PairKer p q (c + c') (d + d') := by
  refine ⟨?_, ?_⟩
  · have : p * (c + c') + (d + d') * q = (p * c + d * q) + (p * c' + d' * q) := by
      rw [mul_add, add_mul]; abel
    rw [this, h.1, h'.1, add_zero]
  · have : (d + d') * p - q * (c + c') = (d * p - q * c) + (d' * p - q * c') := by
      rw [mul_add, add_mul]; abel
    rw [this, h.2, h'.2, add_zero]

/-- The dot identities of the real coordinate of the kernel system, for pure entries. -/
theorem pairKer_dots {k : ℕ} {p q c d : Tower K k} (hp : star p = -p) (hq : star q = -q)
    (hc : star c = -c) (h : PairKer p q c d) :
    dot k p c + dot k d q = 0 ∧ dot k d p = dot k q c := by
  have h1 := congrArg (re k) h.1
  rw [re_add, re_mul_of_star_eq_neg p hc, re_mul_of_star_eq_neg d hq, re_zero_eq] at h1
  have h2 := congrArg (re k) (sub_eq_zero.1 h.2)
  rw [re_mul_of_star_eq_neg d hp, re_mul_of_star_eq_neg q hc] at h2
  exact ⟨by linear_combination -h1, neg_inj.1 h2⟩

/-- The norms of the two sides of the kernel system, at level 3. -/
theorem pairKer_norm {p q c d : Tower K 3} (h : PairKer p q c d) :
    dot 3 p p * dot 3 c c = dot 3 d d * dot 3 q q ∧
      dot 3 d d * dot 3 p p = dot 3 q q * dot 3 c c := by
  have e1 : p * c = -(d * q) := eq_neg_of_add_eq_zero_left h.1
  have e2 : d * p = q * c := sub_eq_zero.1 h.2
  constructor
  · have h3 : dot 3 (p * c) (p * c) = dot 3 (d * q) (d * q) := by
      rw [e1, dot_neg_left, dot_neg_right, neg_neg]
    rwa [dot_mul_self_of_le_three le_rfl, dot_mul_self_of_le_three le_rfl] at h3
  · have h3 : dot 3 (d * p) (d * p) = dot 3 (q * c) (q * c) := by rw [e2]
    rwa [dot_mul_self_of_le_three le_rfl, dot_mul_self_of_le_three le_rfl] at h3

/-- If the first operand is nonzero, `c` and `d` have equal norms. -/
theorem pairKer_dot_eq_of_ne {p q c d : Tower K 3} (h : PairKer p q c d)
    (hne : dot 3 p p + dot 3 q q ≠ 0) : dot 3 c c = dot 3 d d := by
  obtain ⟨A, B⟩ := pairKer_norm h
  have h0 : (dot 3 p p + dot 3 q q) * (dot 3 c c - dot 3 d d) = 0 := by linear_combination A - B
  exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left hne)

/-- The polarized norm law of the octonions: `<x y, x w> = <x, x> <y, w>`, with the factor 2
cancelled. -/
theorem dot_mul_polar_right (h2 : (2 : K) ≠ 0) (x y w : Tower K 3) :
    dot 3 (x * y) (x * w) = dot 3 x x * dot 3 y w := by
  have h := dot_mul_self_of_le_three (R := K) (k := 3) le_rfl x (y + w)
  have h1 := dot_mul_self_of_le_three (R := K) (k := 3) le_rfl x y
  have h3 := dot_mul_self_of_le_three (R := K) (k := 3) le_rfl x w
  rw [mul_add] at h
  simp only [dot_add_left, dot_add_right] at h
  have c1 := dot_comm 3 (x * w) (x * y)
  have c2 := dot_comm 3 w y
  refine mul_left_cancel₀ h2 ?_
  linear_combination h - h1 - h3 - c1 + dot 3 x x * c2

/-- The polarized norm law in both factors: `<x y, z w> + <z y, x w> = 2 <x, z> <y, w>`. -/
theorem dot_mul_polar (h2 : (2 : K) ≠ 0) (x z y w : Tower K 3) :
    dot 3 (x * y) (z * w) + dot 3 (z * y) (x * w) = 2 * dot 3 x z * dot 3 y w := by
  have h := dot_mul_polar_right h2 (x + z) y w
  have p1 := dot_mul_polar_right h2 x y w
  have p2 := dot_mul_polar_right h2 z y w
  simp only [add_mul, dot_add_left, dot_add_right] at h
  have c := dot_comm 3 z x
  linear_combination h - p1 - p2 + dot 3 y w * c

/-- If the first operand is nonzero, a rotation of the second operand gives `dot c d = 0`. -/
theorem pairKer_dot_eq_zero (h2 : (2 : K) ≠ 0) {p q c d : Tower K 3} (hp : star p = -p)
    (hq : star q = -q) (hc : star c = -c) (hd : star d = -d) (h : PairKer p q c d)
    (hne : dot 3 p p + dot 3 q q ≠ 0) : dot 3 c d = 0 := by
  have hs := pairKer_add h (pairKer_rot hp hq hc hd h)
  have e := pairKer_dot_eq_of_ne hs hne
  simp only [dot_add_left, dot_add_right, dot_neg_left, dot_neg_right] at e
  have hcd := dot_comm 3 d c
  have h4 : 2 * (2 * dot 3 c d) = 0 := by linear_combination e - 2 * hcd
  exact (mul_eq_zero.1 ((mul_eq_zero.1 h4).resolve_left h2)).resolve_left h2

/-- With `dot p q = 0` and `|p| = |q|`, the squares of `dot p d` and `dot p c` agree. -/
theorem pairKer_sq (h2 : (2 : K) ≠ 0) {p q c d : Tower K 3} (hp : star p = -p)
    (hq : star q = -q) (hc : star c = -c) (h : PairKer p q c d) (hpq : dot 3 p q = 0)
    (hPQ : dot 3 p p = dot 3 q q) : dot 3 p d * dot 3 p d = dot 3 p c * dot 3 p c := by
  obtain ⟨hi, hii⟩ := pairKer_dots hp hq hc h
  have e1 : p * c = -(d * q) := eq_neg_of_add_eq_zero_left h.1
  have e2 : d * p = q * c := sub_eq_zero.1 h.2
  have hqp : q * p = -(p * q) := mul_comm_neg_of_dot_eq_zero hp hq hpq
  have A := dot_mul_polar h2 p d q c
  have B := dot_mul_polar h2 q d p c
  rw [e1, dot_neg_right, dot_mul_self_of_le_three le_rfl] at A
  rw [hqp, dot_neg_left, ← e2, dot_mul_self_of_le_three le_rfl] at B
  have hc1 := dot_comm 3 p d
  have hs1 : dot 3 q c = dot 3 p d := hii.symm.trans hc1.symm
  have ht1 : dot 3 q d = -dot 3 p c := by rw [dot_comm 3 q d]; linear_combination hi
  rw [hs1] at A
  rw [ht1] at B
  refine mul_left_cancel₀ h2 ?_
  linear_combination dot 3 d d * hPQ - A - B

omit [TrivialStar K] in
/-- The rotation `(p, q) -> (p + q, q - p)` preserves the kernel system. -/
theorem pairKer_rot_left {k : ℕ} {p q c d : Tower K k} (hp : star p = -p) (hq : star q = -q)
    (hc : star c = -c) (hd : star d = -d) (h : PairKer p q c d) :
    PairKer (p + q) (q + -p) c d := by
  have h1 := pairKer_swap hp hq hc hd h
  have h3 := pairKer_add h1 (pairKer_rot hc hd hp hq h1)
  refine pairKer_swap hc hd ?_ ?_ h3
  · rw [star_add, hp, hq, neg_add]
  · rw [star_add, star_neg, hq, hp]; abel

/-- The identities of the kernel system of a pair of nonzero pure octonion pairs. -/
theorem pairKer_identities (h2 : (2 : K) ≠ 0) {p q c d : Tower K 3} (hp : star p = -p)
    (hq : star q = -q) (hc : star c = -c) (hd : star d = -d) (h : PairKer p q c d)
    (hna : dot 3 p p + dot 3 q q ≠ 0) (hnb : dot 3 c c + dot 3 d d ≠ 0) :
    dot 3 c c = dot 3 d d ∧ dot 3 p p = dot 3 q q ∧ dot 3 c d = 0 ∧ dot 3 p q = 0 ∧
      dot 3 p c = 0 ∧ dot 3 q d = 0 ∧ dot 3 p d = 0 ∧ dot 3 q c = 0 := by
  have hs := pairKer_swap hp hq hc hd h
  have hCD := pairKer_dot_eq_of_ne h hna
  have hPQ := pairKer_dot_eq_of_ne hs hnb
  have hcd := pairKer_dot_eq_zero h2 hp hq hc hd h hna
  have hpq := pairKer_dot_eq_zero h2 hc hd hp hq hs hnb
  have hsq1 := pairKer_sq h2 hp hq hc h hpq hPQ
  obtain ⟨hi, hii⟩ := pairKer_dots hp hq hc h
  have hp' : star (p + q) = -(p + q) := by rw [star_add, hp, hq, neg_add]
  have hq' : star (q + -p) = -(q + -p) := by rw [star_add, star_neg, hq, hp]; abel
  have h' := pairKer_rot_left hp hq hc hd h
  have hs' := pairKer_swap hp' hq' hc hd h'
  have hPQ' := pairKer_dot_eq_of_ne hs' hnb
  have hpq' := pairKer_dot_eq_zero h2 hc hd hp' hq' hs' hnb
  have hsq2 := pairKer_sq h2 hp' hq' hc h' hpq' hPQ'
  have hc1 := dot_comm 3 p d
  have hs1 : dot 3 q c = dot 3 p d := hii.symm.trans hc1.symm
  have ht1 : dot 3 q d = -dot 3 p c := by rw [dot_comm 3 q d]; linear_combination hi
  rw [dot_add_left, dot_add_left, hs1, ht1] at hsq2
  have h4 : 2 * (2 * (dot 3 p d * dot 3 p c)) = 0 := by linear_combination -hsq2
  have hst : dot 3 p d * dot 3 p c = 0 :=
    (mul_eq_zero.1 ((mul_eq_zero.1 h4).resolve_left h2)).resolve_left h2
  have hs0 : dot 3 p d = 0 ∧ dot 3 p c = 0 := by
    rcases mul_eq_zero.1 hst with h0 | h0
    · refine ⟨h0, ?_⟩
      rw [h0, mul_zero] at hsq1
      exact mul_self_eq_zero.1 hsq1.symm
    · refine ⟨?_, h0⟩
      rw [h0, mul_zero] at hsq1
      exact mul_self_eq_zero.1 hsq1
  refine ⟨hCD, hPQ, hcd, hpq, hs0.2, ?_, hs0.1, ?_⟩
  · rw [ht1, hs0.2, neg_zero]
  · rw [hs1, hs0.1]

end Kernel

section TwoNonzero

variable {K : Type u} [Field K] [PartialOrder K] [IsOrderedAddMonoid K]

/-- In an ordered field, `2` is nonzero. -/
theorem two_ne_zero_of_sq_nonneg (hsq : ∀ x : K, 0 ≤ x * x) : (2 : K) ≠ 0 := by
  intro h
  have h1 : (0 : K) ≤ 1 := by simpa using hsq 1
  have h3 : (1 : K) + 1 = 0 := by rw [one_add_one_eq_two]; exact h
  have h4 : (1 : K) ≤ 0 := by
    calc (1 : K) = 1 + 0 := (add_zero 1).symm
      _ ≤ 1 + 1 := add_le_add le_rfl h1
      _ = 0 := h3
  exact one_ne_zero (le_antisymm h4 h1)

end TwoNonzero

section Pairs

variable {K : Type u} [Field K] [StarRing K] [TrivialStar K] [PartialOrder K]
  [IsOrderedAddMonoid K]

/-- The real part of the complex bilinear form of `x + i u` and `y + i v`. -/
def cRe (x u y v : Tower K 3) : K := dot 3 x y - dot 3 u v

/-- The imaginary part of the complex bilinear form of `x + i u` and `y + i v`. -/
def cIm (x u y v : Tower K 3) : K := dot 3 x v + dot 3 u y

/-- **Identities of a sedenion pair with zero product.** For nonzero sedenions `a = (p, q)` and
`b = (c, d)` with `a b = 0` over an ordered field, the coordinates `a_0`, `a_8`, `b_0`, `b_8`
vanish, `U - V` and `W` vanish in both parts, and `Im U` and `Im V` vanish, where
`U = z_a . z_a`, `V = z_q . z_q`, `W = z_a . z_q` for `z_a = p + i c` and `z_q = q + i d`. -/
theorem sedenion_pair_identities (hsq : ∀ x : K, 0 ≤ x * x) {p q c d : Tower K 3}
    (ha : (mk p q : Tower K (3 + 1)) ≠ 0) (hb : (mk c d : Tower K (3 + 1)) ≠ 0)
    (h : mk p q * mk c d = 0) :
    (re 3 p = 0 ∧ re 3 q = 0 ∧ re 3 c = 0 ∧ re 3 d = 0) ∧
      cRe p c p c = cRe q d q d ∧ cIm p c p c = cIm q d q d ∧ cRe p c q d = 0 ∧
      cIm p c q d = 0 ∧ cIm p c p c = 0 ∧ cIm q d q d = 0 := by
  obtain ⟨ha0, ha8⟩ := dot_one_eq_zero_and_dot_mk_zero_one_of_mul_eq_zero hsq h hb
  obtain ⟨hb0, hb8⟩ := dot_one_eq_zero_and_dot_mk_zero_one_of_mul_eq_zero_right hsq ha h
  rw [dot_one_right, re_mk] at ha0 hb0
  rw [dot_mk, dot_zero_right, dot_one_right, zero_add] at ha8 hb8
  have hp := star_eq_neg_of_re_eq_zero ha0
  have hq := star_eq_neg_of_re_eq_zero ha8
  have hc := star_eq_neg_of_re_eq_zero hb0
  have hd := star_eq_neg_of_re_eq_zero hb8
  have hna : dot 3 p p + dot 3 q q ≠ 0 := by
    have := dot_self_ne_zero hsq ha
    rwa [dot_mk] at this
  have hnb : dot 3 c c + dot 3 d d ≠ 0 := by
    have := dot_self_ne_zero hsq hb
    rwa [dot_mk] at this
  obtain ⟨hCD, hPQ, hcd, hpq, hpc, hqd, hpd, hqc⟩ :=
    pairKer_identities (two_ne_zero_of_sq_nonneg hsq) hp hq hc hd
      ((mk_mul_mk_eq_zero_iff_pairKer hc hd).1 h) hna hnb
  have u0 : dot 3 p c + dot 3 c p = 0 := by
    rw [dot_comm 3 c p]; linear_combination 2 * hpc
  have v0 : dot 3 q d + dot 3 d q = 0 := by
    rw [dot_comm 3 d q]; linear_combination 2 * hqd
  have w0 : dot 3 p d + dot 3 c q = 0 := by
    rw [dot_comm 3 c q]; linear_combination hpd + hqc
  refine ⟨⟨ha0, ha8, hb0, hb8⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold cRe; linear_combination hPQ - hCD
  · unfold cIm; linear_combination u0 - v0
  · unfold cRe; linear_combination hpq - hcd
  · unfold cIm; exact w0
  · unfold cIm; exact u0
  · unfold cIm; exact v0

/-- Over an ordered field, a pair of nonzero sedenions with zero product has `|a| = |b|` exactly
when `Re U = |p_a|^2 - |p_b|^2` vanishes. -/
theorem dot_eq_iff_cRe_eq_zero (hsq : ∀ x : K, 0 ≤ x * x) {p q c d : Tower K 3}
    (ha : (mk p q : Tower K (3 + 1)) ≠ 0) (hb : (mk c d : Tower K (3 + 1)) ≠ 0)
    (h : mk p q * mk c d = 0) :
    dot (3 + 1) (mk p q) (mk p q) = dot (3 + 1) (mk c d) (mk c d) ↔ cRe p c p c = 0 := by
  obtain ⟨-, hU, -⟩ := sedenion_pair_identities hsq ha hb h
  have h2 := two_ne_zero_of_sq_nonneg hsq
  rw [dot_mk, dot_mk]
  unfold cRe at hU ⊢
  constructor
  · intro e
    refine mul_left_cancel₀ h2 ?_
    linear_combination e + hU
  · intro e
    linear_combination 2 * e - hU

end Pairs

end Tower

end CayleyDickson
