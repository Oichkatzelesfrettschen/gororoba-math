/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AnnihilatorSymmetry

/-!
# The conjugate identities of the trace form

Convention: the product of `Tower R k` is the Cayley-Dickson product of
`GororobaMath.CayleyDickson.Tower`, `(a, b) (c, d) = (a c - star d b, d a + b star c)`,
with `star (a, b) = (star a, -b)`, over a commutative ring whose star is the
identity. `Tower.dot k` is the trace form and `Tower.re k` the coordinate of
`1` of `GororobaMath.CayleyDickson.AnnihilatorSymmetry`; an element `a` is
pure when `star a = -a`.

Every element satisfies `star x = (2 * re k x) • 1 - x` (`Tower.star_add_self`),
and scalars pass through the product on both sides. So `x * (star x * y)` and
`star x * (x * y)` both equal `(2 * re k x) • (x * y) - x * (x * y)`, and the
mirror identity holds the same way; no step uses associativity, alternativity or an
order. Over an ordered domain the trace form is definite, and with the adjoint
identities this makes `x * y = 0`, `star x * y = 0` and `x * star y = 0`
equivalent.

## Main results

* `Tower.mul_star_mul_left`: `x * (star x * y) = star x * (x * y)`, the Rocq
  `conj_mul_left` of the functor `CdTower` in `rocq/quantum/CdTowerDomain.v`.
* `Tower.mul_mul_star_right`: `x * y * star y = x * star y * y`, the Rocq
  `conj_mul_right` of the same functor.
* `Tower.mul_eq_zero_iff_star_mul_eq_zero`: Lemma 9.2 of Biss, Dugger and
  Isaksen (arXiv:math/0511691), the Rocq `lemma_9_2` of the same functor.
* `Tower.dot_mul_left_of_star_eq_neg`: left multiplication by a pure element is
  skew for the trace form, `dot (a * y) z = -dot y (a * z)` (Moreno 1997,
  Proposition 1.7), the Rocq `l_x_skew_symm` of
  `rocq/open/theories/C1539_MorSkewSymm.v`, stated there over the interface
  `CDAlgMoreno` with real coefficients and here over the tower at every level;
  `Tower.dot_mul_right_of_star_eq_neg` is its mirror, `r_x_skew_symm`.

* `Tower.re_mul_comm`, `Tower.re_mul_assoc`: Lemmas 2.6 and 2.8 of Biss, Dugger and Isaksen,
  `re (x * y) = re (y * x)` and `re ((x * y) * z) = re (x * (y * z))`.
* `Tower.mul_mul_self_eq`: the flexible law `(x * y) * x = x * (y * x)`, from the
  symmetrized associator `Tower.flexSum`, over a ring in which `2` is left regular.
* `Tower.mul_dot_smul_sub_star_eq_zero`, `Tower.exists_eq_inv_dot_smul_star_add`: the right
  inverses of `a` lie in `(dot a a)⁻¹ • star a` plus the kernel of left multiplication by `a`.
* `Tower.dot_star_mul_self`, `Tower.dot_mul_self_comm`, `Tower.dot_add_self_add_dot_sub_self`:
  `|star x * y|^2 = |x * y|^2 = |y * x|^2` and the parallelogram law, for `|z|^2 = dot z z`.
* `Tower.re_eq_zero_of_mul_eq_zero_rev`, `Tower.dot_eq_zero_of_mul_eq_zero`,
  `Tower.mul_eq_zero_iff_forall_dot_mul_eq_zero`,
  `Tower.dot_one_eq_zero_and_dot_mk_zero_one_of_mul_eq_zero`: purity and orthogonality of
  zero divisors, with the kernel swap `Tower.swap_mul_eq_zero` of Lemma 9.5.

The Rocq functor `CdTower` takes an ordered domain; the first two identities
hold here over every commutative ring with the identity as star, and Lemma 9.2
under the ordered hypotheses of `GororobaMath.CayleyDickson.AnnihilatorSymmetry`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

/-- Conjugation is `x ↦ (2 * re k x) • 1 - x`. -/
theorem star_eq_smul_one_sub {k : ℕ} (x : Tower R k) :
    star x = (2 * re k x) • (1 : Tower R k) - x :=
  eq_sub_of_add_eq (star_add_self k x)

/-- The identity of Lemma 9.2 of Biss, Dugger and Isaksen,
`x * (star x * y) = star x * (x * y)`. The Rocq original is `conj_mul_left` of
the functor `CdTower` in `rocq/quantum/CdTowerDomain.v`. -/
theorem mul_star_mul_left {k : ℕ} (x y : Tower R k) :
    x * (star x * y) = star x * (x * y) := by
  rw [star_eq_smul_one_sub, sub_mul, sub_mul, smul_mul_assoc', smul_mul_assoc', one_mul, one_mul,
    mul_sub, mul_smul_comm']

/-- The mirror identity `x * y * star y = x * star y * y`. The Rocq original is
`conj_mul_right` of the functor `CdTower` in `rocq/quantum/CdTowerDomain.v`. -/
theorem mul_mul_star_right {k : ℕ} (x y : Tower R k) :
    x * y * star y = x * star y * y := by
  rw [star_eq_smul_one_sub, mul_sub, mul_sub, mul_smul_comm', mul_smul_comm', mul_one, mul_one,
    sub_mul, smul_mul_assoc']

/-- Left multiplication by a pure element is skew for the trace form (Moreno 1997,
Proposition 1.7). The Rocq original is `l_x_skew_symm` of
`rocq/open/theories/C1539_MorSkewSymm.v`. -/
theorem dot_mul_left_of_star_eq_neg {k : ℕ} {a : Tower R k} (ha : star a = -a)
    (y z : Tower R k) : dot k (a * y) z = -dot k y (a * z) := by
  rw [(dot_mul_adjoint k a y z).1, ha, neg_mul, dot_neg_right]

/-- Right multiplication by a pure element is skew for the trace form. The Rocq
original is `r_x_skew_symm` of `rocq/open/theories/C1539_MorSkewSymm.v`. -/
theorem dot_mul_right_of_star_eq_neg {k : ℕ} {a : Tower R k} (ha : star a = -a)
    (y z : Tower R k) : dot k (y * a) z = -dot k y (z * a) := by
  rw [(dot_mul_adjoint k y a z).2, ha, mul_neg, dot_neg_right]

omit [TrivialStar R] in
/-- The coordinate of `1` is additive. -/
theorem re_add (k : ℕ) (x y : Tower R k) : re k (x + y) = re k x + re k y := by
  rw [← dot_one_right, ← dot_one_right, ← dot_one_right, dot_add_left]

omit [TrivialStar R] in
/-- The coordinate of `1` respects subtraction. -/
theorem re_sub (k : ℕ) (x y : Tower R k) : re k (x - y) = re k x - re k y := by
  rw [← dot_one_right, ← dot_one_right, ← dot_one_right, dot_sub_left]

/-- `re (x * y) = re (y * x)` at every level (Lemma 2.6 of Biss, Dugger and Isaksen). The Rocq
original is `re_commutator` of the functor `CdTower` in `rocq/quantum/CdTowerDomain.v`, stated
there over an ordered domain; the proof uses the adjoint identities alone. -/
theorem re_mul_comm {k : ℕ} (x y : Tower R k) : re k (x * y) = re k (y * x) := by
  rw [← dot_one_right, ← dot_one_right, (dot_mul_adjoint k x y 1).2,
    (dot_mul_adjoint k y x 1).1, one_mul, mul_one]

/-- `re ((x * y) * z) = re (x * (y * z))` at every level (Lemma 2.8 of Biss, Dugger and Isaksen).
The Rocq original is `re_associator` of the functor `CdTower` in
`rocq/quantum/CdTowerDomain.v`. -/
theorem re_mul_assoc {k : ℕ} (x y z : Tower R k) : re k (x * y * z) = re k (x * (y * z)) := by
  rw [← dot_one_right, ← dot_one_right, (dot_mul_adjoint k (x * y) z 1).2,
    (dot_mul_adjoint k x y (1 * star z)).1, (dot_mul_adjoint k x (y * z) 1).1,
    (dot_mul_adjoint k y z (star x * 1)).2, one_mul, mul_one]

/-- Every right inverse `b` of `a` satisfies `a * (dot a a • b - star a) = 0`. The Rocq original
is `right_inverse_affine` of the functor `CdTower` in `rocq/quantum/CdTowerDomain.v`, stated
there over an ordered domain; the identity needs no order. -/
theorem mul_dot_smul_sub_star_eq_zero {k : ℕ} {a b : Tower R k} (h : a * b = 1) :
    a * (dot k a a • b - star a) = 0 := by
  rw [mul_sub, mul_smul_comm', h, (mul_star_eq_dot k a).1, sub_self]

/-- Conjugation preserves the trace form. -/
theorem dot_star_star : ∀ (k : ℕ) (x y : Tower R k), dot k (star x) (star y) = dot k x y
  | 0, x, y => by
    change star (base x) * star (base y) = base x * base y
    rw [star_trivial, star_trivial]
  | k + 1, ⟨a, b⟩, ⟨c, d⟩ => by
    change dot k (star a) (star c) + dot k (-b) (-d) = dot k a c + dot k b d
    rw [dot_star_star k a c, dot_neg_left, dot_neg_right, neg_neg]

/-- `|conj(x) y|^2 = |x y|^2`, where `|z|^2 = dot z z` (Brown 1972, Theorem 3.9(ii)). The Rocq
original is `brown1972_theorem_3_9_ii` of `rocq/open/theories/Brown1972ChapterIII.v`; the Rocq
interface assumes a multiplicative norm, which fails from level 4, and this statement holds at
every level: both sides equal `dot y (x * (star x * y))` by the adjoint identity and
`mul_star_mul_left`. -/
theorem dot_star_mul_self {k : ℕ} (x y : Tower R k) :
    dot k (star x * y) (star x * y) = dot k (x * y) (x * y) := by
  rw [(dot_mul_adjoint k (star x) y _).1, star_star, (dot_mul_adjoint k x y _).1,
    mul_star_mul_left]

/-- `|x y|^2 = |y x|^2` (Brown 1972, Theorem 3.9(iii)). The Rocq original is
`brown1972_theorem_3_9_iii` of `rocq/open/theories/Brown1972ChapterIII.v`; this statement needs
no multiplicative norm: `|y x| = |conj(x) conj(y)| = |x conj(y)| = |x y|`. -/
theorem dot_mul_self_comm {k : ℕ} (x y : Tower R k) :
    dot k (x * y) (x * y) = dot k (y * x) (y * x) := by
  have h1 : dot k (y * x) (y * x) = dot k (star x * star y) (star x * star y) := by
    rw [← dot_star_star k (y * x) (y * x), star_mul]
  have h2 : dot k (x * star y) (x * star y) = dot k (x * y) (x * y) := by
    rw [(dot_mul_adjoint k x (star y) _).2, (dot_mul_adjoint k x y _).2, star_star,
      mul_mul_star_right]
  rw [h1, dot_star_mul_self x (star y), h2]

omit [TrivialStar R] in
/-- Cancellation of `2` in the tower: `x + x = 0` forces `x = 0` when `2` is left regular in
`R`. -/
theorem eq_zero_of_add_self_eq_zero (h2 : IsLeftRegular (2 : R)) :
    ∀ {k : ℕ} {x : Tower R k}, x + x = 0 → x = 0
  | 0, x, h => by
    have h' : (2 : R) * base x = 2 * 0 := by
      rw [mul_zero, two_mul]
      exact h
    have hx : base x = 0 := h2 h'
    exact hx
  | k + 1, ⟨a, b⟩, h => by
    have h' : mk (a + a) (b + b) = mk 0 0 := h
    rw [mk_inj] at h'
    change mk a b = mk 0 0
    rw [eq_zero_of_add_self_eq_zero h2 h'.1, eq_zero_of_add_self_eq_zero h2 h'.2]

/-- The symmetrized associator `x (y z) - (x y) z + z (y x) - (z y) x`, the `flex_sum` of
`rocq/quantum/CdTowerDomain.v`. -/
def flexSum {k : ℕ} (x y z : Tower R k) : Tower R k :=
  x * (y * z) - x * y * z + z * (y * x) - z * y * x

/-- Conjugating the first argument negates the symmetrized associator. -/
theorem flexSum_star_left {k : ℕ} (x y z : Tower R k) :
    flexSum (star x) y z = -flexSum x y z := by
  unfold flexSum
  rw [star_eq_smul_one_sub x]
  simp only [mul_sub, sub_mul, smul_mul_assoc', mul_smul_comm', one_mul, mul_one]
  module

/-- Conjugating the middle argument negates the symmetrized associator. -/
theorem flexSum_star_mid {k : ℕ} (x y z : Tower R k) :
    flexSum x (star y) z = -flexSum x y z := by
  unfold flexSum
  rw [star_eq_smul_one_sub y]
  simp only [mul_sub, sub_mul, smul_mul_assoc', mul_smul_comm', one_mul, mul_one]
  module

/-- Conjugating the last argument negates the symmetrized associator. -/
theorem flexSum_star_right {k : ℕ} (x y z : Tower R k) :
    flexSum x y (star z) = -flexSum x y z := by
  unfold flexSum
  rw [star_eq_smul_one_sub z]
  simp only [mul_sub, sub_mul, smul_mul_assoc', mul_smul_comm', one_mul, mul_one]
  module

omit [TrivialStar R] in
/-- Conjugation reverses products, so it carries the symmetrized associator to the negative of
the one of the conjugates. -/
theorem star_flexSum {k : ℕ} (x y z : Tower R k) :
    star (flexSum x y z) = -flexSum (star x) (star y) (star z) := by
  unfold flexSum
  simp only [star_sub, star_add, star_mul]
  abel

/-- The symmetrized associator has coordinate `0` of `1`, by `re_mul_assoc`. -/
theorem re_flexSum {k : ℕ} (x y z : Tower R k) : re k (flexSum x y z) = 0 := by
  unfold flexSum
  simp only [re_add, re_sub, re_mul_assoc x y z, re_mul_assoc z y x]
  ring

/-- The symmetrized associator vanishes: it is its own conjugate with coordinate `0` of `1`, so
twice it is `0`. -/
theorem flexSum_eq_zero (h2 : IsLeftRegular (2 : R)) {k : ℕ} (x y z : Tower R k) :
    flexSum x y z = 0 := by
  have hs := star_add_self k (flexSum x y z)
  rw [re_flexSum, mul_zero, zero_smul] at hs
  have hstar : star (flexSum x y z) = flexSum x y z := by
    rw [star_flexSum, flexSum_star_left, flexSum_star_mid, flexSum_star_right]
    simp only [neg_neg]
  rw [hstar] at hs
  exact eq_zero_of_add_self_eq_zero h2 hs

/-- The flexible law `(x * y) * x = x * (y * x)` at every level (Corollary 2.9 of Biss, Dugger and
Isaksen), over a commutative ring with the identity as star in which `2` is left regular
(`IsLeftRegular (2 : R)`, as in an ordered domain). The Rocq original is `flexible` of the
functor `CdTower` in `rocq/quantum/CdTowerDomain.v`. -/
theorem mul_mul_self_eq (h2 : IsLeftRegular (2 : R)) {k : ℕ} (x y : Tower R k) :
    x * y * x = x * (y * x) := by
  have h := flexSum_eq_zero h2 x y x
  unfold flexSum at h
  have hD : (x * (y * x) - x * y * x) + (x * (y * x) - x * y * x) = 0 := by
    rw [← h]
    abel
  exact (sub_eq_zero.1 (eq_zero_of_add_self_eq_zero h2 hD)).symm

omit [TrivialStar R] in
/-- The parallelogram law `|x + y|^2 + |x - y|^2 = 2 (|x|^2 + |y|^2)` for `|z|^2 = dot z z`
(Brown 1972, Lemma 3.10). The Rocq original is `brown1972_lemma_3_10` of
`rocq/open/theories/Brown1972ChapterIII.v`. -/
theorem dot_add_self_add_dot_sub_self {k : ℕ} (x y : Tower R k) :
    dot k (x + y) (x + y) + dot k (x - y) (x - y) = 2 * (dot k x x + dot k y y) := by
  simp only [dot_add_left, dot_add_right, dot_sub_left, dot_sub_right]
  ring

section Ordered

variable [PartialOrder R] [IsOrderedAddMonoid R] [NoZeroDivisors R]

theorem star_mul_eq_zero_of_mul_eq_zero (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ} {x y : Tower R k}
    (h : x * y = 0) : star x * y = 0 := by
  apply eq_zero_of_dot_self_eq_zero hsq
  rw [(dot_mul_adjoint k (star x) y _).1, star_star, mul_star_mul_left, h, mul_zero,
    dot_zero_right]

theorem mul_star_eq_zero_of_mul_eq_zero (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ} {x y : Tower R k}
    (h : x * y = 0) : x * star y = 0 := by
  apply eq_zero_of_dot_self_eq_zero hsq
  rw [(dot_mul_adjoint k x (star y) _).2, star_star, ← mul_mul_star_right, h, zero_mul,
    dot_zero_right]

/-- Lemma 9.2 of Biss, Dugger and Isaksen: `x * y = 0`, `star x * y = 0` and
`x * star y = 0` are equivalent, at every level, over a commutative ring with the
identity as star, no zero divisors, a partial order compatible with addition and
nonnegative squares. The Rocq original is `lemma_9_2` of the functor `CdTower` in
`rocq/quantum/CdTowerDomain.v`. -/
theorem mul_eq_zero_iff_star_mul_eq_zero (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ} (x y : Tower R k) :
    (x * y = 0 ↔ star x * y = 0) ∧ (x * y = 0 ↔ x * star y = 0) := by
  refine ⟨⟨star_mul_eq_zero_of_mul_eq_zero hsq, fun h => ?_⟩,
    ⟨mul_star_eq_zero_of_mul_eq_zero hsq, fun h => ?_⟩⟩
  · simpa only [star_star] using star_mul_eq_zero_of_mul_eq_zero hsq h
  · simpa only [star_star] using mul_star_eq_zero_of_mul_eq_zero hsq h

/-- Both factors of `z * a = 0` are pure when nonzero (Lemma 9.4 of Biss, Dugger and Isaksen,
on the other side). The Rocq original is `purity_right` of the functor `CdTower` in
`rocq/quantum/CdTowerDomain.v`. -/
theorem re_eq_zero_of_mul_eq_zero_rev (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ} {a z : Tower R k}
    (h : z * a = 0) (ha : a ≠ 0) (hz : z ≠ 0) : re k a = 0 ∧ re k z = 0 :=
  re_eq_zero_of_mul_eq_zero hsq (mul_eq_zero_rev hsq h) ha hz

/-- If `a * z = 0` then `a` and `z` are orthogonal for the trace form. The Rocq original is
`tower_zero_divisor_orthogonal` of `rocq/open/theories/CDTowerZeroDivisors.v`. -/
theorem dot_eq_zero_of_mul_eq_zero (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ} {a z : Tower R k}
    (h : a * z = 0) : dot k a z = 0 := by
  by_cases ha : a = 0
  · rw [ha, dot_zero_left]
  by_cases hz : z = 0
  · rw [hz, dot_zero_right]
  have hrz := (re_eq_zero_of_mul_eq_zero hsq h ha hz).2
  have h1 := (dot_mul_adjoint k a z 1).2
  rw [h, dot_zero_left, one_mul, star_eq_neg_of_re_eq_zero hrz, dot_neg_right] at h1
  exact neg_eq_zero.1 h1.symm

/-- For pure `a`, `a * y = 0` exactly when `y` is orthogonal to the image of left
multiplication by `a`. The Rocq original is `ker_lx_iff_perp_im_lx` of
`rocq/open/theories/C1539_MorSkewSymm.v`, which needs non-degeneracy of the inner product as a
hypothesis; here it comes from the ordered hypotheses. -/
theorem mul_eq_zero_iff_forall_dot_mul_eq_zero (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ}
    {a : Tower R k} (ha : star a = -a) (y : Tower R k) :
    a * y = 0 ↔ ∀ z, dot k y (a * z) = 0 := by
  constructor
  · intro h z
    have := dot_mul_left_of_star_eq_neg ha y z
    rw [h, dot_zero_left] at this
    exact neg_eq_zero.1 this.symm
  · intro h
    apply eq_zero_of_dot_self_eq_zero hsq
    rw [dot_mul_left_of_star_eq_neg ha y (a * y), h]
    simp

omit [TrivialStar R] [PartialOrder R] [IsOrderedAddMonoid R] [NoZeroDivisors R] in
/-- The kernel swap of Lemma 9.5 of Biss, Dugger and Isaksen: `(a, b) * (c, d) = 0` with `a`
pure gives `(-star d, c) * (b, a) = 0`. -/
theorem swap_mul_eq_zero {k : ℕ} {a b c d : Tower R k} (h : mk a b * mk c d = 0)
    (ha : star a = -a) : mk (-star d) c * mk b a = 0 := by
  have h' : mk (a * c - star d * b) (d * a + b * star c) = mk 0 0 := by
    rw [← mk_mul_mk]
    exact h.trans (zero_eq_mk k)
  obtain ⟨H1, H2⟩ := mk_inj.1 h'
  have H3 := congrArg star H2
  rw [star_add, star_mul, star_mul, star_star, star_zero, ha] at H3
  rw [mk_mul_mk, zero_eq_mk, mk_inj]
  constructor
  · rw [ha, neg_mul, neg_mul, sub_neg_eq_add, add_comm, ← sub_eq_add_neg]
    exact H1
  · rw [mul_neg, ← neg_mul]
    exact H3

/-- A left zero divisor of level `k + 1` is orthogonal to `1` and to the adjoined unit
`(0, 1)` (Lemma 9.5 of Biss, Dugger and Isaksen). The Rocq original is `lemma_9_5` of the functor
`CdTower` in `rocq/quantum/CdTowerDomain.v`. -/
theorem dot_one_eq_zero_and_dot_mk_zero_one_of_mul_eq_zero (hsq : ∀ x : R, 0 ≤ x * x) {k : ℕ}
    {x y : Tower R (k + 1)} (h : x * y = 0) (hy : y ≠ 0) :
    dot (k + 1) x 1 = 0 ∧ dot (k + 1) x (mk 0 1) = 0 := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  change mk a b * mk c d = 0 at h
  change mk c d ≠ 0 at hy
  change dot (k + 1) (mk a b) 1 = 0 ∧ dot (k + 1) (mk a b) (mk 0 1) = 0
  by_cases hx : (mk a b : Tower R (k + 1)) = 0
  · rw [hx, dot_zero_left, dot_zero_left]
    exact ⟨rfl, rfl⟩
  have hre : re k a = 0 := (re_eq_zero_of_mul_eq_zero hsq h hx hy).1
  have hs := swap_mul_eq_zero h (star_eq_neg_of_re_eq_zero hre)
  have hy' : (mk (-star d) c : Tower R (k + 1)) ≠ 0 := by
    intro h0
    obtain ⟨h1, h2⟩ := mk_inj.1 (h0.trans (zero_eq_mk k))
    apply hy
    rw [zero_eq_mk, mk_inj]
    exact ⟨h2, star_eq_zero.1 (neg_eq_zero.1 h1)⟩
  refine ⟨?_, ?_⟩
  · rw [dot_one_right]
    exact hre
  · rw [dot_mk, dot_zero_right, dot_one_right, zero_add]
    by_cases hb : (mk b a : Tower R (k + 1)) = 0
    · obtain ⟨hb0, -⟩ := mk_inj.1 (hb.trans (zero_eq_mk k))
      rw [hb0, ← dot_one_right, dot_zero_left]
    · exact (re_eq_zero_of_mul_eq_zero hsq (mul_eq_zero_rev hsq hs) hb hy').1

/-- A right zero divisor of level `k + 1` is orthogonal to `1` and to the adjoined unit. The
Rocq original is `annihilator_orthogonal` of the functor `CdTower` in
`rocq/quantum/CdTowerDomain.v`. -/
theorem dot_one_eq_zero_and_dot_mk_zero_one_of_mul_eq_zero_right (hsq : ∀ x : R, 0 ≤ x * x)
    {k : ℕ} {x y : Tower R (k + 1)} (hx : x ≠ 0) (h : x * y = 0) :
    dot (k + 1) y 1 = 0 ∧ dot (k + 1) y (mk 0 1) = 0 :=
  dot_one_eq_zero_and_dot_mk_zero_one_of_mul_eq_zero hsq (mul_eq_zero_rev hsq h) hx

end Ordered

section Field

variable {K : Type u} [Field K] [StarRing K] [TrivialStar K] [PartialOrder K] [IsOrderedAddMonoid K]

/-- Over an ordered field every right inverse `b` of `a` is `(dot a a)⁻¹ • star a` plus an element
of the kernel of left multiplication by `a`. The Rocq original is `right_inverse_form` of the
functor `CdTowerField` in `rocq/quantum/CdTowerDomain.v`. -/
theorem exists_eq_inv_dot_smul_star_add (hsq : ∀ x : K, 0 ≤ x * x) {k : ℕ} {a b : Tower K k}
    (h : a * b = 1) : ∃ w, a * w = 0 ∧ b = (dot k a a)⁻¹ • star a + w := by
  by_cases ha : a = 0
  · refine ⟨b, by rw [ha, zero_mul], ?_⟩
    rw [ha, star_zero, smul_zero, zero_add]
  · have hd := dot_self_ne_zero hsq ha
    refine ⟨b - (dot k a a)⁻¹ • star a, ?_, (add_sub_cancel _ _).symm⟩
    rw [mul_sub, mul_smul_comm', (mul_star_eq_dot k a).1, h, smul_smul, inv_mul_cancel₀ hd,
      one_smul, sub_self]

end Field

/-- The ordered hypotheses hold over the rationals, at level 5. -/
example (x y : Tower ℚ 5) (h : x * y = 0) : star x * y = 0 :=
  ((mul_eq_zero_iff_star_mul_eq_zero (fun r => mul_self_nonneg r) x y).1).1 h

end Tower

end CayleyDickson
