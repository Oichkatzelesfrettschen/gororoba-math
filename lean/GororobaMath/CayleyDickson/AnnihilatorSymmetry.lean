/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TowerModule

/-!
# Left and right annihilators coincide at every level of the tower

Convention: the product of `Tower R k` is the Cayley-Dickson product of
`GororobaMath.CayleyDickson.Tower`, `(a, b) (c, d) = (a c - star d b, d a + b star c)`,
over a commutative ring whose star is the identity. `Tower.dot k x y` is the
trace form, the sum over the `2 ^ k` coordinates of the products of
corresponding coordinates, and `Tower.re k x` is the coordinate of `1`.

Over a commutative ring with no zero divisors and a partial order under which
`star x * x ≥ 0` (`StarOrderedRing`; with the identity as star, every square is
nonnegative: `ℤ`, `ℚ`, `ℝ`), `dot k x x` is a sum of squares and vanishes only at
`x = 0`. The proof is that of Biss, Dugger and Isaksen, Large annihilators in
Cayley-Dickson algebras (arXiv:math/0511691), Lemma 9.4 and Corollary 9.3: the
norm law
`x * star x = star x * x = dot x x • 1` (`Tower.mul_star_eq_dot`), the
adjoint identities `dot (x * y) z = dot y (star x * z) = dot x (z * star y)`
(`Tower.dot_mul_adjoint`), and the products `dot (a * z) z = dot z z * re a`
and `dot (a * z) a = dot a a * re z`, which make `a` and `z` pure
(`re = 0`, so `star = -id`) when `a * z = 0` with both nonzero. Then
`z * a = (-z) * (-a) = star z * star a = star (a * z) = 0`. No step uses
associativity, alternativity or multiplicativity of the norm, and no step
divides: each cancellation is of the nonzero scalar `dot x x`.

## Main results

* `Tower.mul_eq_zero_iff_rev`: `a * z = 0 ↔ z * a = 0` at every level `k`.
* `Tower.re_eq_zero_of_mul_eq_zero`: both factors of a product that vanishes,
  when nonzero, are pure.
* `Tower.mul_eq_one_rev`: `a * b = 1 → b * a = 1` (direct finiteness).

They are the Lean form of `kernel_equality`, `purity_left` and
`direct_finiteness` of the functor `CdTower` of `rocq/quantum/CdTowerDomain.v`,
proved there over an abstract `OrderedDomain`: a commutative ring with a
relation under which squares are nonnegative, sums of nonnegative terms are
nonnegative and vanish only termwise, with no zero divisors and `1 ≠ 0`. The
hypotheses here give those facts for Mathlib's rings through
`star_mul_self_nonneg`, `add_eq_zero_iff_of_nonneg` and `mul_eq_zero`; the
Rocq signature asks for no antisymmetry of its relation, so it is the wider
of the two. `rocq/quantum/CdAnnihilatorSymmetry.v` is the integer instance.
In characteristic 2 every level is commutative and the swap holds trivially;
over a commutative ring with a square root of `-1` and `2 ≠ 0`, with the
identity as star, it fails from level 2 on (`kernel_swap_iff_two_zero` of
`rocq/quantum/CdTowerRing.v`), so some order hypothesis is needed.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

/-- An element of level 0 as an element of the base ring. -/
def base {R : Type u} (x : Tower R 0) : R := x

variable {R : Type u} [CommRing R] [StarRing R]

/-- The trace form: the sum of the products of corresponding coordinates. -/
def dot : (k : ℕ) → Tower R k → Tower R k → R
  | 0, x, y => (show R from x) * (show R from y)
  | k + 1, ⟨a, b⟩, ⟨c, d⟩ => dot k a c + dot k b d

/-- The coordinate of `1`. -/
def re : (k : ℕ) → Tower R k → R
  | 0, x => x
  | k + 1, ⟨a, _⟩ => re k a

omit [StarRing R] in
theorem dot_mk {k : ℕ} (a b c d : Tower R k) :
    dot (k + 1) (mk a b) (mk c d) = dot k a c + dot k b d := rfl

omit [CommRing R] [StarRing R] in
theorem re_mk {k : ℕ} (a b : Tower R k) : re (k + 1) (mk a b) = re k a := rfl

theorem add_mk {k : ℕ} (a b c d : Tower R k) :
    mk a b + mk c d = mk (a + c) (b + d) := rfl

omit [StarRing R] in
theorem dot_comm : ∀ (k : ℕ) (x y : Tower R k), dot k x y = dot k y x
  | 0, x, y => mul_comm (show R from x) (show R from y)
  | k + 1, ⟨a, b⟩, ⟨c, d⟩ => by
    change dot k a c + dot k b d = dot k c a + dot k d b
    rw [dot_comm k a c, dot_comm k b d]

theorem dot_add_left : ∀ (k : ℕ) (x y z : Tower R k), dot k (x + y) z = dot k x z + dot k y z
  | 0, x, y, z => add_mul (show R from x) (show R from y) (show R from z)
  | k + 1, ⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩ => by
    change dot k (a + c) e + dot k (b + d) f = (dot k a e + dot k b f) + (dot k c e + dot k d f)
    rw [dot_add_left k a c e, dot_add_left k b d f]
    ring

theorem dot_neg_left : ∀ (k : ℕ) (x y : Tower R k), dot k (-x) y = -dot k x y
  | 0, x, y => neg_mul (show R from x) (show R from y)
  | k + 1, ⟨a, b⟩, ⟨c, d⟩ => by
    change dot k (-a) c + dot k (-b) d = -(dot k a c + dot k b d)
    rw [dot_neg_left k a c, dot_neg_left k b d]
    ring

theorem dot_smul_left : ∀ (k : ℕ) (r : R) (x y : Tower R k), dot k (r • x) y = r * dot k x y
  | 0, r, x, y => mul_assoc r (show R from x) (show R from y)
  | k + 1, r, ⟨a, b⟩, ⟨c, d⟩ => by
    change dot k (r • a) c + dot k (r • b) d = r * (dot k a c + dot k b d)
    rw [dot_smul_left k r a c, dot_smul_left k r b d]
    ring

theorem dot_zero_left : ∀ (k : ℕ) (y : Tower R k), dot k 0 y = 0
  | 0, y => zero_mul (show R from y)
  | k + 1, ⟨c, d⟩ => by
    change dot k 0 c + dot k 0 d = 0
    rw [dot_zero_left k c, dot_zero_left k d, add_zero]

theorem dot_sub_left (k : ℕ) (x y z : Tower R k) : dot k (x - y) z = dot k x z - dot k y z := by
  rw [sub_eq_add_neg, dot_add_left, dot_neg_left, ← sub_eq_add_neg]

theorem dot_add_right (k : ℕ) (x y z : Tower R k) : dot k x (y + z) = dot k x y + dot k x z := by
  rw [dot_comm, dot_add_left, dot_comm k y, dot_comm k z]

theorem dot_neg_right (k : ℕ) (x y : Tower R k) : dot k x (-y) = -dot k x y := by
  rw [dot_comm, dot_neg_left, dot_comm]

theorem dot_sub_right (k : ℕ) (x y z : Tower R k) : dot k x (y - z) = dot k x y - dot k x z := by
  rw [dot_comm, dot_sub_left, dot_comm k y, dot_comm k z]

theorem dot_smul_right (k : ℕ) (r : R) (x y : Tower R k) : dot k x (r • y) = r * dot k x y := by
  rw [dot_comm, dot_smul_left, dot_comm]

theorem dot_zero_right (k : ℕ) (x : Tower R k) : dot k x 0 = 0 := by
  rw [dot_comm, dot_zero_left]

theorem dot_one_right : ∀ (k : ℕ) (x : Tower R k), dot k x 1 = re k x
  | 0, x => mul_one (show R from x)
  | k + 1, ⟨a, b⟩ => by
    change dot k a 1 + dot k b 0 = re k a
    rw [dot_one_right k a, dot_zero_right, add_zero]

section Cancel

variable [NoZeroDivisors R]

/-- A nonzero scalar cancels from `r • x = 0`. -/
theorem eq_zero_of_smul_eq_zero {r : R} (hr : r ≠ 0) : ∀ {k : ℕ} {x : Tower R k}, r • x = 0 → x = 0
  | 0, x, h => by
    have hx : (show R from x) = 0 :=
      (mul_eq_zero.1 (show r * (show R from x) = 0 from h)).resolve_left hr
    exact hx
  | k + 1, ⟨a, b⟩, h => by
    have h' : mk (r • a) (r • b) = mk 0 0 := h
    rw [mk_inj] at h'
    change mk a b = mk 0 0
    rw [eq_zero_of_smul_eq_zero hr h'.1, eq_zero_of_smul_eq_zero hr h'.2]

end Cancel

variable [TrivialStar R]

/-- `star x + x` is twice the coordinate of `1`. -/
theorem star_add_self : ∀ (k : ℕ) (x : Tower R k), star x + x = (2 * re k x) • (1 : Tower R k)
  | 0, x => by
    change star (base x) + base x = (2 * base x) * 1
    rw [star_trivial]
    ring
  | k + 1, ⟨a, b⟩ => by
    change mk (star a) (-b) + mk a b = (2 * re k a) • mk 1 0
    rw [add_mk, star_add_self k a, neg_add_cancel, smul_mk, smul_zero]

/-- An element whose coordinate of `1` vanishes is pure: its star is its
negative. -/
theorem star_eq_neg_of_re_eq_zero {k : ℕ} {x : Tower R k} (h : re k x = 0) : star x = -x := by
  have hs := star_add_self k x
  rw [h, mul_zero, zero_smul] at hs
  exact eq_neg_of_add_eq_zero_left hs

/-- The norm law `x * star x = star x * x = dot x x • 1`. The two are proved
together, since each doubling step uses both at the level below. -/
theorem mul_star_eq_dot : ∀ (k : ℕ) (x : Tower R k),
    x * star x = dot k x x • (1 : Tower R k) ∧ star x * x = dot k x x • (1 : Tower R k)
  | 0, x => by
    change base x * star (base x) = (base x * base x) * 1 ∧
      star (base x) * base x = (base x * base x) * 1
    rw [star_trivial, mul_one]
    exact ⟨rfl, rfl⟩
  | k + 1, ⟨a, b⟩ => by
    obtain ⟨ha1, ha2⟩ := mul_star_eq_dot k a
    obtain ⟨_, hb2⟩ := mul_star_eq_dot k b
    change mk a b * mk (star a) (-b) = (dot k a a + dot k b b) • mk 1 0 ∧
      mk (star a) (-b) * mk a b = (dot k a a + dot k b b) • mk 1 0
    rw [smul_mk, smul_zero, add_smul, mk_mul_mk, mk_mul_mk, mk_inj, mk_inj, star_neg, star_star]
    simp only [neg_mul, mul_neg, sub_neg_eq_add]
    rw [ha1, ha2, hb2]
    exact ⟨⟨rfl, neg_add_cancel _⟩, ⟨rfl, add_neg_cancel _⟩⟩

/-- The adjoint identities `dot (x * y) z = dot y (star x * z)` and
`dot (x * y) z = dot x (z * star y)`, proved together. -/
theorem dot_mul_adjoint : ∀ (k : ℕ) (x y z : Tower R k),
    dot k (x * y) z = dot k y (star x * z) ∧ dot k (x * y) z = dot k x (z * star y)
  | 0, x, y, z => by
    change base x * base y * base z = base y * (star (base x) * base z) ∧
      base x * base y * base z = base x * (base z * star (base y))
    rw [star_trivial, star_trivial]
    exact ⟨by ring, by ring⟩
  | k + 1, ⟨x1, x2⟩, ⟨y1, y2⟩, ⟨z1, z2⟩ => by
    have AL := fun a b c => (dot_mul_adjoint k a b c).1
    have AR := fun a b c => (dot_mul_adjoint k a b c).2
    change dot (k + 1) (mk x1 x2 * mk y1 y2) (mk z1 z2) =
        dot (k + 1) (mk y1 y2) (star (mk x1 x2) * mk z1 z2) ∧
      dot (k + 1) (mk x1 x2 * mk y1 y2) (mk z1 z2) =
        dot (k + 1) (mk x1 x2) (mk z1 z2 * star (mk y1 y2))
    simp only [star_mk, mk_mul_mk, dot_mk, dot_add_left, dot_sub_left, dot_add_right,
      dot_neg_right, star_neg, star_star, neg_mul, mul_neg, sub_neg_eq_add]
    have h1 := AL x1 y1 z1
    have h2 := AL (star y2) x2 z1
    have h3 := AR x2 (star z1) y2
    have h4 := AR y2 x1 z2
    have h5 := AR x2 (star y1) z2
    have h6 := AL (star z2) x2 y1
    have h7 := AR x1 y1 z1
    have h8 := AL y2 x1 z2
    simp only [star_star] at h2 h3 h5 h6
    have c1 := dot_comm k y2 (x2 * star z1)
    have c2 := dot_comm k y1 (star z2 * x2)
    exact ⟨by linear_combination h1 + h4 - h2 + h5 - c2 - h6 + c1 + h3,
      by linear_combination h7 - h2 + h8 + h5⟩

theorem dot_mul_self_right (k : ℕ) (a z : Tower R k) : dot k (a * z) z = dot k z z * re k a := by
  rw [(dot_mul_adjoint k a z z).2, (mul_star_eq_dot k z).1, dot_smul_right, dot_one_right]

theorem dot_mul_self_left (k : ℕ) (a z : Tower R k) : dot k (a * z) a = dot k a a * re k z := by
  rw [(dot_mul_adjoint k a z a).1, (mul_star_eq_dot k a).2, dot_smul_right, dot_one_right]

section Ordered

variable [PartialOrder R] [StarOrderedRing R] [NoZeroDivisors R]

omit [NoZeroDivisors R] in
theorem dot_self_nonneg : ∀ (k : ℕ) (x : Tower R k), 0 ≤ dot k x x
  | 0, x => by
    change 0 ≤ base x * base x
    have h := star_mul_self_nonneg (base x)
    rwa [star_trivial] at h
  | k + 1, ⟨a, b⟩ => add_nonneg (dot_self_nonneg k a) (dot_self_nonneg k b)

theorem eq_zero_of_dot_self_eq_zero : ∀ {k : ℕ} {x : Tower R k}, dot k x x = 0 → x = 0
  | 0, x, h => by
    have hx : base x = 0 := mul_self_eq_zero.1 (show base x * base x = 0 from h)
    exact hx
  | k + 1, ⟨a, b⟩, h => by
    have h' : dot k a a + dot k b b = 0 := h
    rw [add_eq_zero_iff_of_nonneg (dot_self_nonneg k a) (dot_self_nonneg k b)] at h'
    change mk a b = mk 0 0
    rw [eq_zero_of_dot_self_eq_zero h'.1, eq_zero_of_dot_self_eq_zero h'.2]

theorem dot_self_ne_zero {k : ℕ} {x : Tower R k} (hx : x ≠ 0) : dot k x x ≠ 0 :=
  fun h => hx (eq_zero_of_dot_self_eq_zero h)

/-- Lemma 9.4 of Biss, Dugger and Isaksen: when `a * z = 0` with `a` and
`z` nonzero, both are pure. The Rocq original is `purity_left` of the
functor `CdTower` in `rocq/quantum/CdTowerDomain.v`. -/
theorem re_eq_zero_of_mul_eq_zero {k : ℕ} {a z : Tower R k} (h : a * z = 0) (ha : a ≠ 0)
    (hz : z ≠ 0) : re k a = 0 ∧ re k z = 0 := by
  have hr := dot_mul_self_right k a z
  have hl := dot_mul_self_left k a z
  rw [h, dot_zero_left] at hr hl
  exact ⟨(mul_eq_zero.1 hr.symm).resolve_left (dot_self_ne_zero hz),
    (mul_eq_zero.1 hl.symm).resolve_left (dot_self_ne_zero ha)⟩

theorem mul_eq_zero_rev {k : ℕ} {a z : Tower R k} (h : a * z = 0) : z * a = 0 := by
  by_cases ha : a = 0
  · rw [ha, mul_zero]
  by_cases hz : z = 0
  · rw [hz, zero_mul]
  obtain ⟨ra, rz⟩ := re_eq_zero_of_mul_eq_zero h ha hz
  rw [← neg_mul_neg, ← star_eq_neg_of_re_eq_zero ra, ← star_eq_neg_of_re_eq_zero rz,
    ← star_mul, h, star_zero]

/-- Corollary 9.3 of Biss, Dugger and Isaksen: the left and right
annihilators of every element coincide, at every level. The Rocq original is
`kernel_equality` of the functor `CdTower` in `rocq/quantum/CdTowerDomain.v`. -/
theorem mul_eq_zero_iff_rev {k : ℕ} (a z : Tower R k) : a * z = 0 ↔ z * a = 0 :=
  ⟨mul_eq_zero_rev, mul_eq_zero_rev⟩

/-- Direct finiteness: a right inverse is a left inverse. The Rocq original
is `direct_finiteness` of the functor `CdTower` in
`rocq/quantum/CdTowerDomain.v`. -/
theorem mul_eq_one_rev {k : ℕ} {a b : Tower R k} (h : a * b = 1) : b * a = 1 := by
  by_cases ha : a = 0
  · have h01 : (0 : Tower R k) = 1 := by rw [← h, ha, zero_mul]
    rw [← mul_one (b * a), ← h01, mul_zero]
  have hw : a * (dot k a a • b - star a) = 0 := by
    rw [mul_sub, mul_smul_comm', h, (mul_star_eq_dot k a).1, sub_self]
  have hw' := mul_eq_zero_rev hw
  rw [sub_mul, smul_mul_assoc', (mul_star_eq_dot k a).2, ← smul_sub] at hw'
  exact sub_eq_zero.1 (eq_zero_of_smul_eq_zero (dot_self_ne_zero ha) hw')

/-- The hypotheses hold over the integers. -/
example (a z : Tower ℤ 5) (h : a * z = 0) : z * a = 0 := (mul_eq_zero_iff_rev a z).1 h

/-- The hypotheses hold over the reals. -/
example (a b : Tower ℝ 7) (h : a * b = 1) : b * a = 1 := mul_eq_one_rev h

end Ordered

end Tower

end CayleyDickson
