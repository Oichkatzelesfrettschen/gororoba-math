/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TraceForm

/-!
# The bilinear and trilinear forms of left multiplication

Convention: the product of `Tower R k` is the Cayley-Dickson product of
`GororobaMath.CayleyDickson.Tower`, `(a, b) (c, d) = (a c - star d b, d a + b star c)`, over a
commutative ring whose star is the identity; `Tower.dot k` is the trace form and `Tower.re k`
the coordinate of `1` of `GororobaMath.CayleyDickson.AnnihilatorSymmetry`, and an element `a`
is pure when `star a = -a`. Left multiplication by `a` is `L_a`, and its kernel `{u | a * u = 0}`
is the right annihilator of `a`.

Three forms are read off `L_a`:

* `Tower.gramForm k a u v = dot (a * u) (a * v)`, the pullback of the trace form along `L_a`,
  symmetric and, over an ordered ring, positive semidefinite;
* `Tower.skewForm k a u v = dot u (a * v)`, skew in `u` and `v` when `a` is pure;
* `Tower.tripleForm k a b c = dot a (b * c)`, alternating on pure elements.

`skewForm k a u v` is linear in the point `a`, so on the module of pure elements it is a two-form
with linear coefficients and its exterior derivative at `a`, evaluated on constant vector fields
`a`, `b`, `c`, is the alternating sum of the directional derivatives
`skewForm a b c - skewForm b a c + skewForm c a b`. `Tower.skewForm_exterior_derivative` evaluates
that sum to `-3 * tripleForm a b c`. The statement is this algebraic identity; no manifold, sphere
or differential form of Mathlib enters it. `tripleForm` has constant coefficients, so the two-form
is not closed and its derivative is an exact three-form.

No step uses associativity or alternativity. The radical statements use the ordered hypotheses of
`GororobaMath.CayleyDickson.AnnihilatorSymmetry` (`ℤ`, `ℚ`, `ℝ`, every ordered field), under which
the trace form is definite.

## Main results

* `Tower.skewForm_swap`, `Tower.skewForm_self`: `skewForm a` is skew, and vanishes on the
  diagonal when `re a = 0`.
* `Tower.tripleForm_swap_left`, `Tower.tripleForm_swap_outer`, `Tower.tripleForm_swap_right`:
  `tripleForm` changes sign under each transposition of pure arguments.
* `Tower.skewForm_exterior_derivative`: for pure `a`, `b`, `c`,
  `skewForm a b c - skewForm b a c + skewForm c a b = -3 * tripleForm a b c`.
* `Tower.gramForm_self_eq_zero_iff`, `Tower.forall_gramForm_eq_zero_iff`: the isotropic vectors
  and the radical of `gramForm a` are the kernel of `L_a`.
* `Tower.forall_skewForm_eq_zero_iff`: for pure `a` the radical of `skewForm a` is the kernel of
  `L_a`.
* `Tower.re_mul_eq_zero_of_dot_eq_zero`, `Tower.dot_mul_self_eq_zero_of_re_eq_zero`: for pure
  `a`, `L_a` preserves the orthogonal complement of `1` and `a`, the tangent space at `a` of
  the sphere of pure elements of norm `dot a a`.
* `Tower.re_eq_zero_and_dot_eq_zero_of_mul_eq_zero`: the kernel of `L_a` lies in that complement.
* `Tower.mul_eq_zero_iff_forall_tangent_skewForm_eq_zero`: the radical of `skewForm a` restricted
  to that complement is again the kernel of `L_a`. Over a field the restricted form then has rank
  `2 ^ k - 2 - nullity a` by rank-nullity; that count is not stated here.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] {k : ℕ}

/-- The pullback of the trace form along left multiplication by `a`. -/
def gramForm (k : ℕ) (a u v : Tower R k) : R := dot k (a * u) (a * v)

/-- The form `dot u (a * v)`, skew in `u` and `v` when `a` is pure. -/
def skewForm (k : ℕ) (a u v : Tower R k) : R := dot k u (a * v)

/-- The trilinear form `dot a (b * c)`, alternating on pure elements. -/
def tripleForm (k : ℕ) (a b c : Tower R k) : R := dot k a (b * c)

omit [TrivialStar R] in
theorem skewForm_eq_tripleForm (a u v : Tower R k) : skewForm k a u v = tripleForm k u a v := rfl

omit [TrivialStar R] in
theorem gramForm_comm (a u v : Tower R k) : gramForm k a u v = gramForm k a v u :=
  dot_comm k _ _

/-- For pure `a` the form `skewForm a` is skew. -/
theorem skewForm_swap {a : Tower R k} (ha : star a = -a) (u v : Tower R k) :
    skewForm k a v u = -skewForm k a u v := by
  rw [skewForm, skewForm, dot_comm k v (a * u), dot_mul_left_of_star_eq_neg ha]

/-- When `re a = 0` the form `skewForm a` vanishes on the diagonal. -/
theorem skewForm_self {a : Tower R k} (hre : re k a = 0) (u : Tower R k) :
    skewForm k a u u = 0 := by
  rw [skewForm, dot_comm k u (a * u), dot_mul_self_right, hre, mul_zero]

/-- `tripleForm` changes sign when its first two arguments are exchanged, for a pure third. -/
theorem tripleForm_swap_left {c : Tower R k} (hc : star c = -c) (a b : Tower R k) :
    tripleForm k b a c = -tripleForm k a b c := by
  rw [tripleForm, tripleForm, dot_comm k b (a * c), dot_mul_right_of_star_eq_neg hc]

/-- `tripleForm` changes sign when its outer arguments are exchanged, for a pure middle one. -/
theorem tripleForm_swap_outer {b : Tower R k} (hb : star b = -b) (a c : Tower R k) :
    tripleForm k c b a = -tripleForm k a b c := by
  rw [tripleForm, tripleForm, dot_comm k a (b * c), dot_mul_left_of_star_eq_neg hb, neg_neg]

/-- `tripleForm` changes sign when its last two arguments are exchanged, for pure arguments. -/
theorem tripleForm_swap_right {a b c : Tower R k} (ha : star a = -a) (hb : star b = -b)
    (hc : star c = -c) : tripleForm k a c b = -tripleForm k a b c := by
  have h1 := tripleForm_swap_left hb a c
  have h2 := tripleForm_swap_outer ha c b
  have h3 := tripleForm_swap_left hc a b
  linear_combination h1 - h2 + h3

/-- The exterior derivative of the two-form `a ↦ skewForm a` on pure elements, in the constant
directions `a`, `b`, `c`, is `-3 * tripleForm a b c`. -/
theorem skewForm_exterior_derivative {a b c : Tower R k} (ha : star a = -a) (hb : star b = -b)
    (hc : star c = -c) :
    skewForm k a b c - skewForm k b a c + skewForm k c a b = -3 * tripleForm k a b c := by
  have h1 := tripleForm_swap_left hc a b
  have h2 := tripleForm_swap_right ha hb hc
  simp only [skewForm_eq_tripleForm]
  linear_combination h1 + h2

/-- For pure `a`, `re (a * u) = 0` when `u` is orthogonal to `a`. -/
theorem re_mul_eq_zero_of_dot_eq_zero {a u : Tower R k} (ha : star a = -a)
    (hua : dot k u a = 0) : re k (a * u) = 0 := by
  rw [← dot_one_right, dot_mul_left_of_star_eq_neg ha, mul_one, hua, neg_zero]

/-- `a * u` is orthogonal to `a` when `re u = 0`. -/
theorem dot_mul_self_eq_zero_of_re_eq_zero {a u : Tower R k} (hu : re k u = 0) :
    dot k (a * u) a = 0 := by
  rw [dot_mul_self_left, hu, mul_zero]

section Ordered

variable [PartialOrder R] [IsOrderedAddMonoid R] [NoZeroDivisors R]

omit [TrivialStar R] in
/-- The isotropic vectors of `gramForm a` are the kernel of left multiplication by `a`. -/
theorem gramForm_self_eq_zero_iff (hsq : ∀ x : R, 0 ≤ x * x) (a u : Tower R k) :
    gramForm k a u u = 0 ↔ a * u = 0 := by
  constructor
  · intro h
    exact eq_zero_of_dot_self_eq_zero hsq h
  · intro h
    rw [gramForm, h, dot_zero_left]

omit [TrivialStar R] in
/-- The radical of `gramForm a` is the kernel of left multiplication by `a`. -/
theorem forall_gramForm_eq_zero_iff (hsq : ∀ x : R, 0 ≤ x * x) (a u : Tower R k) :
    (∀ v, gramForm k a u v = 0) ↔ a * u = 0 := by
  constructor
  · intro h
    exact (gramForm_self_eq_zero_iff hsq a u).1 (h u)
  · intro h v
    rw [gramForm, h, dot_zero_left]

/-- For pure `a` the radical of `skewForm a` is the kernel of left multiplication by `a`. -/
theorem forall_skewForm_eq_zero_iff (hsq : ∀ x : R, 0 ≤ x * x) {a : Tower R k}
    (ha : star a = -a) (u : Tower R k) : (∀ v, skewForm k a u v = 0) ↔ a * u = 0 :=
  (mul_eq_zero_iff_forall_dot_mul_eq_zero hsq ha u).symm

/-- A nonzero element of the kernel of left multiplication by a nonzero `a` is orthogonal to `1`
and to `a`. -/
theorem re_eq_zero_and_dot_eq_zero_of_mul_eq_zero (hsq : ∀ x : R, 0 ≤ x * x) {a u : Tower R k}
    (h : a * u = 0) (ha : a ≠ 0) (hu : u ≠ 0) : re k u = 0 ∧ dot k u a = 0 :=
  ⟨(re_eq_zero_of_mul_eq_zero hsq h ha hu).2, by
    rw [dot_comm]
    exact dot_eq_zero_of_mul_eq_zero hsq h⟩

/-- For pure `a` and `u` orthogonal to `1` and `a`, `a * u = 0` exactly when `skewForm a u`
vanishes on every `v` orthogonal to `1` and `a`: the radical of the restricted form is the kernel
of left multiplication by `a`. -/
theorem mul_eq_zero_iff_forall_tangent_skewForm_eq_zero (hsq : ∀ x : R, 0 ≤ x * x)
    {a u : Tower R k} (ha : star a = -a) (hu : re k u = 0) (hua : dot k u a = 0) :
    a * u = 0 ↔ ∀ v, re k v = 0 → dot k v a = 0 → skewForm k a u v = 0 := by
  constructor
  · intro h v _ _
    exact (forall_skewForm_eq_zero_iff hsq ha u).2 h v
  · intro h
    have h0 := h (a * u) (re_mul_eq_zero_of_dot_eq_zero ha hua)
      (dot_mul_self_eq_zero_of_re_eq_zero hu)
    rw [skewForm] at h0
    apply eq_zero_of_dot_self_eq_zero hsq
    rw [dot_mul_left_of_star_eq_neg ha u (a * u), h0, neg_zero]

end Ordered

end Tower

end CayleyDickson
