/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AlternativeIdentities

/-!
# The commutator of two elements of a double with pure first halves

Convention: the product of `CayleyDickson A` is that of `GororobaMath.CayleyDickson.Basic`,
`(a, b) (c, d) = (a c - star d b, d a + b star c)`, with `star (a, b) = (star a, -b)`, over a
nonassociative ring `A` with a star. An element `a` of `A` is pure when `star a = -a`.

For `z = (a, b)` and `k = (c, d)` with `a` and `c` pure, `star c = -c` and `star a = -a` turn
the second halves of `z k` and `k z` into `d a - b c` and its negative, so the commutator is
`([a, c] - (star d b - star b d), 2 (d a - b c))`. The identity uses distributivity alone: no
associativity, alternativity or commutativity of `A` enters, so it holds in the double of every
level of the tower. Row A5-472 of the findings ledger of gororoba-quantum
(`docs/evidence/a5-exceptional-fibers/ledger.tsv`) states it for the double of the octonions,
the instance `A := Tower R 3`.

## Main results

* `CayleyDickson.mul_sub_mul_of_star_eq_neg`: the commutator formula.
* `CayleyDickson.mul_comm_iff_of_star_eq_neg`: where `x + x = 0` forces `x = 0` in `A`, the
  two elements commute exactly when `[a, c] = star d b - star b d` and `d a = b c`.
* `CayleyDickson.mul_sub_mul_im_of_add_self_eq_zero`: where `x + x = 0` for every `x`
  (characteristic 2), the second half of the commutator is zero for every such pair.
* `Tower.dot_mul_mul_right_of_le_three`, `Tower.dot_mul_mul_left_of_le_three`: at levels up to
  3, `dot (x * a) (y * a) = dot x y * dot a a` and `dot (b * x) (b * y) = dot b b * dot x y`, from
  the adjoint identities and the inverse properties `Tower.mul_mul_star_of_le_three` and
  `Tower.star_mul_mul_of_le_three`, over every commutative ring with the identity as star.
* `Tower.dot_mul_dot_eq_of_mul_eq_mul_polar`, `Tower.dot_mul_dot_eq_of_mul_eq_mul`: for two
  solutions `(c, d)` and `(c', d')` of `d a = b c` at levels up to 3,
  `dot d d' * |a|^2 = |b|^2 * dot c c'`, and `|d|^2 |a|^2 = |b|^2 |c|^2` for one. With `z = (a, b)`
  and `k = (c, d)` in the double of the octonions and `a`, `c` pure, `dot a a` is the form
  `N1(z)` of the row and `dot b b` is `(N2 + N3)(z)`, so these read
  `N1(z) (N2 + N3)(k) = (N2 + N3)(z) N1(k)` and its polarization on the solutions of `d a = b c`.
-/

@[expose] public section

namespace CayleyDickson

section Commutator

variable {A : Type*} [NonAssocRing A] [StarRing A]

/-- The commutator of `(a, b)` and `(c, d)` with `a` and `c` pure. -/
theorem mul_sub_mul_of_star_eq_neg {a b c d : A} (ha : star a = -a) (hc : star c = -c) :
    ((⟨a, b⟩ : CayleyDickson A) * ⟨c, d⟩ - ⟨c, d⟩ * ⟨a, b⟩) =
      ⟨a * c - c * a - (star d * b - star b * d), d * a - b * c + (d * a - b * c)⟩ := by
  ext
  · simp only [sub_re, mul_re]
    abel
  · simp only [sub_im, mul_im, ha, hc, mul_neg]
    abel

/-- Where `x + x = 0` forces `x = 0`, two elements with pure first halves commute exactly when
both halves of the commutator formula vanish. -/
theorem mul_comm_iff_of_star_eq_neg (h2 : ∀ x : A, x + x = 0 → x = 0) {a b c d : A}
    (ha : star a = -a) (hc : star c = -c) :
    (⟨a, b⟩ : CayleyDickson A) * ⟨c, d⟩ = ⟨c, d⟩ * ⟨a, b⟩ ↔
      a * c - c * a = star d * b - star b * d ∧ d * a = b * c := by
  rw [← sub_eq_zero, mul_sub_mul_of_star_eq_neg ha hc]
  constructor
  · intro h
    have h1 : a * c - c * a - (star d * b - star b * d) = 0 := congrArg CayleyDickson.re h
    have h3 : d * a - b * c + (d * a - b * c) = 0 := congrArg CayleyDickson.im h
    exact ⟨sub_eq_zero.1 h1, sub_eq_zero.1 (h2 _ h3)⟩
  · rintro ⟨h1, h3⟩
    ext
    · exact sub_eq_zero.2 h1
    · change d * a - b * c + (d * a - b * c) = 0
      rw [sub_eq_zero.2 h3, add_zero]

/-- Where `x + x = 0` for every `x`, the second half of the commutator of two elements with pure
first halves is zero. -/
theorem mul_sub_mul_im_of_add_self_eq_zero (h2 : ∀ x : A, x + x = 0) {a b c d : A}
    (ha : star a = -a) (hc : star c = -c) :
    ((⟨a, b⟩ : CayleyDickson A) * ⟨c, d⟩ - ⟨c, d⟩ * ⟨a, b⟩).im = 0 := by
  rw [mul_sub_mul_of_star_eq_neg ha hc]
  exact h2 _

end Commutator

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

/-- At levels up to 3, right multiplication by `a` scales the trace form by `dot a a`. -/
theorem dot_mul_mul_right_of_le_three {k : ℕ} (hk : k ≤ 3) (x y a : Tower R k) :
    dot k (x * a) (y * a) = dot k x y * dot k a a := by
  rw [(dot_mul_adjoint k x a (y * a)).2, mul_mul_star_of_le_three hk a y, dot_smul_right,
    mul_comm]

/-- At levels up to 3, left multiplication by `b` scales the trace form by `dot b b`. -/
theorem dot_mul_mul_left_of_le_three {k : ℕ} (hk : k ≤ 3) (b x y : Tower R k) :
    dot k (b * x) (b * y) = dot k b b * dot k x y := by
  rw [(dot_mul_adjoint k b x (b * y)).1, star_mul_mul_of_le_three hk b y, dot_smul_right]

/-- At levels up to 3, two solutions `(c, d)` and `(c', d')` of `d * a = b * c` satisfy
`dot d d' * |a|^2 = |b|^2 * dot c c'`. -/
theorem dot_mul_dot_eq_of_mul_eq_mul_polar {k : ℕ} (hk : k ≤ 3)
    {a b c d c' d' : Tower R k} (h : d * a = b * c) (h' : d' * a = b * c') :
    dot k d d' * dot k a a = dot k b b * dot k c c' := by
  rw [← dot_mul_mul_right_of_le_three hk, ← dot_mul_mul_left_of_le_three hk, h, h']

/-- At levels up to 3, `d * a = b * c` gives `|d|^2 |a|^2 = |b|^2 |c|^2`. -/
theorem dot_mul_dot_eq_of_mul_eq_mul {k : ℕ} (hk : k ≤ 3) {a b c d : Tower R k}
    (h : d * a = b * c) : dot k d d * dot k a a = dot k b b * dot k c c :=
  dot_mul_dot_eq_of_mul_eq_mul_polar hk h h

end Tower

end CayleyDickson
