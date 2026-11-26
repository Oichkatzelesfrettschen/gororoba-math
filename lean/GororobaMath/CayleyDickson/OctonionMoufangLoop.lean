/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Alternative
public import GororobaMath.CayleyDickson.NormMultiplicative
public import GororobaMath.CayleyDickson.Kaplansky
public import GororobaMath.CayleyDickson.NonAssociative
public import GororobaMath.CayleyDickson.TraceForm

/-!
# The unit-norm octonions form a Moufang loop

Convention: the product and the star of `Tower R k` are those of
`GororobaMath.CayleyDickson.Tower`, `(a, b) (c, d) = (a c - star d b, d a + b star c)`, over a
commutative ring `R` whose star is the identity (`TrivialStar R`); `Tower R 3` is the octonion
algebra with coefficients in `R`. `Tower.dot k x y` is the trace form of
`GororobaMath.CayleyDickson.AnnihilatorSymmetry`, so `dot 3 x x` is the sum of the eight squares of
the coordinates of `x`, and a unit-norm octonion is an element with `dot 3 x x = 1`.

`CayleyDickson.IsMoufangLoop` has the fields of agda-stdlib v2.4 `Algebra.Structures.IsMoufangLoop`
(the definitions `LeftDividesˡ`, `LeftDividesʳ`, `RightDividesˡ`, `RightDividesʳ`, `LeftBol`,
`RightBol` and `Identical` of `Algebra.Definitions`) with propositional equality, so congruence of
the operations is automatic. Mathlib v4.35.0 defines no loop.

The Agda partner is `agda/src/GororobaMath/CayleyDickson/OctonionMoufangLoop.agda`, theorem
`isMoufangLoop`, which proves the same packaging with agda-stdlib's structure and runs on demand
through `ci/check_agda.sh`.

## Main results

* `Tower.mul_star_mul_of_le_three`, `Tower.star_mul_mul_of_le_three`,
  `Tower.mul_star_mul_right_of_le_three`, `Tower.mul_mul_star_of_le_three`: at levels up to 3,
  `x (star x y) = star x (x y) = dot x x • y` and `(y star x) x = (y x) star x = dot x x • y`.
* `Tower.OctonionUnit`: the unit-norm elements of `Tower R 3`, closed under the product, the left
  division `star x * y` and the right division `y * star x`.
* `Tower.octonionUnit_isMoufangLoop`: the unit-norm octonions satisfy `IsMoufangLoop`.
* `Tower.OctonionUnit.not_mul_assoc`: the loop is not associative when `2 ≠ 0` in `R`.
-/

@[expose] public section

namespace CayleyDickson

/-- The laws of agda-stdlib v2.4 `Algebra.Structures.IsMoufangLoop`: two-sided division, the unit,
the left and right Bol identities and the identical (middle) Moufang identity, with propositional
equality. -/
structure IsMoufangLoop {L : Type*} (mul ldiv rdiv : L → L → L) (one : L) : Prop where
  leftDivides_left : ∀ x y, mul x (ldiv x y) = y
  leftDivides_right : ∀ x y, ldiv x (mul x y) = y
  rightDivides_left : ∀ x y, mul (rdiv y x) x = y
  rightDivides_right : ∀ x y, rdiv (mul y x) x = y
  one_mul : ∀ x, mul one x = x
  mul_one : ∀ x, mul x one = x
  leftBol : ∀ x y z, mul x (mul y (mul x z)) = mul (mul x (mul y x)) z
  rightBol : ∀ x y z, mul (mul (mul z x) y) x = mul z (mul (mul x y) x)
  identical : ∀ x y z, mul (mul z x) (mul y z) = mul z (mul (mul x y) z)

namespace Tower

universe u

section Divisions

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] {k : ℕ}

/-- Left alternativity gives `x (star x y) = dot x x • y` at levels up to 3. -/
theorem mul_star_mul_of_le_three (hk : k ≤ 3) (x y : Tower R k) :
    x * (star x * y) = dot k x x • y := by
  rw [star_eq_smul_one_sub]
  simp only [sub_mul, mul_sub, smul_mul_assoc', mul_smul_comm', one_mul,
    left_alternative_of_le_three hk, mul_self_eq_smul_sub, sub_sub_cancel]

/-- Left alternativity gives `star x (x y) = dot x x • y` at levels up to 3. -/
theorem star_mul_mul_of_le_three (hk : k ≤ 3) (x y : Tower R k) :
    star x * (x * y) = dot k x x • y := by
  have h := star_eq_smul_one_sub x
  have hx : star x * (x * y) = (2 * re k x) • (x * y) - x * (x * y) := by
    rw [h, sub_mul, smul_mul_assoc', one_mul]
  rw [hx, left_alternative_of_le_three hk]
  simp only [mul_self_eq_smul_sub, sub_mul, smul_mul_assoc', one_mul, sub_sub_cancel]

/-- Right alternativity gives `(y star x) x = dot x x • y` at levels up to 3. -/
theorem mul_star_mul_right_of_le_three (hk : k ≤ 3) (x y : Tower R k) :
    (y * star x) * x = dot k x x • y := by
  rw [star_eq_smul_one_sub]
  simp only [sub_mul, mul_sub, smul_mul_assoc', mul_smul_comm', mul_one,
    right_alternative_of_le_three hk, mul_self_eq_smul_sub, sub_sub_cancel]

/-- Right alternativity gives `(y x) star x = dot x x • y` at levels up to 3. -/
theorem mul_mul_star_of_le_three (hk : k ≤ 3) (x y : Tower R k) :
    (y * x) * star x = dot k x x • y := by
  rw [star_eq_smul_one_sub]
  simp only [mul_sub, mul_smul_comm', mul_one,
    right_alternative_of_le_three hk, mul_self_eq_smul_sub, sub_sub_cancel]

/-- The trace form of the star equals that of the element. -/
theorem dot_star_self (x : Tower R k) : dot k (star x) (star x) = dot k x x := by
  have h1 := (mul_star_eq_dot k (star x)).1
  rw [star_star] at h1
  have h2 := (mul_star_eq_dot k x).2
  have h3 := congrArg (re k) (h1.symm.trans h2)
  simpa only [re_smul, re_one, mul_one] using h3

omit [TrivialStar R] in
/-- A basis element has trace form `1`. -/
theorem dot_e_self : ∀ (k : ℕ) (p : BitVec k), dot k (e R k p) (e R k p) = 1
  | 0, _ => by
    rw [e_zero_level]
    change (1 : R) * 1 = 1
    exact mul_one 1
  | k + 1, p => by
    cases hp : p.msb
    · rw [e_succ_of_not_msb hp, dot_mk, dot_e_self k, dot_zero_left, add_zero]
    · rw [e_succ_of_msb hp, dot_mk, dot_e_self k, dot_zero_left, zero_add]

end Divisions

section Loop

variable (R : Type u) [CommRing R] [StarRing R]

/-- The unit-norm octonions: the elements of `Tower R 3` with `dot 3 x x = 1`. -/
def OctonionUnit : Type u := {x : Tower R 3 // dot 3 x x = 1}

namespace OctonionUnit

variable {R} [TrivialStar R]

/-- The product of unit-norm octonions, closed by the multiplicativity of the trace form. -/
def mul (x y : OctonionUnit R) : OctonionUnit R :=
  ⟨x.1 * y.1, by rw [dot_mul_self_of_le_three le_rfl, x.2, y.2, one_mul]⟩

/-- The left division `ldiv x y = star x * y`. -/
def ldiv (x y : OctonionUnit R) : OctonionUnit R :=
  ⟨star x.1 * y.1, by rw [dot_mul_self_of_le_three le_rfl, dot_star_self, x.2, y.2, one_mul]⟩

/-- The right division `rdiv y x = y * star x`. -/
def rdiv (y x : OctonionUnit R) : OctonionUnit R :=
  ⟨y.1 * star x.1, by rw [dot_mul_self_of_le_three le_rfl, dot_star_self, x.2, y.2, one_mul]⟩

/-- The unit `1`. -/
def one : OctonionUnit R :=
  ⟨1, by rw [dot_one_right, re_one]⟩

end OctonionUnit

open OctonionUnit in
/-- The unit-norm octonions over a commutative ring with trivial star form a Moufang loop, with
the divisions `star x * y` and `y * star x`; the Bol and middle identities are the level-3
laws of `Alternative.lean`. -/
theorem octonionUnit_isMoufangLoop [TrivialStar R] :
    IsMoufangLoop (mul (R := R)) ldiv rdiv one where
  leftDivides_left x y := Subtype.ext <| by
    change x.1 * (star x.1 * y.1) = y.1
    rw [mul_star_mul_of_le_three le_rfl, x.2, one_smul]
  leftDivides_right x y := Subtype.ext <| by
    change star x.1 * (x.1 * y.1) = y.1
    rw [star_mul_mul_of_le_three le_rfl, x.2, one_smul]
  rightDivides_left x y := Subtype.ext <| by
    change (y.1 * star x.1) * x.1 = y.1
    rw [mul_star_mul_right_of_le_three le_rfl, x.2, one_smul]
  rightDivides_right x y := Subtype.ext <| by
    change (y.1 * x.1) * star x.1 = y.1
    rw [mul_mul_star_of_le_three le_rfl, x.2, one_smul]
  one_mul x := Subtype.ext (one_mul x.1)
  mul_one x := Subtype.ext (mul_one x.1)
  leftBol x y z := Subtype.ext (bol_left_of_le_three le_rfl x.1 y.1 z.1)
  rightBol x y z := Subtype.ext (bol_right_of_le_three le_rfl x.1 y.1 z.1)
  identical x y z := Subtype.ext (moufang_middle_of_le_three le_rfl z.1 x.1 y.1)

/-- Over a ring with `2 ≠ 0`, the product of the unit-norm octonions is not associative: the
basis elements `e 1, e 2, e 4` have trace form `1` and a nonzero associator. -/
theorem OctonionUnit.not_mul_assoc [TrivialStar R] (h2 : (2 : R) ≠ 0) :
    ¬ ∀ x y z : OctonionUnit R, mul (mul x y) z = mul x (mul y z) := by
  intro h
  have h' : e R 3 1#3 * e R 3 2#3 * e R 3 4#3 = e R 3 1#3 * (e R 3 2#3 * e R 3 4#3) :=
    congrArg Subtype.val
      (h ⟨e R 3 1#3, dot_e_self 3 _⟩ ⟨e R 3 2#3, dot_e_self 3 _⟩ ⟨e R 3 4#3, dot_e_self 3 _⟩)
  have h0 := sub_eq_zero.2 h'
  have h1 : associator (e R 3 1#3) (e R 3 2#3) (e R 3 4#3) = 0 := h0
  rw [associator_e_e_e] at h1
  have hc : basisAssocCoeff 3 1#3 2#3 4#3 = 2 ∨ basisAssocCoeff 3 1#3 2#3 4#3 = -2 := by decide
  rcases hc with hc | hc
  · rw [hc] at h1
    exact two_zsmul_e_ne_zero h2 3 _ h1
  · rw [hc, neg_smul, neg_eq_zero] at h1
    exact two_zsmul_e_ne_zero h2 3 _ h1

end Loop

end Tower

end CayleyDickson
