/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Tower

/-!
# Challenge: zero products from aligned pairs of a two-term operand

This file restates, with `sorry` as each proof, the headline theorems that
`GororobaMath.CayleyDickson.TwoTerm` proves and that the "Lean library" table of `README.md` names, together with the definitions that
`GororobaMath.CayleyDickson.TwoTerm` introduces and those statements use.
This file imports the library module that the solution module itself imports, so `Tower`, `e` and
`negSign` are the library's own; a restated definition copies the solution's text and must elaborate to
the same constant.
`lake comparator --config` with the JSON file beside this one checks that each named theorem of the
solution module has the statement written here and depends only on `propext`, `Classical.choice` and
`Quot.sound`. No library module imports this file, and the admission gate does not build it.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [NonAssocRing R] [StarRing R]

/-- The partner index of `x` under the operand `e i + e j`. -/
def partner {k : ℕ} (i j x : BitVec k) : BitVec k := x ^^^ i ^^^ j

/-- The pair `{x, partner i j x}` is aligned with opposite signs: the sign
of `e i * e x` is opposite to that of `e j * e x'`, and the sign of
`e j * e x` opposite to that of `e i * e x'`. -/
def alignedAdd (k : ℕ) (i j x : BitVec k) : Bool :=
  (negSign k i x != negSign k j (partner i j x)) &&
    (negSign k j x != negSign k i (partner i j x))

/-- The pair `{x, partner i j x}` is aligned with equal signs. -/
def alignedSub (k : ℕ) (i j x : BitVec k) : Bool :=
  (negSign k i x == negSign k j (partner i j x)) &&
    (negSign k j x == negSign k i (partner i j x))

/-- An aligned pair of opposite signs gives the zero product
`(e i + e j) * (e x + e x') = 0`. -/
theorem two_term_mul_add_eq_zero (k : ℕ) (i j x : BitVec k) (h : alignedAdd k i j x = true) :
    (e R k i + e R k j) * (e R k x + e R k (partner i j x)) = 0 := by
  sorry

/-- An aligned pair of equal signs gives the zero product
`(e i + e j) * (e x - e x') = 0`. -/
theorem two_term_mul_sub_eq_zero (k : ℕ) (i j x : BitVec k) (h : alignedSub k i j x = true) :
    (e R k i + e R k j) * (e R k x - e R k (partner i j x)) = 0 := by
  sorry

end Tower

end CayleyDickson
