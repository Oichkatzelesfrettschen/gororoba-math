/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.ZeroDivisors
public import GororobaMath.CayleyDickson.TraceForm

/-!
# Sedenion witness products of a zero-divisor selector case

Convention: `Tower R 4` is the sedenion algebra of `GororobaMath.CayleyDickson.Tower`,
`Tower.e R 4 p` is the basis unit of index `p`, and `Tower.dot 4` is the trace form, so
`dot 4 x x` is the sum of the squares of the sixteen coordinates of `x`. The three products below
are the ones `cd_core.cd_multiply_exact` of gororoba-quantum evaluates for the selector
probabilities of its zero-divisor hardware case, where
`P(s = 0) = dot 4 (u * v) (u * v) / 8` for `u = e₁ + e₁₀`.

## Main results

* `Tower.sedenion_dark_mul_eq_zero`, `Tower.sedenion_dark_factors_ne_zero`: the product
  `(e₁ + e₁₀)(e₄ - e₁₅)` is `0` over every ring, and both factors are nonzero over a nontrivial
  ring.
* `Tower.sedenion_bright_mul`, `Tower.sedenion_bright_dot`: `(e₁ + e₁₀)(e₄ + e₁₅) = 2 (e₅ - e₁₄)`
  over every ring, and `dot` of the product with itself is `8`.
* `Tower.sedenion_fixture_mul`, `Tower.sedenion_fixture_dot`:
  `(e₁ + e₁₀)(e₂ - e₁₃) = e₃ + e₇ + e₈ - e₁₂`, four signed units of four distinct indices, and
  `dot` of the product with itself is `4`.
* `Tower.sedenion_witness_selector_probabilities`: the three squared norms divided by `8` are
  `0`, `1` and `1/2` over a field of characteristic zero.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

section Products

variable {R : Type u} [NonAssocRing R] [StarRing R]

/-- A product of two basis units whose sign bit is clear is the unit of the exclusive or. -/
theorem e_mul_e_of_not_negSign {k : ℕ} {p q r : BitVec k} (hr : p ^^^ q = r)
    (h : negSign k p q = false) : e R k p * e R k q = e R k r := by
  rw [e_mul_e, h, hr]
  rfl

/-- A product of two basis units whose sign bit is set is the negated unit of the exclusive or. -/
theorem e_mul_e_of_negSign {k : ℕ} {p q r : BitVec k} (hr : p ^^^ q = r)
    (h : negSign k p q = true) : e R k p * e R k q = -e R k r := by
  rw [e_mul_e, h, hr]
  rfl

/-- The dark witness: `(e₁ + e₁₀)(e₄ - e₁₅) = 0` over every ring. -/
theorem sedenion_dark_mul_eq_zero :
    (e R 4 1#4 + e R 4 10#4) * (e R 4 4#4 - e R 4 15#4) = 0 := by
  have h : partner 1#4 10#4 4#4 = 15#4 := by decide
  have := two_term_mul_sub_eq_zero (R := R) 4 1#4 10#4 4#4 (by decide)
  rwa [h] at this

/-- The bright control: `(e₁ + e₁₀)(e₄ + e₁₅) = 2 (e₅ - e₁₄)` over every ring. -/
theorem sedenion_bright_mul :
    (e R 4 1#4 + e R 4 10#4) * (e R 4 4#4 + e R 4 15#4) =
      (2 : ℤ) • (e R 4 5#4 - e R 4 14#4) := by
  rw [add_mul, mul_add, mul_add, e_mul_e_of_not_negSign (r := 5#4) (by decide) (by decide),
    e_mul_e_of_negSign (r := 14#4) (by decide) (by decide),
    e_mul_e_of_negSign (r := 14#4) (by decide) (by decide),
    e_mul_e_of_not_negSign (r := 5#4) (by decide) (by decide), two_smul]
  abel

/-- The fixture: `(e₁ + e₁₀)(e₂ - e₁₃) = e₃ + e₇ + e₈ - e₁₂`, four units of four distinct
indices. -/
theorem sedenion_fixture_mul :
    (e R 4 1#4 + e R 4 10#4) * (e R 4 2#4 - e R 4 13#4) =
      e R 4 3#4 + e R 4 7#4 + e R 4 8#4 - e R 4 12#4 := by
  rw [sub_eq_add_neg, add_mul, mul_add, mul_add, mul_neg, mul_neg,
    e_mul_e_of_not_negSign (r := 3#4) (by decide) (by decide),
    e_mul_e_of_not_negSign (r := 12#4) (by decide) (by decide),
    e_mul_e_of_not_negSign (r := 8#4) (by decide) (by decide),
    e_mul_e_of_negSign (r := 7#4) (by decide) (by decide)]
  abel

end Products

section Nonzero

variable {R : Type u} [NonAssocRing R] [StarRing R] [Nontrivial R]

/-- Both factors of the dark witness are nonzero. -/
theorem sedenion_dark_factors_ne_zero :
    e R 4 1#4 + e R 4 10#4 ≠ 0 ∧ e R 4 4#4 - e R 4 15#4 ≠ 0 := by
  refine ⟨e_add_e_ne_zero (k := 3) (p := 1#4) (q := 10#4) (by decide) (by decide), ?_⟩
  rw [e_succ_of_not_msb (by decide : (4#4).msb = false),
    e_succ_of_msb (by decide : (15#4).msb = true)]
  change mk (e R 3 ((4#4).setWidth 3) - 0) (0 - e R 3 ((15#4).setWidth 3)) ≠ 0
  rw [sub_zero]
  intro h
  exact e_ne_zero 3 _ (mk_inj.1 (h.trans (zero_eq_mk 3))).1

end Nonzero

section Norms

variable {R : Type u} [CommRing R] [StarRing R]

/-- The trace form of the bright product with itself is `8`. -/
theorem sedenion_bright_dot :
    dot 4 ((e R 4 1#4 + e R 4 10#4) * (e R 4 4#4 + e R 4 15#4))
      ((e R 4 1#4 + e R 4 10#4) * (e R 4 4#4 + e R 4 15#4)) = 8 := by
  rw [sedenion_bright_mul, two_smul]
  simp only [dot_add_left, dot_add_right, dot_sub_left, dot_sub_right, dot_e_e]
  simp
  norm_num

/-- The trace form of the fixture product with itself is `4`. -/
theorem sedenion_fixture_dot :
    dot 4 ((e R 4 1#4 + e R 4 10#4) * (e R 4 2#4 - e R 4 13#4))
      ((e R 4 1#4 + e R 4 10#4) * (e R 4 2#4 - e R 4 13#4)) = 4 := by
  rw [sedenion_fixture_mul]
  simp only [dot_add_left, dot_add_right, dot_sub_left, dot_sub_right, dot_e_e]
  simp
  norm_num

/-- The trace form of the dark product with itself is `0`. -/
theorem sedenion_dark_dot :
    dot 4 ((e R 4 1#4 + e R 4 10#4) * (e R 4 4#4 - e R 4 15#4))
      ((e R 4 1#4 + e R 4 10#4) * (e R 4 4#4 - e R 4 15#4)) = 0 := by
  rw [sedenion_dark_mul_eq_zero, dot_zero_left]

end Norms

section Selector

variable {K : Type u} [Field K] [StarRing K] [CharZero K]

/-- The squared norms of the dark, bright and fixture products divided by `8` are `0`, `1` and
`1/2`. -/
theorem sedenion_witness_selector_probabilities :
    dot 4 ((e K 4 1#4 + e K 4 10#4) * (e K 4 4#4 - e K 4 15#4))
        ((e K 4 1#4 + e K 4 10#4) * (e K 4 4#4 - e K 4 15#4)) / 8 = 0 ∧
    dot 4 ((e K 4 1#4 + e K 4 10#4) * (e K 4 4#4 + e K 4 15#4))
        ((e K 4 1#4 + e K 4 10#4) * (e K 4 4#4 + e K 4 15#4)) / 8 = 1 ∧
    dot 4 ((e K 4 1#4 + e K 4 10#4) * (e K 4 2#4 - e K 4 13#4))
        ((e K 4 1#4 + e K 4 10#4) * (e K 4 2#4 - e K 4 13#4)) / 8 = 1 / 2 := by
  rw [sedenion_dark_dot, sedenion_bright_dot, sedenion_fixture_dot]
  refine ⟨by simp, by norm_num, by norm_num⟩

end Selector

end Tower

end CayleyDickson
