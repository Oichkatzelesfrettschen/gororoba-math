/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.BaseChange
public import GororobaMath.CayleyDickson.AnnihilatorSymmetry
public import GororobaMath.CayleyDickson.TraceForm

/-!
# The doubled order-three map of the sedenions

Convention: `Tower R k` is the `k`-fold Cayley-Dickson double of a commutative ring `R` with the
identity as star (`TrivialStar R`), with the product
`(a, b) (c, d) = (a c - star d b, d a + b star c)` of
`GororobaMath.CayleyDickson.Tower`; `Tower.re k x` is the coordinate of `1`
(`GororobaMath.CayleyDickson.AnnihilatorSymmetry`) and the imaginary part of `x` is
`x - re k x • 1`. For a root `r3` of `r3 * r3 = 3`, `Tower.orderThree r3` sends the pair
`(A, B)` of level `k + 1` to
`((3 re A) • 1 - A + r3 • im B, (3 re B) • 1 - B - r3 • im A)`: it fixes three times the real
parts and turns the pair of imaginary parts by a third of a turn, twice the map `psi` of
Eq. 61 of Gresnigt (arXiv 2609.10569).

## Main results

* `Tower.orderThree_mul`: `psi2 x * psi2 y = 2 psi2 (x * y)` on the sedenions when `r3 * r3 = 3`.
* `Tower.orderThree_star`: the map commutes with the star at every level, the Rocq
  `OrderThreeMap.psi2_conj` of `rocq/quantum/CdTowerOrderThreeMap.v`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

/-- Twice the order-three map:
`(A, B) ↦ ((3 re A) • 1 - A + r3 • im B, (3 re B) • 1 - B - r3 • im A)` with `im y = y - re y • 1`.
It is `OrderThreeMap.psi2` of `rocq/quantum/CdTowerOrderThreeMap.v`. -/
def orderThree (r3 : R) {k : ℕ} : Tower R (k + 1) → Tower R (k + 1)
  | ⟨A, B⟩ =>
    mk ((3 * re k A) • (1 : Tower R k) - A + r3 • B - (r3 * re k B) • (1 : Tower R k))
      ((3 * re k B) • (1 : Tower R k) - B - r3 • A + (r3 * re k A) • (1 : Tower R k))

omit [TrivialStar R] in
theorem orderThree_mk (r3 : R) {k : ℕ} (A B : Tower R k) :
    orderThree r3 (mk A B) =
      mk ((3 * re k A) • (1 : Tower R k) - A + r3 • B - (r3 * re k B) • (1 : Tower R k))
        ((3 * re k B) • (1 : Tower R k) - B - r3 • A + (r3 * re k A) • (1 : Tower R k)) := rfl

omit [TrivialStar R] in
theorem re_one : ∀ k : ℕ, re k (1 : Tower R k) = 1
  | 0 => rfl
  | k + 1 => by
    rw [one_eq_mk, re_mk, re_one k]

omit [TrivialStar R] in
theorem re_neg (k : ℕ) (x : Tower R k) : re k (-x) = -re k x := by
  rw [← dot_one_right, ← dot_one_right, dot_neg_left]

omit [TrivialStar R] in
theorem re_smul (k : ℕ) (r : R) (x : Tower R k) : re k (r • x) = r * re k x := by
  rw [← dot_one_right, ← dot_one_right, dot_smul_left]

theorem re_star (k : ℕ) (x : Tower R k) : re k (star x) = re k x := by
  have h := congrArg (re k) (star_add_self k x)
  rw [re_add, re_smul, re_one] at h
  linear_combination h

/-- The doubled order-three map commutes with the star at every level. The Rocq original is
`OrderThreeMap.psi2_conj` of `rocq/quantum/CdTowerOrderThreeMap.v`. -/
theorem orderThree_star (r3 : R) {k : ℕ} (x : Tower R (k + 1)) :
    orderThree r3 (star x) = star (orderThree r3 x) := by
  obtain ⟨A, B⟩ := x
  have hA : star A = (2 * re k A) • (1 : Tower R k) - A := eq_sub_of_add_eq (star_add_self k A)
  have hB : star B = (2 * re k B) • (1 : Tower R k) - B := eq_sub_of_add_eq (star_add_self k B)
  change orderThree r3 (mk (star A) (-B)) = star (orderThree r3 (mk A B))
  rw [orderThree_mk, orderThree_mk, star_mk]
  refine mk_inj.2 ⟨?_, ?_⟩
  · simp only [re_star, re_neg, star_sub, star_add, star_smul', star_one]
    simp only [hA, hB]
    module
  · simp only [re_star, re_neg]
    simp only [hA]
    module

/-! At level `0` the tower is the base ring: `base` is the identity, and the next theorems are its
compatibilities with the structure of the level, each true by definition. -/

omit [TrivialStar R] in
theorem base_add (a b : Tower R 0) : base (a + b) = base a + base b := rfl

omit [TrivialStar R] in
theorem base_sub (a b : Tower R 0) : base (a - b) = base a - base b := rfl

omit [TrivialStar R] in
theorem base_mul (a b : Tower R 0) : base (a * b) = base a * base b := rfl

omit [TrivialStar R] in
theorem base_neg (a : Tower R 0) : base (-a) = -base a := rfl

omit [TrivialStar R] in
theorem base_smul (r : R) (a : Tower R 0) : base (r • a) = r * base a := rfl

theorem base_star (a : Tower R 0) : base (star a) = base a := star_trivial (base a)

omit [TrivialStar R] in
theorem base_one : base (1 : Tower R 0) = 1 := rfl

omit [TrivialStar R] in
theorem base_zero : base (0 : Tower R 0) = 0 := rfl

omit [CommRing R] [StarRing R] [TrivialStar R] in
theorem re_level_zero (x : Tower R 0) : re 0 x = base x := rfl

omit [CommRing R] [StarRing R] [TrivialStar R] in
theorem base_ext {a b : Tower R 0} (h : base a = base b) : a = b := h

omit [CommRing R] [StarRing R] [TrivialStar R] in
theorem exists_mk {k : ℕ} (x : Tower R (k + 1)) : ∃ a b : Tower R k, x = mk a b :=
  ⟨CayleyDickson.re x, CayleyDickson.im x, rfl⟩

/-- The doubled order-three map is multiplicative up to the factor `2` on the sedenions over
every commutative ring with a square root of `3`: `psi2 x * psi2 y = 2 psi2 (x * y)`. The
proof splits both factors into their 16 coordinates and closes each of the 16 coordinate
identities by `grind` from `r3 * r3 = 3`. The Rocq original is `OrderThreeMap.psi2_mul` of
`rocq/quantum/CdTowerOrderThreeMap.v`, which transports the 256 basis checks over `ℤ[√3]`. -/
theorem orderThree_mul (r3 : R) (h3 : r3 * r3 = 3) (x y : Tower R 4) :
    orderThree r3 x * orderThree r3 y = (2 : R) • orderThree r3 (x * y) := by
  obtain ⟨x_0_3, x_8_3, rfl⟩ := exists_mk x
  obtain ⟨x_0_2, x_4_2, rfl⟩ := exists_mk x_0_3
  obtain ⟨x_0_1, x_2_1, rfl⟩ := exists_mk x_0_2
  obtain ⟨x0, x1, rfl⟩ := exists_mk x_0_1
  obtain ⟨x2, x3, rfl⟩ := exists_mk x_2_1
  obtain ⟨x_4_1, x_6_1, rfl⟩ := exists_mk x_4_2
  obtain ⟨x4, x5, rfl⟩ := exists_mk x_4_1
  obtain ⟨x6, x7, rfl⟩ := exists_mk x_6_1
  obtain ⟨x_8_2, x_12_2, rfl⟩ := exists_mk x_8_3
  obtain ⟨x_8_1, x_10_1, rfl⟩ := exists_mk x_8_2
  obtain ⟨x8, x9, rfl⟩ := exists_mk x_8_1
  obtain ⟨x10, x11, rfl⟩ := exists_mk x_10_1
  obtain ⟨x_12_1, x_14_1, rfl⟩ := exists_mk x_12_2
  obtain ⟨x12, x13, rfl⟩ := exists_mk x_12_1
  obtain ⟨x14, x15, rfl⟩ := exists_mk x_14_1
  obtain ⟨y_0_3, y_8_3, rfl⟩ := exists_mk y
  obtain ⟨y_0_2, y_4_2, rfl⟩ := exists_mk y_0_3
  obtain ⟨y_0_1, y_2_1, rfl⟩ := exists_mk y_0_2
  obtain ⟨y0, y1, rfl⟩ := exists_mk y_0_1
  obtain ⟨y2, y3, rfl⟩ := exists_mk y_2_1
  obtain ⟨y_4_1, y_6_1, rfl⟩ := exists_mk y_4_2
  obtain ⟨y4, y5, rfl⟩ := exists_mk y_4_1
  obtain ⟨y6, y7, rfl⟩ := exists_mk y_6_1
  obtain ⟨y_8_2, y_12_2, rfl⟩ := exists_mk y_8_3
  obtain ⟨y_8_1, y_10_1, rfl⟩ := exists_mk y_8_2
  obtain ⟨y8, y9, rfl⟩ := exists_mk y_8_1
  obtain ⟨y10, y11, rfl⟩ := exists_mk y_10_1
  obtain ⟨y_12_1, y_14_1, rfl⟩ := exists_mk y_12_2
  obtain ⟨y12, y13, rfl⟩ := exists_mk y_12_1
  obtain ⟨y14, y15, rfl⟩ := exists_mk y_14_1
  simp only [orderThree_mk, mk_mul_mk, star_mk, re_mk, smul_mk, add_mk, sub_eq_add_neg, neg_mk,
    one_eq_mk, zero_eq_mk, mk_inj, re_level_zero]
  repeat' constructor
  all_goals
    refine base_ext ?_
    simp only [base_add, base_mul, base_neg, base_smul, base_star, base_one, base_zero]
    grind

end Tower

end CayleyDickson
