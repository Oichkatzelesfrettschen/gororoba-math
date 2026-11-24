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

* `Tower.orderThree_mul_succ`: `psi2 x * psi2 y = 2 psi2 (x * y)` at every level `k + 1` when
  `r3 * r3 = 3`; `Tower.orderThree_mul` is its instance on the sedenions.
* `Tower.orderThree_cube`: `psi2 (psi2 (psi2 x)) = 8 x`.
* `Tower.orderThree_reflect`: `2 ε (psi2 x) = psi2 (psi2 (ε x))` for the reflection
  `ε(A, B) = (A, -B)` (`Tower.reflectPair`).
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
/-- The local copy of `re_one` of `Kaplansky`; private, so the two modules import together. -/
private theorem re_one : ∀ k : ℕ, re k (1 : Tower R k) = 1
  | 0 => rfl
  | k + 1 => by
    rw [one_eq_mk, re_mk, re_one k]

omit [TrivialStar R] in
theorem re_neg (k : ℕ) (x : Tower R k) : re k (-x) = -re k x := by
  rw [← dot_one_right, ← dot_one_right, dot_neg_left]

omit [TrivialStar R] in
private theorem re_smul (k : ℕ) (r : R) (x : Tower R k) : re k (r • x) = r * re k x := by
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

omit [TrivialStar R] in
private theorem re_smul_one (k : ℕ) (a : R) : re k (a • (1 : Tower R k)) = a := by
  rw [re_smul, re_one, mul_one]

omit [TrivialStar R] in
/-- Every element of a level is a scalar multiple of `1` plus an element with zero real part. -/
theorem exists_imag {k : ℕ} (x : Tower R k) :
    ∃ (a : R) (ξ : Tower R k), re k ξ = 0 ∧ x = a • (1 : Tower R k) + ξ :=
  ⟨re k x, x - re k x • (1 : Tower R k), by rw [re_sub, re_smul_one, sub_self], by abel⟩

/-- The real part of a product with a second factor of zero real part is minus the dot product
of the factors. -/
theorem re_mul_of_re_eq_zero {k : ℕ} {ξ η : Tower R k} (hη : re k η = 0) :
    re k (ξ * η) = -dot k ξ η := by
  have h := re_mul_star ξ η
  rw [star_eq_neg_of_re_eq_zero hη, mul_neg, re_neg] at h
  linear_combination -h

/-- Two elements with zero real part anticommute up to the scalar `-2 dot`: the polarization of
`x * star x = dot x x • 1` of `mul_star_eq_dot`, valid at every level. -/
theorem mul_add_mul_comm_of_re_eq_zero {k : ℕ} {ξ η : Tower R k} (hξ : re k ξ = 0)
    (hη : re k η = 0) :
    ξ * η + η * ξ = (-(2 * dot k ξ η)) • (1 : Tower R k) := by
  have hs : re k (ξ + η) = 0 := by rw [re_add, hξ, hη, add_zero]
  have h1 := (mul_star_eq_dot k (ξ + η)).1
  have h2 := (mul_star_eq_dot k ξ).1
  have h3 := (mul_star_eq_dot k η).1
  rw [star_eq_neg_of_re_eq_zero hs] at h1
  rw [star_eq_neg_of_re_eq_zero hξ] at h2
  rw [star_eq_neg_of_re_eq_zero hη] at h3
  simp only [mul_add, add_mul, mul_neg, neg_add, dot_add_left, dot_add_right, add_smul] at h1 h2 h3
  rw [dot_comm k η ξ] at h1
  linear_combination (norm := module) -h1 + h2 + h3

/-- The doubled order-three map is multiplicative up to the factor `2` at every level `k + 1`
over every commutative ring with a square root of `3`: `psi2 x * psi2 y = 2 psi2 (x * y)`. Both
factors split into a scalar part and a part with zero real part in each half. The product
expands into products of the four imaginary parts, and the identity reduces to
`ξ η + η ξ = -2 dot ξ η` for pairs of them and `r3 * r3 = 3`. The Rocq original at level 4 is
`OrderThreeMap.psi2_mul` of `rocq/quantum/CdTowerOrderThreeMap.v`. -/
theorem orderThree_mul_succ (r3 : R) (h3 : r3 * r3 = 3) {k : ℕ} (x y : Tower R (k + 1)) :
    orderThree r3 x * orderThree r3 y = (2 : R) • orderThree r3 (x * y) := by
  obtain ⟨A, B⟩ := x
  obtain ⟨C, D⟩ := y
  obtain ⟨a, α, hα, rfl⟩ := exists_imag A
  obtain ⟨b, β, hβ, rfl⟩ := exists_imag B
  obtain ⟨c, γ, hγ, rfl⟩ := exists_imag C
  obtain ⟨d, δ, hδ, rfl⟩ := exists_imag D
  have hγ' := star_eq_neg_of_re_eq_zero hγ
  have hδ' := star_eq_neg_of_re_eq_zero hδ
  have rAC := re_mul_of_re_eq_zero (ξ := α) hγ
  have rDB := re_mul_of_re_eq_zero (ξ := δ) hβ
  have rDA := re_mul_of_re_eq_zero (ξ := δ) hα
  have rBC := re_mul_of_re_eq_zero (ξ := β) hγ
  have cAC := mul_add_mul_comm_of_re_eq_zero hα hγ
  have cDB := mul_add_mul_comm_of_re_eq_zero hδ hβ
  have cDA := mul_add_mul_comm_of_re_eq_zero hδ hα
  have cBC := mul_add_mul_comm_of_re_eq_zero hβ hγ
  change orderThree r3 (mk (a • 1 + α) (b • 1 + β)) * orderThree r3 (mk (c • 1 + γ) (d • 1 + δ)) =
    (2 : R) • orderThree r3 (mk (a • 1 + α) (b • 1 + β) * mk (c • 1 + γ) (d • 1 + δ))
  simp only [orderThree_mk, mk_mul_mk, smul_mk, mk_inj]
  simp only [re_add, re_sub, re_neg, re_smul, re_one, hα, hβ, hγ, hδ, rAC, rDB, rDA,
    rBC, star_add, star_sub, star_smul', star_one, hγ', hδ', mul_add, add_mul,
    mul_sub, sub_mul, mul_neg, neg_mul, smul_mul_assoc', mul_smul_comm', one_mul, mul_one,
    smul_add, smul_sub, smul_neg, smul_smul]
  refine ⟨?_, ?_⟩
  · linear_combination (norm := module) h3 • (β * δ + γ * α) + (3 : R) • cAC + (3 : R) • cDB
      - r3 • cDA + r3 • cBC
  · linear_combination (norm := module) h3 • (α * δ - γ * β) + r3 • cAC + r3 • cDB
      + (3 : R) • cDA - (3 : R) • cBC

/-- The doubled order-three map is multiplicative up to the factor `2` on the sedenions: the
level-4 instance of `orderThree_mul_succ`. The Rocq original is `OrderThreeMap.psi2_mul` of
`rocq/quantum/CdTowerOrderThreeMap.v`, which transports the 256 basis checks over `ℤ[√3]`. -/
theorem orderThree_mul (r3 : R) (h3 : r3 * r3 = 3) (x y : Tower R 4) :
    orderThree r3 x * orderThree r3 y = (2 : R) • orderThree r3 (x * y) :=
  orderThree_mul_succ r3 h3 x y

omit [TrivialStar R] in
/-- Three applications of the doubled order-three map scale by `8 = 2 ^ 3`: the map is `2` times
an automorphism of order `3`. -/
theorem orderThree_cube (r3 : R) (h3 : r3 * r3 = 3) {k : ℕ} (x : Tower R (k + 1)) :
    orderThree r3 (orderThree r3 (orderThree r3 x)) = (8 : R) • x := by
  obtain ⟨A, B⟩ := x
  obtain ⟨a, α, hα, rfl⟩ := exists_imag A
  obtain ⟨b, β, hβ, rfl⟩ := exists_imag B
  change orderThree r3 (orderThree r3 (orderThree r3 (mk (a • 1 + α) (b • 1 + β)))) =
    (8 : R) • mk (a • 1 + α) (b • 1 + β)
  simp only [orderThree_mk, smul_mk, mk_inj]
  simp only [re_add, re_sub, re_smul, re_one, hα, hβ, smul_add, smul_sub, smul_smul]
  refine ⟨?_, ?_⟩
  · linear_combination (norm := module) h3 • ((3 : R) • α - r3 • β)
  · linear_combination (norm := module) h3 • (r3 • α + (3 : R) • β)

/-- The reflection `(A, B) ↦ (A, -B)` of a double. -/
def reflectPair {k : ℕ} : Tower R (k + 1) → Tower R (k + 1)
  | ⟨A, B⟩ => mk A (-B)

omit [TrivialStar R] in
theorem reflectPair_mk {k : ℕ} (A B : Tower R k) : reflectPair (mk A B) = mk A (-B) := rfl

omit [TrivialStar R] in
/-- The reflection and the order-three map satisfy the relation `ε ψ = ψ² ε` of Brown's
generators in the scaled form `2 * ε (psi2 x) = psi2 (psi2 (ε x))`, where `psi2 = 2 ψ`. -/
theorem orderThree_reflect (r3 : R) (h3 : r3 * r3 = 3) {k : ℕ} (x : Tower R (k + 1)) :
    (2 : R) • reflectPair (orderThree r3 x) = orderThree r3 (orderThree r3 (reflectPair x)) := by
  obtain ⟨A, B⟩ := x
  obtain ⟨a, α, hα, rfl⟩ := exists_imag A
  obtain ⟨b, β, hβ, rfl⟩ := exists_imag B
  change (2 : R) • reflectPair (orderThree r3 (mk (a • 1 + α) (b • 1 + β))) =
    orderThree r3 (orderThree r3 (reflectPair (mk (a • 1 + α) (b • 1 + β))))
  simp only [orderThree_mk, reflectPair_mk, smul_mk, mk_inj]
  simp only [re_add, re_sub, re_neg, re_smul, re_one, hα, hβ, smul_add, smul_sub,
    smul_smul, smul_neg]
  refine ⟨?_, ?_⟩
  · linear_combination (norm := module) h3 • α
  · linear_combination (norm := module) (-1 : R) • h3 • β

end Tower

end CayleyDickson
