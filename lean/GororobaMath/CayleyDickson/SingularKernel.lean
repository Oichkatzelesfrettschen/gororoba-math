/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AlternativeIdentities
public import GororobaMath.CayleyDickson.DoublingCommutator
public import GororobaMath.CayleyDickson.Kaplansky
public import GororobaMath.CayleyDickson.TowerModule
public import GororobaMath.CayleyDickson.AssociatorSpace

/-!
# Annihilating vectors of a singular sedenion built from two octonions

Convention: the product of `Tower R k` is the Cayley-Dickson product
`(a, b) (c, d) = (a c - star d b, d a + b star c)` of `GororobaMath.CayleyDickson.Basic`
(`Tower.mk_mul_mk`), the associator is `associator a b c = (a * b) * c - a * (b * c)`, and
`Tower.dot`, `Tower.re` are the trace form and the coordinate of `1`. An element is pure
when `re k x = 0`, which gives `star x = -x`. The level results read over a commutative
ring `R` with the identity as star and use no division and no hypothesis on `2`.

For pure octonions `a`, `b` with `dot a b = 0` and `dot a a = ν = dot b b`, the sedenion
`z = mk a b` is annihilated on the left by `kvec a b ν y`, whose halves are `ν • x` and
`-((b * x) * a)` for the associator `x = associator a b y`. The mechanism: `x` is pure and
orthogonal to `1`, `a`, `b`, `a * b`, so it anticommutes with each of them, which turns
the two components of `z * kvec` into `ν • (a * x) - ((b * x) * a) * b` and
`-(((b * x) * a) * a) - ν • (b * x)`; the alternative laws of level 3 cancel both.

## Main results

* `Tower.kvec`: the vector `mk (ν • x) (-((b * x) * a))` of level 4.
* `Tower.re_kvec`: both halves of `kvec` have real part zero.
* `Tower.mk_mul_kvec`: `mk a b * kvec a b ν y = 0` for every `y`.
* `Tower.re_associator`, `Tower.dot_associator_left`, `Tower.dot_associator_mid`,
  `Tower.dot_associator_mul`: the associator `associator a b y` is orthogonal to
  `1`, `a`, `b`, `a * b`.
* `Tower.mul_comm_neg_of_dot_eq_zero`: orthogonal pure elements anticommute.
* `Tower.mul_mul_mul_eq_smul`: `((b * x) * a) * b = ν • (a * x)` for `x` pure and orthogonal
  to `a`, `b`, `a * b`.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R]

/-- A pure element squares to minus its norm. -/
theorem mul_self_eq_neg_smul_of_re_eq_zero {k : ℕ} {u : Tower R k} (h : re k u = 0) :
    u * u = -(dot k u u • (1 : Tower R k)) := by
  have h1 := (mul_star_eq_dot k u).1
  rw [star_eq_neg_of_re_eq_zero h, mul_neg] at h1
  exact neg_eq_iff_eq_neg.1 h1

/-- The polarization of `u * star u = dot u u • 1` for pure elements. -/
theorem mul_add_mul_rev_of_re_eq_zero {k : ℕ} {u v : Tower R k} (hu : re k u = 0)
    (hv : re k v = 0) :
    u * v + v * u = -((dot k u v + dot k u v) • (1 : Tower R k)) := by
  have h := (mul_star_eq_dot k (u + v)).1
  rw [star_add, mul_add, add_mul, add_mul, (mul_star_eq_dot k u).1, (mul_star_eq_dot k v).1,
    dot_add_left, dot_add_right, dot_add_right, dot_comm k v u, add_smul, add_smul, add_smul,
    star_eq_neg_of_re_eq_zero hu, star_eq_neg_of_re_eq_zero hv, mul_neg, mul_neg] at h
  have h' := sub_eq_zero.2 h.symm
  have e : u * v + v * u + (dot k u v • (1 : Tower R k) + dot k u v • (1 : Tower R k)) = 0 := by
    refine Eq.trans ?_ h'
    abel
  rw [add_smul]
  exact eq_neg_of_add_eq_zero_left e

/-- Orthogonal pure elements anticommute. -/
theorem mul_comm_neg_of_dot_eq_zero {k : ℕ} {u v : Tower R k} (hu : re k u = 0)
    (hv : re k v = 0) (h : dot k u v = 0) : u * v = -(v * u) := by
  have h1 := mul_add_mul_rev_of_re_eq_zero hu hv
  rw [h, add_zero, zero_smul, neg_zero] at h1
  exact eq_neg_of_add_eq_zero_left h1

/-- The coordinate of `1` of a product with a pure left factor is minus the trace form. -/
theorem re_mul_of_re_eq_zero {k : ℕ} {u : Tower R k} (hu : re k u = 0) (v : Tower R k) :
    re k (u * v) = -dot k u v := by
  rw [← dot_one_right, (dot_mul_adjoint k u v 1).1, mul_one, star_eq_neg_of_re_eq_zero hu,
    dot_neg_right, dot_comm k v u]

/-- The associator is orthogonal to `1`. -/
theorem re_associator (a b y : Tower R 3) : re 3 (associator a b y) = 0 := by
  have h := dot_associator_add_dot_associator_of_le_three (le_refl 3) a b y 1
  rw [associator_one_right, dot_zero_right, add_zero, dot_one_right] at h
  exact h

/-- The associator `associator a b y` is orthogonal to `a`. -/
theorem dot_associator_left (a b y : Tower R 3) : dot 3 (associator a b y) a = 0 := by
  have h := dot_associator_add_dot_associator_of_le_three (le_refl 3) a b y a
  have h0 : associator a b a = 0 := sub_eq_zero.2 (flexible_of_le_three (le_refl 3) a b)
  rw [h0, dot_zero_right, add_zero] at h
  exact h

/-- The associator `associator a b y` is orthogonal to `b`. -/
theorem dot_associator_mid (a b y : Tower R 3) : dot 3 (associator a b y) b = 0 := by
  have h := dot_associator_add_dot_associator_of_le_three (le_refl 3) a b y b
  rw [associator_self_right_of_le_three (le_refl 3), dot_zero_right, add_zero] at h
  exact h

/-- The associator `associator a b y` is orthogonal to `a * b`. -/
theorem dot_associator_mul (a b y : Tower R 3) : dot 3 (associator a b y) (a * b) = 0 := by
  unfold associator
  rw [dot_sub_left, dot_mul_self_left, dot_mul_mul_left_of_le_three (le_refl 3) a (b * y) b,
    dot_mul_self_left, dot_mul_mul_left_of_le_three (le_refl 3) a b b]
  ring

/-- The associator of `a`, `b` and `y` has star equal to its negation. -/
theorem star_associator_eq_neg (a b y : Tower R 3) : star (associator a b y) = -associator a b y :=
  star_eq_neg_of_re_eq_zero (re_associator a b y)

/-- For pure `a`, `b` with `dot a b = 0` and `x` pure and orthogonal to `a`, `b` and `a * b`:
`x` anticommutes with `a`, `b` and `a * b`, and the associator swap of the first two slots of
`(x, a, b)` gives `a * (b * x) = x * (a * b) = -((a * b) * x)`. -/
theorem mul_mul_eq_neg_mul_mul {a b x : Tower R 3} (ha : re 3 a = 0) (hb : re 3 b = 0)
    (hx : re 3 x = 0) (hab : dot 3 a b = 0) (hxa : dot 3 x a = 0) (hxb : dot 3 x b = 0)
    (hxab : dot 3 x (a * b) = 0) : a * (b * x) = -(a * b * x) := by
  have hax : a * x = -(x * a) :=
    mul_comm_neg_of_dot_eq_zero ha hx (by rw [dot_comm]; exact hxa)
  have hbx : b * x = -(x * b) :=
    mul_comm_neg_of_dot_eq_zero hb hx (by rw [dot_comm]; exact hxb)
  have hab0 : re 3 (a * b) = 0 := by rw [re_mul_of_re_eq_zero ha, hab, neg_zero]
  have hcx : a * b * x = -(x * (a * b)) :=
    mul_comm_neg_of_dot_eq_zero hab0 hx (by rw [dot_comm]; exact hxab)
  have hxb' : x * b = -(b * x) := by rw [hbx, neg_neg]
  have hF2 : a * (b * x) = x * (a * b) := by
    have hs := associator_add_swap_left_of_le_three (le_refl 3) x a b
    unfold associator at hs
    rw [hax, neg_mul, hxb', mul_neg] at hs
    refine eq_of_sub_eq_zero (Eq.trans ?_ hs)
    abel
  rw [hF2, hcx, neg_neg]

/-- For pure `a`, `b` with `dot a b = 0` and `dot b b = ν`, and `x` pure and orthogonal to
`a`, `b` and `a * b`: the associator swap of the last two slots of `(a * b, x, b)` gives
`((a * b) * x) * b = -(((a * b) * b) * x)`, and `(a * b) * b = -(ν • a)` by right
alternativity. -/
theorem mul_mul_mul_eq_smul {a b x : Tower R 3} {ν : R} (ha : re 3 a = 0) (hb : re 3 b = 0)
    (hx : re 3 x = 0) (hab : dot 3 a b = 0) (hxa : dot 3 x a = 0) (hxb : dot 3 x b = 0)
    (hxab : dot 3 x (a * b) = 0) (hbν : dot 3 b b = ν) :
    b * x * a * b = ν • (a * x) := by
  have hbx : b * x = -(x * b) :=
    mul_comm_neg_of_dot_eq_zero hb hx (by rw [dot_comm]; exact hxb)
  have hba : b * a = -(a * b) :=
    mul_comm_neg_of_dot_eq_zero hb ha (by rw [dot_comm]; exact hab)
  have hw0 : re 3 (b * x) = 0 := by
    rw [re_mul_of_re_eq_zero hb, dot_comm, hxb, neg_zero]
  have hwa : dot 3 (b * x) a = 0 := by
    rw [(dot_mul_adjoint 3 b x a).1, star_eq_neg_of_re_eq_zero hb, neg_mul, hba, neg_neg, hxab]
  have hwa' : b * x * a = -(a * (b * x)) := mul_comm_neg_of_dot_eq_zero hw0 ha hwa
  have hxb' : x * b = -(b * x) := by rw [hbx, neg_neg]
  have hwa2 : b * x * a = a * b * x := by
    rw [hwa', mul_mul_eq_neg_mul_mul ha hb hx hab hxa hxb hxab, neg_neg]
  have hs2 := associator_add_swap_right_of_le_three (le_refl 3) (a * b) x b
  unfold associator at hs2
  rw [hxb', mul_neg] at hs2
  have h3 : a * b * x * b + a * b * b * x = 0 := by
    refine Eq.trans ?_ hs2
    abel
  have hcb : a * b * b = -(ν • a) := by
    rw [right_alternative_of_le_three (le_refl 3), mul_self_eq_neg_smul_of_re_eq_zero hb, hbν,
      mul_neg, mul_smul_comm', mul_one]
  rw [hcb, neg_mul, smul_mul_assoc'] at h3
  rw [hwa2]
  exact add_neg_eq_zero.1 h3

/-- The vector of the annihilator of `mk a b` that the associator `x = associator a b y` gives:
`mk (ν • x) (-((b * x) * a))`. -/
def kvec (a b : Tower R 3) (ν : R) (y : Tower R 3) : Tower R 4 :=
  mk (ν • associator a b y) (-(b * associator a b y * a))

/-- The first half of `kvec` has real part zero. -/
theorem re_kvec_fst (a b : Tower R 3) (ν : R) (y : Tower R 3) :
    re 3 (ν • associator a b y) = 0 := by
  rw [← dot_one_right, dot_smul_left, dot_one_right, re_associator, mul_zero]

/-- The second half of `kvec` has real part zero. -/
theorem re_kvec_snd {a b : Tower R 3} (ha : re 3 a = 0) (hb : re 3 b = 0) (hab : dot 3 a b = 0)
    (y : Tower R 3) : re 3 (-(b * associator a b y * a)) = 0 := by
  have hx := re_associator a b y
  have hxb : dot 3 (associator a b y) b = 0 := dot_associator_mid a b y
  have hxab : dot 3 (associator a b y) (a * b) = 0 := dot_associator_mul a b y
  have hba : b * a = -(a * b) :=
    mul_comm_neg_of_dot_eq_zero hb ha (by rw [dot_comm]; exact hab)
  have hw0 : re 3 (b * associator a b y) = 0 := by
    rw [re_mul_of_re_eq_zero hb, dot_comm, hxb, neg_zero]
  have hwa : dot 3 (b * associator a b y) a = 0 := by
    rw [(dot_mul_adjoint 3 b _ a).1, star_eq_neg_of_re_eq_zero hb, neg_mul, hba, neg_neg, hxab]
  rw [← dot_one_right, dot_neg_left, dot_one_right, re_mul_of_re_eq_zero hw0, hwa, neg_zero,
    neg_zero]

/-- Both halves of `kvec` have real part zero, so `kvec` is pure. -/
theorem re_kvec {a b : Tower R 3} (ha : re 3 a = 0) (hb : re 3 b = 0) (hab : dot 3 a b = 0)
    (ν : R) (y : Tower R 3) :
    re 4 (kvec a b ν y) = 0 ∧ re 3 (ν • associator a b y) = 0 ∧
      re 3 (-(b * associator a b y * a)) = 0 :=
  ⟨re_kvec_fst a b ν y, re_kvec_fst a b ν y, re_kvec_snd ha hb hab y⟩

/-- The doubled pair `mk a b` annihilates `kvec a b ν y` on the left. -/
theorem mk_mul_kvec {a b : Tower R 3} {ν : R} (ha : re 3 a = 0) (hb : re 3 b = 0)
    (hab : dot 3 a b = 0) (haν : dot 3 a a = ν) (hbν : dot 3 b b = ν) (y : Tower R 3) :
    mk a b * kvec a b ν y = 0 := by
  have hx := re_associator a b y
  have hxa : dot 3 (associator a b y) a = 0 := dot_associator_left a b y
  have hxb : dot 3 (associator a b y) b = 0 := dot_associator_mid a b y
  have hxab : dot 3 (associator a b y) (a * b) = 0 := dot_associator_mul a b y
  have hcore := mul_mul_mul_eq_smul ha hb hx hab hxa hxb hxab hbν
  have hba : b * a = -(a * b) :=
    mul_comm_neg_of_dot_eq_zero hb ha (by rw [dot_comm]; exact hab)
  have hw0 : re 3 (b * associator a b y) = 0 := by
    rw [re_mul_of_re_eq_zero hb, dot_comm, hxb, neg_zero]
  have hwa : dot 3 (b * associator a b y) a = 0 := by
    rw [(dot_mul_adjoint 3 b _ a).1, star_eq_neg_of_re_eq_zero hb, neg_mul, hba, neg_neg, hxab]
  have hwa' : b * associator a b y * a = -(a * (b * associator a b y)) :=
    mul_comm_neg_of_dot_eq_zero hw0 ha hwa
  have hst : star (b * associator a b y * a) = -(b * associator a b y * a) := by
    rw [star_mul, star_eq_neg_of_re_eq_zero ha, star_eq_neg_of_re_eq_zero hw0, neg_mul_neg,
      hwa', neg_neg]
  unfold kvec
  rw [mk_mul_mk, zero_eq_mk, mk_inj]
  constructor
  · rw [star_neg, hst, neg_neg, hcore, mul_smul_comm', sub_self]
  · rw [star_smul', star_associator_eq_neg, neg_mul, right_alternative_of_le_three (le_refl 3),
      mul_self_eq_neg_smul_of_re_eq_zero ha, haν]
    simp only [mul_neg, smul_neg, mul_smul_comm', mul_one, neg_neg]
    abel

/-- The associator `associator a b y` as a linear map of `y`. -/
def assocMap (a b : Tower R 3) : Tower R 3 →ₗ[R] Tower R 3 :=
  mulLeft R 3 (a * b) - mulLeft R 3 a ∘ₗ mulLeft R 3 b

theorem assocMap_apply (a b y : Tower R 3) : assocMap a b y = associator a b y := rfl

/-- The trace form against a fixed element, as a linear map. -/
def dotLin (k : ℕ) (v : Tower R k) : Tower R k →ₗ[R] R where
  toFun y := dot k y v
  map_add' x y := dot_add_left k x y v
  map_smul' r x := by simp only [dot_smul_left, RingHom.id_apply, smul_eq_mul]

omit [TrivialStar R] in
theorem dotLin_apply (k : ℕ) (v y : Tower R k) : dotLin k v y = dot k y v := rfl

/-- The associator of `a`, `b` and `a * b` vanishes when `a`, `b` are pure and orthogonal. -/
theorem associator_mul_self {a b : Tower R 3} {ν : R} (ha : re 3 a = 0) (hb : re 3 b = 0)
    (hab : dot 3 a b = 0) (haν : dot 3 a a = ν) (hbν : dot 3 b b = ν) :
    associator a b (a * b) = 0 := by
  have hba : b * a = -(a * b) :=
    mul_comm_neg_of_dot_eq_zero hb ha (by rw [dot_comm]; exact hab)
  have hab0 : re 3 (a * b) = 0 := by rw [re_mul_of_re_eq_zero ha, hab, neg_zero]
  have hnn : dot 3 (a * b) (a * b) = ν ^ 2 := by
    rw [dot_mul_mul_left_of_le_three (le_refl 3), haν, hbν]; ring
  have h1 : b * (a * b) = ν • a := by
    have e : a * b = -(b * a) := by rw [hba, neg_neg]
    rw [e, mul_neg, left_alternative_of_le_three (le_refl 3), mul_self_eq_neg_smul_of_re_eq_zero hb,
      hbν, neg_mul, smul_mul_assoc', one_mul, neg_neg]
  unfold associator
  rw [h1, mul_smul_comm', mul_self_eq_neg_smul_of_re_eq_zero ha, haν,
    mul_self_eq_neg_smul_of_re_eq_zero hab0, hnn, smul_neg, smul_smul, sub_eq_zero, pow_two]

/-- The associator `associator a b y` for `y` orthogonal to `1`, `a`, `b` and `a * b` is
`2 • ((a * b) * y)`: the sign is positive under the product of the tower. -/
theorem associator_eq_two_smul_of_orth {a b y : Tower R 3} (ha : re 3 a = 0) (hb : re 3 b = 0)
    (hab : dot 3 a b = 0) (hy1 : dot 3 y 1 = 0) (hya : dot 3 y a = 0) (hyb : dot 3 y b = 0)
    (hyab : dot 3 y (a * b) = 0) : associator a b y = (2 : R) • (a * b * y) := by
  have hy : re 3 y = 0 := by rw [← dot_one_right]; exact hy1
  unfold associator
  rw [mul_mul_eq_neg_mul_mul ha hb hy hab hya hyb hyab, sub_neg_eq_add, two_smul]

section Dimension

variable {F : Type u} [Field F] [StarRing F] [TrivialStar F]

/-- The four generators `1, a, b, a * b` of the quaternion subalgebra of `a` and `b`. -/
def hbasis (a b : Tower F 3) : Fin 4 → Tower F 3 := ![1, a, b, a * b]

/-- The squared norms `1, ν, ν, ν ^ 2` of the four generators. -/
def hnorm (ν : F) : Fin 4 → F := ![1, ν, ν, ν ^ 2]

/-- The four generators are pairwise orthogonal with norms `1, ν, ν, ν ^ 2`. -/
theorem dot_hbasis {a b : Tower F 3} {ν : F} (ha : re 3 a = 0) (hb : re 3 b = 0)
    (hab : dot 3 a b = 0) (haν : dot 3 a a = ν) (hbν : dot 3 b b = ν) (i j : Fin 4) :
    dot 3 (hbasis a b i) (hbasis a b j) = if i = j then hnorm ν i else 0 := by
  have h11 : dot 3 (1 : Tower F 3) 1 = 1 := by rw [dot_one_right, re_one]
  have h1a : dot 3 (1 : Tower F 3) a = 0 := by rw [dot_comm, dot_one_right, ha]
  have h1b : dot 3 (1 : Tower F 3) b = 0 := by rw [dot_comm, dot_one_right, hb]
  have h1ab : dot 3 (1 : Tower F 3) (a * b) = 0 := by
    rw [dot_comm, dot_one_right, re_mul_of_re_eq_zero ha, hab, neg_zero]
  have hbab : dot 3 b (a * b) = 0 := by
    have h := dot_mul_mul_right_of_le_three (le_refl 3) 1 a b
    rw [one_mul, h1a, zero_mul] at h
    exact h
  have haab : dot 3 a (a * b) = 0 := by
    have h := dot_mul_mul_left_of_le_three (le_refl 3) a 1 b
    rw [mul_one, h1b, mul_zero] at h
    exact h
  have hnn : dot 3 (a * b) (a * b) = ν ^ 2 := by
    rw [dot_mul_mul_left_of_le_three (le_refl 3), haν, hbν]; ring
  have g1a := dot_comm 3 a 1
  have g1b := dot_comm 3 b 1
  have g1ab := dot_comm 3 (a * b) 1
  have gba := dot_comm 3 b a
  have gaab := dot_comm 3 (a * b) a
  have gbab := dot_comm 3 (a * b) b
  fin_cases i <;> fin_cases j <;>
    simp [hbasis, hnorm, h11, h1a, h1b, h1ab, hbab, haab, hnn, haν, hbν, hab, g1a, g1b, g1ab,
      gba, gaab, gbab]

omit [StarRing F] [TrivialStar F] in
theorem hnorm_ne_zero {ν : F} (hν : ν ≠ 0) (i : Fin 4) : hnorm ν i ≠ 0 := by
  fin_cases i <;> simp [hnorm, hν]

/-- The four generators `1, a, b, a * b` are linearly independent. -/
theorem linearIndependent_hbasis {a b : Tower F 3} {ν : F} (ha : re 3 a = 0) (hb : re 3 b = 0)
    (hab : dot 3 a b = 0) (haν : dot 3 a a = ν) (hbν : dot 3 b b = ν) (hν : ν ≠ 0) :
    LinearIndependent F (hbasis a b) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h := congrArg (fun w => dot 3 w (hbasis a b j)) hg
  simp only [Fin.sum_univ_four, dot_add_left, dot_smul_left, dot_zero_left,
    dot_hbasis ha hb hab haν hbν] at h
  have key : g j * hnorm ν j = 0 := by
    fin_cases j <;> simpa [hnorm] using h
  exact (mul_eq_zero.1 key).resolve_right (hnorm_ne_zero hν j)

/-- The span of `1, a, b, a * b`. -/
def hspan (a b : Tower F 3) : Submodule F (Tower F 3) := Submodule.span F (Set.range (hbasis a b))

/-- The span of `1, a, b, a * b` has dimension 4. -/
theorem finrank_hspan {a b : Tower F 3} {ν : F} (ha : re 3 a = 0) (hb : re 3 b = 0)
    (hab : dot 3 a b = 0) (haν : dot 3 a a = ν) (hbν : dot 3 b b = ν) (hν : ν ≠ 0) :
    Module.finrank F (hspan a b) = 4 := by
  rw [hspan, finrank_span_eq_card (linearIndependent_hbasis ha hb hab haν hbν hν)]
  simp

/-- The orthogonal complement of the span of `1, a, b, a * b`. -/
def hperp (a b : Tower F 3) : Submodule F (Tower F 3) :=
  LinearMap.ker (LinearMap.pi fun i => dotLin 3 (hbasis a b i))

omit [TrivialStar F] in
theorem mem_hperp {a b y : Tower F 3} :
    y ∈ hperp a b ↔ ∀ i, dot 3 y (hbasis a b i) = 0 := by
  simp [hperp, LinearMap.mem_ker, funext_iff, dotLin_apply]

theorem hperp_surjective {a b : Tower F 3} {ν : F} (ha : re 3 a = 0) (hb : re 3 b = 0)
    (hab : dot 3 a b = 0) (haν : dot 3 a a = ν) (hbν : dot 3 b b = ν) (hν : ν ≠ 0) :
    Function.Surjective (LinearMap.pi fun i => dotLin 3 (hbasis a b i)) := by
  intro t
  refine ⟨∑ i, (t i / hnorm ν i) • hbasis a b i, ?_⟩
  funext j
  simp only [LinearMap.pi_apply, dotLin_apply, Fin.sum_univ_four, dot_add_left, dot_smul_left,
    dot_hbasis ha hb hab haν hbν]
  fin_cases j <;> simp [hnorm, hν]

/-- The orthogonal complement of `1, a, b, a * b` in the octonions has dimension 4. -/
theorem finrank_hperp {a b : Tower F 3} {ν : F} (ha : re 3 a = 0) (hb : re 3 b = 0)
    (hab : dot 3 a b = 0) (haν : dot 3 a a = ν) (hbν : dot 3 b b = ν) (hν : ν ≠ 0) :
    Module.finrank F (hperp a b) = 4 := by
  have h := LinearMap.finrank_range_add_finrank_ker (LinearMap.pi fun i => dotLin 3 (hbasis a b i))
  rw [LinearMap.range_eq_top.2 (hperp_surjective ha hb hab haν hbν hν), finrank_top,
    Module.finrank_fin_fun, finrank_eq F 3] at h
  change 4 + Module.finrank F (hperp a b) = 2 ^ 3 at h
  omega

/-- The associator map vanishes on `1, a, b, a * b`. -/
theorem assocMap_hbasis {a b : Tower F 3} {ν : F} (ha : re 3 a = 0) (hb : re 3 b = 0)
    (hab : dot 3 a b = 0) (haν : dot 3 a a = ν) (hbν : dot 3 b b = ν) (i : Fin 4) :
    assocMap a b (hbasis a b i) = 0 := by
  rw [assocMap_apply]
  fin_cases i
  · exact associator_one_right a b
  · exact sub_eq_zero.2 (flexible_of_le_three (le_refl 3) a b)
  · exact associator_self_right_of_le_three (le_refl 3) a b
  · exact associator_mul_self ha hb hab haν hbν

/-- The associator map vanishes on the span of `1, a, b, a * b`. -/
theorem hspan_le_ker {a b : Tower F 3} {ν : F} (ha : re 3 a = 0) (hb : re 3 b = 0)
    (hab : dot 3 a b = 0) (haν : dot 3 a a = ν) (hbν : dot 3 b b = ν) :
    hspan a b ≤ LinearMap.ker (assocMap a b) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  exact assocMap_hbasis ha hb hab haν hbν i

/-- The range of the associator map lies in the orthogonal complement of `1, a, b, a * b`. -/
theorem range_assocMap_le_hperp (a b : Tower F 3) :
    LinearMap.range (assocMap a b) ≤ hperp a b := by
  rintro _ ⟨y, rfl⟩
  rw [mem_hperp]
  intro i
  rw [assocMap_apply]
  fin_cases i
  · change dot 3 (associator a b y) 1 = 0
    rw [dot_one_right]; exact re_associator a b y
  · exact dot_associator_left a b y
  · exact dot_associator_mid a b y
  · exact dot_associator_mul a b y

/-- The associator map is injective on the orthogonal complement of `1, a, b, a * b`, where it
is `2 • ((a * b) * y)`; this needs `2 ≠ 0` and `ν ≠ 0`. -/
theorem assocMap_injective_hperp {a b : Tower F 3} {ν : F} (h2 : (2 : F) ≠ 0) (ha : re 3 a = 0)
    (hb : re 3 b = 0) (hab : dot 3 a b = 0) (haν : dot 3 a a = ν) (hbν : dot 3 b b = ν)
    (hν : ν ≠ 0) : Function.Injective ((assocMap a b).domRestrict (hperp a b)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  have hm := mem_hperp.1 y.2
  have hy1 : dot 3 y.1 1 = 0 := hm 0
  have hya : dot 3 y.1 a = 0 := hm 1
  have hyb : dot 3 y.1 b = 0 := hm 2
  have hyab : dot 3 y.1 (a * b) = 0 := hm 3
  have hz : associator a b y.1 = 0 := hy
  rw [associator_eq_two_smul_of_orth ha hb hab hy1 hya hyb hyab] at hz
  have hz2 : a * b * y.1 = 0 := (smul_eq_zero.1 hz).resolve_left h2
  have hnn : dot 3 (a * b) (a * b) = ν ^ 2 := by
    rw [dot_mul_mul_left_of_le_three (le_refl 3), haν, hbν]; ring
  have h3 : ν ^ 2 • y.1 = 0 := by
    rw [← hnn, ← star_mul_mul_of_le_three (le_refl 3) (a * b) y.1, hz2, mul_zero]
  exact Subtype.ext ((smul_eq_zero.1 h3).resolve_left (pow_ne_zero 2 hν))

/-- The range of the associator map has dimension 4. -/
theorem finrank_range_assocMap {a b : Tower F 3} {ν : F} (h2 : (2 : F) ≠ 0) (ha : re 3 a = 0)
    (hb : re 3 b = 0) (hab : dot 3 a b = 0) (haν : dot 3 a a = ν) (hbν : dot 3 b b = ν)
    (hν : ν ≠ 0) : Module.finrank F (LinearMap.range (assocMap a b)) = 4 := by
  apply le_antisymm
  · exact (Submodule.finrank_mono (range_assocMap_le_hperp a b)).trans
      (finrank_hperp ha hb hab haν hbν hν).le
  · have hinj := assocMap_injective_hperp h2 ha hb hab haν hbν hν
    have h := LinearMap.finrank_range_of_inj hinj
    rw [finrank_hperp ha hb hab haν hbν hν] at h
    rw [← h]
    exact Submodule.finrank_mono (LinearMap.range_domRestrict_le_range _ _)

/-- The range of the associator map is the orthogonal complement of `1, a, b, a * b`. -/
theorem range_assocMap_eq_hperp {a b : Tower F 3} {ν : F} (h2 : (2 : F) ≠ 0) (ha : re 3 a = 0)
    (hb : re 3 b = 0) (hab : dot 3 a b = 0) (haν : dot 3 a a = ν) (hbν : dot 3 b b = ν)
    (hν : ν ≠ 0) : LinearMap.range (assocMap a b) = hperp a b :=
  Submodule.eq_of_le_of_finrank_eq (range_assocMap_le_hperp a b)
    ((finrank_range_assocMap h2 ha hb hab haν hbν hν).trans
      (finrank_hperp ha hb hab haν hbν hν).symm)

end Dimension

end Tower

end CayleyDickson
