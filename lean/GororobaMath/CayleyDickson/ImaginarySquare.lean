/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.FlexibleLaw
public import GororobaMath.CayleyDickson.AssociatorSpace

/-!
# The imaginary square law of the Cayley-Dickson tower

Convention: `Tower R k` is the `k`-fold Cayley-Dickson double of a commutative ring `R` with the
identity as star, the product is `Tower.mk_mul_mk`, and an element `x` is imaginary when
`star x = -x` (every element with `re k x = 0` is, by `Tower.star_eq_neg_of_re_eq_zero`).

For imaginary `x` and every `q`, `x * (x * q) = (q * x) * x`, so left and right multiplication
by `x` have the same square (Skiouris, "Algebraic hiddenness", 2026, Theorem 9.1). The proof
polarizes the flexible law `Tower.mul_mul_self_eq'` and uses that an imaginary `x` squares to a
scalar multiple of `1`, which commutes with every element. No level, characteristic or
regularity hypothesis enters.

## Main results

* `Tower.mul_mul_add_mul_mul_eq`: the polarized flexible law
  `(a * b) * c + (c * b) * a = a * (b * c) + c * (b * a)`.
* `Tower.mul_mul_eq_mul_mul_of_star_eq_neg`: `x * (x * q) = (q * x) * x` for imaginary `x`.
* `Tower.star_mul_mul_eq_mul_mul_star_of_star_eq_neg`: the same law in the form
  `star x * (x * q) = (q * x) * star x`.
* `Tower.mulLeft_comp_self_eq_mulRight_comp_self_of_star_eq_neg`: the squares of the linear maps
  `mulLeft R k x` and `mulRight R k x` agree.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [CommRing R] [StarRing R] [TrivialStar R] {k : ℕ}

/-- Applying the flexible law to `a + c` and `b` and subtracting its instances at `a` and at
`c` leaves the cross terms, which vanish. -/
theorem mul_mul_add_mul_mul_eq (a b c : Tower R k) :
    a * b * c + c * b * a = a * (b * c) + c * (b * a) := by
  have h := mul_mul_self_eq' (a + c) b
  have e : (a + c) * b * (a + c) - (a + c) * (b * (a + c)) - (a * b * a - a * (b * a)) -
      (c * b * c - c * (b * c)) = (a * b * c + c * b * a) - (a * (b * c) + c * (b * a)) := by
    noncomm_ring
  rw [h, mul_mul_self_eq' a b, mul_mul_self_eq' c b] at e
  simp only [sub_self] at e
  exact sub_eq_zero.1 e.symm

/-- An imaginary element squares to the scalar `-dot x x` times `1`, which commutes with every
element. -/
theorem mul_self_mul_eq_mul_mul_self_of_star_eq_neg {x : Tower R k} (hx : star x = -x)
    (q : Tower R k) : x * x * q = q * (x * x) := by
  have h := (mul_star_eq_dot k x).1
  rw [hx, mul_neg] at h
  have hsq : x * x = -(dot k x x • (1 : Tower R k)) := neg_eq_iff_eq_neg.1 h
  rw [hsq, neg_mul, mul_neg, smul_mul_assoc', mul_smul_comm', one_mul, mul_one]

/-- Imaginary `x` satisfies `x * (x * q) = (q * x) * x`: the polarized flexible law at
`(x, x, q)` and the centrality of `x * x`. -/
theorem mul_mul_eq_mul_mul_of_star_eq_neg {x : Tower R k} (hx : star x = -x) (q : Tower R k) :
    x * (x * q) = q * x * x := by
  have h := mul_mul_add_mul_mul_eq x x q
  rw [mul_self_mul_eq_mul_mul_self_of_star_eq_neg hx q] at h
  rw [add_comm (x * (x * q))] at h
  exact (add_left_cancel h).symm

/-- The form `star x * (x * q) = (q * x) * star x` of the imaginary square law. -/
theorem star_mul_mul_eq_mul_mul_star_of_star_eq_neg {x : Tower R k} (hx : star x = -x)
    (q : Tower R k) : star x * (x * q) = q * x * star x := by
  rw [hx, neg_mul, mul_neg, mul_mul_eq_mul_mul_of_star_eq_neg hx q]

/-- The squares of left and right multiplication by an imaginary element agree. -/
theorem mulLeft_comp_self_eq_mulRight_comp_self_of_star_eq_neg {x : Tower R k}
    (hx : star x = -x) :
    mulLeft R k x ∘ₗ mulLeft R k x = mulRight R k x ∘ₗ mulRight R k x :=
  LinearMap.ext fun q => by
    simp only [LinearMap.comp_apply, mulLeft_apply, mulRight_apply]
    exact mul_mul_eq_mul_mul_of_star_eq_neg hx q

end Tower

end CayleyDickson
