/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Basic

/-!
# The doubling unit anticommutes with every element of imaginary halves

Convention: the product of `CayleyDickson A` is that of `GororobaMath.CayleyDickson.Basic`,
`(a, b) (c, d) = (a c - star d b, d a + b star c)`, with `star (a, b) = (star a, -b)`, over a
nonassociative ring `A` with a star ring structure. `CayleyDickson.unit` is the doubling unit
`h = (0, 1)`. An element `(a, b)` has imaginary halves when `star a = -a` and `star b = -b`; over
the reals that is orthogonality to `1` and to `h`.

For `z = (c, d)` the product `h z` is `(-star d, star c)`, so `h (h z) = -z` for every `z`. For
`x = (a, b)` with imaginary halves the two halves of `h (x z) + x (h z)` are
`-(star a + a) star d - c (star b + b)` and `star c (star a + a) - (star b + b) d`, both zero.
Left multiplication by `h` therefore squares to `-1`, anticommutes with left multiplication by
`x`, and carries the kernel of the latter into itself. The proofs use distributivity, the unit
and zero laws, and the star laws of a star ring: additivity, `star (star u) = u` and
`star (u v) = star v star u`. No associativity enters, so the identities hold at every doubled
level `Tower R (k + 1)` over every coefficient ring.

With `i_n = h` these are, in Biss, Dugger and Isaksen, Large annihilators in Cayley-Dickson
algebras (arXiv:math/0511691), Lemma 5.2 (`i_n (i_n x) = -x`), the case `alpha = i_n` of
Lemma 5.7 (`alpha (x y) = x (alpha* y)`, restated as the conjugate-linearity of `L_x` in
Lemma 6.4) and the case `alpha = i_n` of Lemma 9.6 (`Ann x` is closed under `C_n`), there over
the reals and here over every star ring. `Tower.mk_mul_iota_mul` and `Tower.mul_cs_mul_eq_zero`
of `GororobaMath.CayleyDickson.ScaledPairAnnihilator` and `Tower.iota_mul_iota_mul` of
`GororobaMath.CayleyDickson.AnnihilatorBound` state the same identities on the tower over a field.
Row A5-671 of the findings ledger of gororoba-quantum
(`docs/evidence/a5-exceptional-fibers/ledger.tsv`) checks the anticommutation on the basis of the
sedenions.

## Main results

* `CayleyDickson.unit_mul_unit_mul`: `h (h z) = -z`.
* `CayleyDickson.unit_mul_mul_add_mul_unit_mul`: for `x` with imaginary halves,
  `h (x z) + x (h z) = 0`.
* `CayleyDickson.mul_unit_mul_eq_zero`: for `x` with imaginary halves, `x z = 0` implies
  `x (h z) = 0`.
-/

@[expose] public section

namespace CayleyDickson

variable {A : Type*} [NonAssocRing A] [StarRing A]

/-- Left multiplication by the doubling unit squares to `-1`. -/
theorem unit_mul_unit_mul (z : CayleyDickson A) : (unit : CayleyDickson A) * (unit * z) = -z := by
  ext <;> simp [unit]

/-- Left multiplication by the doubling unit anticommutes with left multiplication by an element of
imaginary halves. -/
theorem unit_mul_mul_add_mul_unit_mul (a b : A) (ha : star a = -a) (hb : star b = -b)
    (z : CayleyDickson A) :
    unit * ((⟨a, b⟩ : CayleyDickson A) * z) + (⟨a, b⟩ : CayleyDickson A) * (unit * z) = 0 := by
  ext
  · simp only [unit, add_re, mul_re, zero_mul, mul_im, star_add, star_mul, ha, neg_mul, star_star,
      hb, mul_neg, mul_one, zero_sub, neg_add_rev, neg_neg, mul_zero, one_mul, zero_add, zero_re]
    abel
  · simp only [unit, add_im, mul_im, mul_zero, mul_re, star_sub, star_mul, ha, mul_neg, hb,
      star_star, neg_mul, sub_neg_eq_add, one_mul, zero_add, zero_mul, mul_one, zero_sub, star_neg,
      zero_im]
    abel

/-- The kernel of left multiplication by an element of imaginary halves is invariant under left
multiplication by the doubling unit. -/
theorem mul_unit_mul_eq_zero {a b : A} (ha : star a = -a) (hb : star b = -b)
    {z : CayleyDickson A} (hz : (⟨a, b⟩ : CayleyDickson A) * z = 0) :
    (⟨a, b⟩ : CayleyDickson A) * (unit * z) = 0 := by
  have h := unit_mul_mul_add_mul_unit_mul a b ha hb z
  rwa [hz, mul_zero, zero_add] at h

end CayleyDickson
