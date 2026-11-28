/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Basic

/-!
# The doubling unit anticommutes with every doubly pure element

Convention: the product of `CayleyDickson A` is that of `GororobaMath.CayleyDickson.Basic`,
`(a, b) (c, d) = (a c - star d b, d a + b star c)`, with `star (a, b) = (star a, -b)`, over a
nonassociative ring `A` with a star that reverses products. The doubling unit is `h = (0, 1)`; an
element `(a, b)` is doubly pure when `star a = -a` and `star b = -b`, that is, when it is
orthogonal to `1` and to `h`.

For `z = (c, d)` the product `h z` is `(-star d, star c)`, so `h (h z) = -z` for every `z`. For
doubly pure `x = (a, b)` the two halves of `h (x z) + x (h z)` are
`-(star a + a) star d - c (star b + b)` and `star c (star a + a) - (star b + b) d`, both zero.
Left multiplication by `h` is therefore a complex structure that anticommutes with left
multiplication by every doubly pure element, and the kernel of the latter is invariant under it.
Only distributivity and the reversal `star (x y) = star y star x` enter, so the identities hold at
every level of the tower over every coefficient ring.

This is Biss, Dugger and Isaksen, Large annihilators in Cayley-Dickson algebras
(arXiv:math/0511691), Proposition 5.3 and Lemma 6.4, there over the reals: `A_n` is a vector space
over `<1, i_n>` by left multiplication, and `L_x` is conjugate-linear for `x` orthogonal to
`<1, i_n>`. Row A5-671 of the findings ledger of gororoba-quantum
(`docs/evidence/a5-exceptional-fibers/ledger.tsv`) checks the anticommutation on the basis of the
sedenions.

## Main results

* `CayleyDickson.doublingUnit_mul_doublingUnit_mul`: `h (h z) = -z`.
* `CayleyDickson.doublingUnit_mul_mul_add_mul_doublingUnit_mul`: for doubly pure `x`,
  `h (x z) + x (h z) = 0`.
* `CayleyDickson.mul_doublingUnit_mul_eq_zero`: for doubly pure `x`, `x z = 0` implies
  `x (h z) = 0`.
-/

@[expose] public section

namespace CayleyDickson

variable {A : Type*} [NonAssocRing A] [StarRing A]

/-- Left multiplication by the doubling unit squares to `-1`. -/
theorem doublingUnit_mul_doublingUnit_mul (z : CayleyDickson A) :
    (⟨0, 1⟩ : CayleyDickson A) * ((⟨0, 1⟩ : CayleyDickson A) * z) = -z := by
  ext <;> simp

/-- Left multiplication by the doubling unit anticommutes with left multiplication by a doubly
pure element. -/
theorem doublingUnit_mul_mul_add_mul_doublingUnit_mul (a b : A) (ha : star a = -a)
    (hb : star b = -b) (z : CayleyDickson A) :
    (⟨0, 1⟩ : CayleyDickson A) * ((⟨a, b⟩ : CayleyDickson A) * z) +
      (⟨a, b⟩ : CayleyDickson A) * ((⟨0, 1⟩ : CayleyDickson A) * z) = 0 := by
  ext <;> simp [star_sub, star_add, ha, hb] <;> abel

/-- The kernel of left multiplication by a doubly pure element is invariant under left
multiplication by the doubling unit. -/
theorem mul_doublingUnit_mul_eq_zero {a b : A} (ha : star a = -a) (hb : star b = -b)
    {z : CayleyDickson A} (hz : (⟨a, b⟩ : CayleyDickson A) * z = 0) :
    (⟨a, b⟩ : CayleyDickson A) * ((⟨0, 1⟩ : CayleyDickson A) * z) = 0 := by
  have h := doublingUnit_mul_mul_add_mul_doublingUnit_mul a b ha hb z
  rwa [hz, mul_zero, zero_add] at h

end CayleyDickson
