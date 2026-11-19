/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Basic

/-!
# Scalar actions on a Cayley-Dickson double

Convention: `CayleyDickson A` is the double of `GororobaMath.CayleyDickson.Basic`, pairs
`(re, im)` with `(a, b) * (c, d) = (a * c - star d * b, d * a + b * star c)` and
`star (a, b) = (star a, -b)`. A scalar `r` of a commutative ring `S` with the identity as star
acts on each half (`CayleyDickson.instModule`).

When `A` is an `S`-module on which the product is bilinear (`IsScalarTower S A A`,
`SMulCommClass S A A`) and the star is semilinear (`StarModule S A`), the double has the same
three properties: scalars pass through the product on either side and through the star. The
tower `Tower.smul_mul_star` states the case `A = Tower R k` over `S = R`; here the statement
is for every star ring `A`, so it applies to any level of a tower built over `A`.

## Main results

* `CayleyDickson.smul_mul_assoc`: `(r • x) * y = r • (x * y)`, the Rocq `mul_scale_left` of
  `CDDouble` in `rocq/open/theories/CDDoubleFunctor.v` and of `GenericRingBase` in
  `rocq/open/theories/CDScalarExtension.v`.
* `CayleyDickson.mul_smul_comm`: `x * (r • y) = r • (x * y)`, `mul_scale_right` of both.
* `CayleyDickson.instStarModule`: `star (r • x) = r • star x`, `conj_scale` of both.
-/

@[expose] public section

namespace CayleyDickson

variable {A : Type*} [NonAssocRing A] [StarRing A]
  {S : Type*} [CommRing S] [StarRing S] [TrivialStar S] [Module S A] [IsScalarTower S A A]
  [SMulCommClass S A A] [StarModule S A]

omit [StarRing S] [TrivialStar S] [StarModule S A] in
/-- Scalars pass through the product of the double on the left. The Rocq originals are
`CDDouble.mul_scale_left` of `rocq/open/theories/CDDoubleFunctor.v` and
`GenericRingBase.mul_scale_left` of `rocq/open/theories/CDScalarExtension.v`. -/
theorem smul_mul_assoc (r : S) (x y : CayleyDickson A) : (r • x) * y = r • (x * y) := by
  ext <;> simp [_root_.smul_mul_assoc, _root_.mul_smul_comm, smul_sub, smul_add]

/-- Scalars pass through the product of the double on the right; the star of a scalar is the
scalar. The Rocq originals are `CDDouble.mul_scale_right` of
`rocq/open/theories/CDDoubleFunctor.v` and `GenericRingBase.mul_scale_right` of
`rocq/open/theories/CDScalarExtension.v`. -/
theorem mul_smul_comm (r : S) (x y : CayleyDickson A) : x * (r • y) = r • (x * y) := by
  ext <;> simp [_root_.smul_mul_assoc, _root_.mul_smul_comm, star_smul, smul_sub, smul_add]

/-- The star of the double is semilinear over `S`. The Rocq originals are
`CDDouble.conj_scale` of `rocq/open/theories/CDDoubleFunctor.v` and
`GenericRingBase.conj_scale` of `rocq/open/theories/CDScalarExtension.v`. -/
instance instStarModule : StarModule S (CayleyDickson A) where
  star_smul r x := by ext <;> simp [star_smul]

end CayleyDickson
