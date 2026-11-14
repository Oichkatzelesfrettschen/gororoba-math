/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib

/-!
# The Cayley-Dickson double of a star ring

`CayleyDickson A` is the set of pairs `(re, im)` over a ring `A` with a star
operation, under the product

  `(a, b) * (c, d) = (a * c - star d * b, d * a + b * star c)`

and the conjugation `star (a, b) = (star a, -b)`. The product is the one of
gororoba-quantum `gororoba_quantum/cd_core.py` (`cd_sign`) and of the Rocq
tower `CdTowerRing.v` of gororoba-quantum (`RingTower.mul`), so a statement
proved here reads on the same basis signs as both.

`A` is a `NonAssocRing`: the double of an associative ring is associative
only when `A` is commutative, and the double of the octonions is not
alternative, so no instance here assumes associativity of `A`. The star of
`A` is an additive involution with `star (x * y) = star y * star x`
(`StarRing`), and the double is again a `NonAssocRing` with a `StarRing`
structure, which is what lets the construction iterate
(`GororobaMath.CayleyDickson.Tower`).

## Main results

* `CayleyDickson.instNonAssocRing`, `CayleyDickson.instStarRing`: the double
  of a nonassociative star ring is a nonassociative star ring.
* `CayleyDickson.mul_star_self`: `x * star x = (re * star re + star im * im, 0)`.
* `CayleyDickson.reflect`: `(a, b) ↦ (a, -b)` preserves products, sums, `1`
  and `star`.
* `CayleyDickson.inl`: `a ↦ (a, 0)` preserves products, sums, `1` and `star`
  and is injective.
* `CayleyDickson.instModule`, `CayleyDickson.linearEquivProd`: an
  `R`-module structure on `A` acts on each half, and the double is then the
  product `A × A` as an `R`-module.
-/

@[expose] public section

/-- The Cayley-Dickson double of `A`: pairs `(re, im)`. -/
@[ext]
structure CayleyDickson (A : Type*) where
  /-- The first half, the copy of `A` that contains `1`. -/
  re : A
  /-- The second half, the multiples of the new imaginary unit. -/
  im : A

namespace CayleyDickson

variable {A : Type*}

instance [DecidableEq A] : DecidableEq (CayleyDickson A) := fun x y =>
  decidable_of_iff (x.re = y.re ∧ x.im = y.im) CayleyDickson.ext_iff.symm

section Additive

variable [NonAssocRing A]

instance : Zero (CayleyDickson A) := ⟨⟨0, 0⟩⟩
instance : One (CayleyDickson A) := ⟨⟨1, 0⟩⟩
instance : Add (CayleyDickson A) := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg (CayleyDickson A) := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Sub (CayleyDickson A) := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩

@[simp] theorem zero_re : (0 : CayleyDickson A).re = 0 := rfl
@[simp] theorem zero_im : (0 : CayleyDickson A).im = 0 := rfl
@[simp] theorem one_re : (1 : CayleyDickson A).re = 1 := rfl
@[simp] theorem one_im : (1 : CayleyDickson A).im = 0 := rfl
@[simp] theorem add_re (x y : CayleyDickson A) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : CayleyDickson A) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : CayleyDickson A) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : CayleyDickson A) : (-x).im = -x.im := rfl
@[simp] theorem sub_re (x y : CayleyDickson A) : (x - y).re = x.re - y.re := rfl
@[simp] theorem sub_im (x y : CayleyDickson A) : (x - y).im = x.im - y.im := rfl

/-- Natural and integer multiples act on each half, so the `ℕ`- and
`ℤ`-actions of the group are the componentwise ones and agree with every
componentwise module structure built over them. -/
instance : AddCommGroup (CayleyDickson A) where
  add_assoc x y z := by ext <;> simp [add_assoc]
  zero_add x := by ext <;> simp
  add_zero x := by ext <;> simp
  add_comm x y := by ext <;> simp [add_comm]
  neg_add_cancel x := by ext <;> simp
  sub_eq_add_neg x y := by ext <;> simp [sub_eq_add_neg]
  nsmul n x := ⟨n • x.re, n • x.im⟩
  nsmul_zero x := by ext <;> exact AddMonoid.nsmul_zero _
  nsmul_succ n x := by ext <;> exact AddMonoid.nsmul_succ n _
  zsmul n x := ⟨n • x.re, n • x.im⟩
  zsmul_zero' x := by ext <;> exact SubNegMonoid.zsmul_zero' _
  zsmul_succ' n x := by ext <;> exact SubNegMonoid.zsmul_succ' n _
  zsmul_neg' n x := by ext <;> exact SubNegMonoid.zsmul_neg' n _

@[simp] theorem nsmul_re (n : ℕ) (x : CayleyDickson A) : (n • x).re = n • x.re := rfl
@[simp] theorem nsmul_im (n : ℕ) (x : CayleyDickson A) : (n • x).im = n • x.im := rfl
@[simp] theorem zsmul_re (n : ℤ) (x : CayleyDickson A) : (n • x).re = n • x.re := rfl
@[simp] theorem zsmul_im (n : ℤ) (x : CayleyDickson A) : (n • x).im = n • x.im := rfl

/-- The reflection `(a, b) ↦ (a, -b)` of the second half. -/
def reflect (x : CayleyDickson A) : CayleyDickson A := ⟨x.re, -x.im⟩

@[simp] theorem reflect_re (x : CayleyDickson A) : (reflect x).re = x.re := rfl
@[simp] theorem reflect_im (x : CayleyDickson A) : (reflect x).im = -x.im := rfl

@[simp] theorem reflect_reflect (x : CayleyDickson A) : reflect (reflect x) = x := by
  ext <;> simp

@[simp] theorem reflect_one : reflect (1 : CayleyDickson A) = 1 := by ext <;> simp

theorem reflect_add (x y : CayleyDickson A) :
    reflect (x + y) = reflect x + reflect y := by
  ext <;> simp [add_comm]

/-- The embedding `a ↦ (a, 0)` of `A` as the first half. -/
def inl (a : A) : CayleyDickson A := ⟨a, 0⟩

@[simp] theorem inl_re (a : A) : (inl a).re = a := rfl
@[simp] theorem inl_im (a : A) : (inl a).im = 0 := rfl
@[simp] theorem inl_one : inl (1 : A) = 1 := rfl
@[simp] theorem inl_zero : inl (0 : A) = 0 := rfl

theorem inl_add (a b : A) : inl (a + b) = inl a + inl b := by ext <;> simp

theorem inl_injective : Function.Injective (inl : A → CayleyDickson A) :=
  fun _ _ h => congrArg CayleyDickson.re h

end Additive

section Module

variable [NonAssocRing A] {R : Type*} [Semiring R] [Module R A]

/-- A scalar acts on each half. At `R = ℕ` and `R = ℤ` this is the action of
the group structure, since `nsmul` and `zsmul` act on each half too. -/
instance : SMul R (CayleyDickson A) := ⟨fun r x => ⟨r • x.re, r • x.im⟩⟩

@[simp] theorem smul_re (r : R) (x : CayleyDickson A) : (r • x).re = r • x.re := rfl
@[simp] theorem smul_im (r : R) (x : CayleyDickson A) : (r • x).im = r • x.im := rfl

/-- The double of an `R`-module is an `R`-module, componentwise. -/
instance instModule : Module R (CayleyDickson A) where
  one_smul x := by ext <;> simp
  mul_smul r s x := by ext <;> simp [mul_smul]
  smul_zero r := by ext <;> simp
  smul_add r x y := by ext <;> simp
  add_smul r s x := by ext <;> simp [add_smul]
  zero_smul x := by ext <;> simp

variable (A R) in
/-- The double is the product of its two halves as an `R`-module. -/
def linearEquivProd : CayleyDickson A ≃ₗ[R] A × A where
  toFun x := (x.re, x.im)
  invFun p := ⟨p.1, p.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem linearEquivProd_apply (x : CayleyDickson A) :
    linearEquivProd A R x = (x.re, x.im) := rfl

@[simp] theorem linearEquivProd_symm_apply (p : A × A) :
    (linearEquivProd A R).symm p = ⟨p.1, p.2⟩ := rfl

end Module

section Ring

variable [NonAssocRing A] [StarRing A]

instance : Mul (CayleyDickson A) :=
  ⟨fun x y => ⟨x.re * y.re - star y.im * x.im, y.im * x.re + x.im * star y.re⟩⟩

instance : Star (CayleyDickson A) := ⟨fun x => ⟨star x.re, -x.im⟩⟩

@[simp] theorem mul_re (x y : CayleyDickson A) :
    (x * y).re = x.re * y.re - star y.im * x.im := rfl

@[simp] theorem mul_im (x y : CayleyDickson A) :
    (x * y).im = y.im * x.re + x.im * star y.re := rfl

@[simp] theorem star_re (x : CayleyDickson A) : (star x).re = star x.re := rfl
@[simp] theorem star_im (x : CayleyDickson A) : (star x).im = -x.im := rfl

/-- The double of a nonassociative ring with a star is a nonassociative
ring. Distributivity, `0` and `1` need only the additivity of `star` and
`star 1 = 1`. -/
instance instNonAssocRing : NonAssocRing (CayleyDickson A) where
  left_distrib x y z := by
    ext <;> simp [mul_add, add_mul, star_add] <;> abel
  right_distrib x y z := by
    ext <;> simp [mul_add, add_mul] <;> abel
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp

/-- Conjugation reverses products at the doubled level because it does at
the level below; no associativity enters. -/
instance instStarRing : StarRing (CayleyDickson A) where
  star_involutive x := by ext <;> simp
  star_mul x y := by
    ext <;> simp [star_sub, star_mul]
  star_add x y := by
    ext
    · simp [star_add]
    · simp [add_comm]

/-- `x * star x` lies in the first half. -/
theorem mul_star_self (x : CayleyDickson A) :
    x * star x = ⟨x.re * star x.re + star x.im * x.im, 0⟩ := by
  ext <;> simp

/-- `star x * x` lies in the first half. -/
theorem star_mul_self (x : CayleyDickson A) :
    star x * x = ⟨star x.re * x.re + star x.im * x.im, 0⟩ := by
  ext <;> simp

/-- The reflection preserves products. With `reflect_add`, `reflect_one`,
`reflect_star` and `reflect_reflect` it is an involution that preserves the
ring and star operations, so it carries the kernel of left multiplication by
`x` onto the kernel of left multiplication by `reflect x`. -/
theorem reflect_mul (x y : CayleyDickson A) :
    reflect (x * y) = reflect x * reflect y := by
  ext <;> simp [add_comm]

theorem reflect_star (x : CayleyDickson A) : reflect (star x) = star (reflect x) := by
  ext <;> simp

theorem inl_mul (a b : A) : inl (a * b) = inl a * inl b := by ext <;> simp
theorem inl_star (a : A) : inl (star a) = star (inl a) := by ext <;> simp

/-- The new imaginary unit `(0, 1)`. -/
def unit : CayleyDickson A := ⟨0, 1⟩

/-- The new unit squares to `-1`. -/
theorem unit_mul_unit : (unit : CayleyDickson A) * unit = -1 := by
  ext <;> simp [unit]

/-- The new unit is conjugated to its negative. -/
theorem star_unit : star (unit : CayleyDickson A) = -unit := by
  ext <;> simp [unit]

end Ring

section Comm

variable [CommRing A] [StarRing A] [TrivialStar A]

/-- Over a commutative ring with the identity as star, the first double is
commutative: the complex numbers over the reals, the Gaussian integers over
the integers. The second double is the first level where `x * y = 0` and
`y * x = 0` can differ. -/
theorem mul_comm_of_trivialStar (x y : CayleyDickson A) : x * y = y * x := by
  ext <;> simp <;> ring

end Comm

end CayleyDickson
