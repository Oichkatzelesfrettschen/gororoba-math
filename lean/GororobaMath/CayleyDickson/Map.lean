/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.NonAssociative

/-!
# Maps of a Cayley-Dickson double

Convention: `CayleyDickson A` is the double of `GororobaMath.CayleyDickson.Basic`,
pairs `(re, im)` with the product `(a, b) * (c, d) = (a * c - star d * b, d * a + b * star c)`
and the star `star (a, b) = (star a, -b)`. `CayleyDickson.map f` applies `f` to both
halves, `(a, b) ↦ (f a, f b)`.

A non-unital ring homomorphism `f : A →ₙ+* B` between two star rings that commutes
with the star extends to the doubles: `CayleyDickson.map f` again preserves sums,
products and the star, and it preserves `1` when `f` does. Since the extension
has the hypotheses it needs, it extends again, to every level of a tower built
over `A` and `B`.

## Main results

* `CayleyDickson.map_mul`: `map f (x * y) = map f x * map f y`.
* `CayleyDickson.map_star`, `CayleyDickson.map_add`, `CayleyDickson.map_one`.
* `CayleyDickson.mapHom`: the extension as a non-unital ring homomorphism.

The Rocq original is `diag_mul` of the section `Diagonal` of the functor
`RingTower` in `rocq/quantum/CdTowerRing.v`, with `diag_add`, `diag_scale`,
`diag_conj` and `diag_one` beside it. There `f` maps one level of a tower over
a commutative ring `D` to itself, and preserves sums, the scalars of `D`,
products and conjugates. Here `f` maps between two star rings, neither
commutative nor associative; additivity makes it `ℤ`-linear, and a map
`D`-linear for scalars acting on both halves is `D`-linear on the double
(`CayleyDickson.map_smul`).

`Tower.lift j k` is the iterated embedding `x ↦ (x, 0)` of level `j` into level `j + k`,
with `lift j 0 = id` and `lift j (k + 1) x = mk (lift j k x) 0`. It preserves products
(`Tower.lift_mul`) and is injective (`Tower.lift_injective`); the Rocq original is
`lift_mul` and `lift_injective` of the functor `RingTower` in `rocq/quantum/CdTowerRing.v`,
whose `lift j k` lands in `cd (k + j)`, while here the target is `Tower R (j + k)`, so that
`j + (k + 1)` unfolds to `(j + k) + 1` by `rfl`.
-/

@[expose] public section

namespace CayleyDickson

variable {A B : Type*}

/-- `f` applied to both halves: `(a, b) ↦ (f a, f b)`. -/
def map (f : A → B) (x : CayleyDickson A) : CayleyDickson B := ⟨f x.re, f x.im⟩

@[simp] theorem map_re (f : A → B) (x : CayleyDickson A) : (map f x).re = f x.re := rfl
@[simp] theorem map_im (f : A → B) (x : CayleyDickson A) : (map f x).im = f x.im := rfl

section Additive

variable [NonAssocRing A] [NonAssocRing B]

/-- The extension of an additive map is additive. -/
protected theorem map_add (f : A →+ B) (x y : CayleyDickson A) :
    map f (x + y) = map f x + map f y := by
  ext <;> simp

/-- A map linear over scalars `S` extends to a map linear over `S`. -/
protected theorem map_smul {S : Type*} [Semiring S] [Module S A] [Module S B]
    (f : A →ₗ[S] B) (r : S) (x : CayleyDickson A) : map f (r • x) = r • map f x := by
  ext <;> simp

/-- The extension of a map that preserves `1` and `0` preserves `1`. -/
protected theorem map_one (f : A → B) (h1 : f 1 = 1) (h0 : f 0 = 0) :
    map f (1 : CayleyDickson A) = 1 := by
  ext <;> simp [h1, h0]

end Additive

section Ring

variable [NonAssocRing A] [StarRing A] [NonAssocRing B] [StarRing B]

/-- A non-unital ring homomorphism that commutes with the star extends to a
map of the doubles that preserves products. -/
protected theorem map_mul (f : A →ₙ+* B) (hf : ∀ x, f (star x) = star (f x))
    (x y : CayleyDickson A) : map f (x * y) = map f x * map f y := by
  ext <;> simp [hf]

/-- The extension commutes with the star. -/
protected theorem map_star (f : A → B) (hf : ∀ x, f (star x) = star (f x))
    (hneg : ∀ x, f (-x) = -f x) (x : CayleyDickson A) : map f (star x) = star (map f x) := by
  ext <;> simp [hf, hneg]

/-- The extension of a star-preserving non-unital ring homomorphism, bundled, so
that it extends again. -/
def mapHom (f : A →ₙ+* B) (hf : ∀ x, f (star x) = star (f x)) :
    CayleyDickson A →ₙ+* CayleyDickson B where
  toFun := map f
  map_mul' := CayleyDickson.map_mul f hf
  map_zero' := by ext <;> simp
  map_add' := CayleyDickson.map_add f.toAddMonoidHom

@[simp] theorem mapHom_apply (f : A →ₙ+* B) (hf : ∀ x, f (star x) = star (f x))
    (x : CayleyDickson A) : mapHom f hf x = map f x := rfl

/-- The bundled extension commutes with the star, so `mapHom` applies to it. -/
theorem mapHom_star (f : A →ₙ+* B) (hf : ∀ x, f (star x) = star (f x))
    (x : CayleyDickson A) : mapHom f hf (star x) = star (mapHom f hf x) :=
  CayleyDickson.map_star f hf (map_neg f) x

end Ring

/-- The reflection `a ↦ (re a, -im a)` of a double, extended to the next double,
preserves products: the instance `diag_reflect_mul` of `rocq/quantum/CdTowerRing.v`. -/
example {A : Type*} [NonAssocRing A] [StarRing A] (x y : CayleyDickson (CayleyDickson A)) :
    map reflect (x * y) = map reflect x * map reflect y := by
  let f : CayleyDickson A →ₙ+* CayleyDickson A :=
    { toFun := reflect
      map_mul' := reflect_mul
      map_zero' := by ext <;> simp
      map_add' := reflect_add }
  exact CayleyDickson.map_mul f reflect_star x y

namespace Tower

universe u

variable {R : Type u} [NonAssocRing R] [StarRing R]

/-- The iterated embedding `x ↦ (x, 0)` of level `j` into level `j + k`. -/
def lift (j : ℕ) : (k : ℕ) → Tower R j → Tower R (j + k)
  | 0, x => x
  | k + 1, x => mk (lift j k x) 0

/-- The iterated embedding preserves products. The Rocq original is `lift_mul` of the functor
`RingTower` in `rocq/quantum/CdTowerRing.v`. -/
theorem lift_mul (j k : ℕ) (x y : Tower R j) :
    lift j k (x * y) = lift j k x * lift j k y := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change mk (lift j k (x * y)) 0 = mk (lift j k x) 0 * mk (lift j k y) 0
    rw [mk_zero_mul_mk_zero, ih]

/-- The iterated embedding is injective. The Rocq original is `lift_injective` of the functor
`RingTower` in `rocq/quantum/CdTowerRing.v`. -/
theorem lift_injective (j k : ℕ) : Function.Injective (lift (R := R) j k) := by
  induction k with
  | zero => exact fun _ _ h => h
  | succ k ih => exact fun x y h => ih (mk_inj.1 h).1

end Tower

end CayleyDickson
