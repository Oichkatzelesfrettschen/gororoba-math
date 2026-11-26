-- SPDX-License-Identifier: Apache-2.0
{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- The Cayley-Dickson doubling on raw operations
--
-- Convention: an element of level k + 1 is a pair (a , b) of elements of
-- level k, and the doubled operations are
--
--   (a , b) + (c , d) = (a + c , b + d)
--   (a , b) (c , d)   = (a c - conj d b , d a + b conj c)
--   - (a , b)         = (- a , - b)
--   conj (a , b)      = (conj a , - b),
--
-- the product and star of lean/GororobaMath/CayleyDickson/Tower.lean
-- (CayleyDickson.Tower.mk_mul_mk and CayleyDickson.Tower.star_mk), so
-- Tower 3 over a commutative ring whose star is the identity is the
-- octonion algebra Tower R 3 of that file.  flatten lists the 2 ^ k
-- coordinates with the first component first, so coordinate p is the
-- basis index p of Tower.e, the bit of 2 ^ k selecting the second half
-- of the outermost double.
--
-- The operations are raw: the same definitions run on a ring carrier and
-- on the polynomial expressions of the ring solver, which is how
-- GororobaMath.CayleyDickson.OctonionMoufangLoop checks the octonion
-- identities coordinate by coordinate.
------------------------------------------------------------------------

module GororobaMath.CayleyDickson.Doubling where

open import Data.Nat.Base using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Vec.Base using (Vec; _∷_; []; _++_; take; drop)
open import Level using (Level; _⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)

private
  variable
    a b p : Level

-- The operations that the doubling reads and produces.
record StarOps (A : Set a) : Set a where
  field
    add mul : A → A → A
    neg conj : A → A

-- Level k of the tower over A: k nested pairs.
Tower : ℕ → Set a → Set a
Tower zero    A = A
Tower (suc k) A = Tower k A × Tower k A

-- One Cayley-Dickson doubling.
double : {A : Set a} → StarOps A → StarOps (A × A)
double o = record
  { add  = λ x y → add (proj₁ x) (proj₁ y) , add (proj₂ x) (proj₂ y)
  ; mul  = λ x y →
      add (mul (proj₁ x) (proj₁ y)) (neg (mul (conj (proj₂ y)) (proj₂ x))) ,
      add (mul (proj₂ y) (proj₁ x)) (mul (proj₂ x) (conj (proj₁ y)))
  ; neg  = λ x → neg (proj₁ x) , neg (proj₂ x)
  ; conj = λ x → conj (proj₁ x) , neg (proj₂ x)
  }
  where open StarOps o

-- The operations of level k.
tower : {A : Set a} (k : ℕ) → StarOps A → StarOps (Tower k A)
tower zero    o = o
tower (suc k) o = double (tower k o)

-- The coordinatewise lift of a function.
mapT : {A : Set a} {B : Set b} (k : ℕ) → (A → B) → Tower k A → Tower k B
mapT zero    f x = f x
mapT (suc k) f x = mapT k f (proj₁ x) , mapT k f (proj₂ x)

-- The coordinatewise lift of a relation.
Pointwise : {A : Set a} {B : Set b} (k : ℕ) → (A → B → Set p) →
            Tower k A → Tower k B → Set p
Pointwise zero    P x y = P x y
Pointwise (suc k) P x y =
  Pointwise k P (proj₁ x) (proj₁ y) × Pointwise k P (proj₂ x) (proj₂ y)

-- The element with first coordinate o and every other coordinate z.
unitT : {A : Set a} (k : ℕ) → A → A → Tower k A
unitT zero    o z = o
unitT (suc k) o z = unitT k o z , unitT k z z

-- The trace form: the sum over the coordinates of the products.
dotT : {A : Set a} (k : ℕ) → (A → A → A) → (A → A → A) → Tower k A → Tower k A → A
dotT zero    add mul x y = mul x y
dotT (suc k) add mul x y =
  add (dotT k add mul (proj₁ x) (proj₁ y)) (dotT k add mul (proj₂ x) (proj₂ y))

-- The number of coordinates, 2 ^ k.
size : ℕ → ℕ
size zero    = 1
size (suc k) = size k +ℕ size k

-- The coordinates in basis-index order, and back.
flatten : {A : Set a} (k : ℕ) → Tower k A → Vec A (size k)
flatten zero    x = x ∷ []
flatten (suc k) x = flatten k (proj₁ x) ++ flatten k (proj₂ x)

unflatten : {A : Set a} (k : ℕ) → Vec A (size k) → Tower k A
unflatten zero    (x ∷ _) = x
unflatten (suc k) v       = unflatten k (take (size k) v) , unflatten k (drop (size k) v)

-- A relation that is an equivalence lifts to an equivalence.
Pointwise-isEquivalence : {A : Set a} {_∼_ : Rel A p} (k : ℕ) →
                          IsEquivalence _∼_ → IsEquivalence (Pointwise k _∼_)
Pointwise-isEquivalence zero    e = e
Pointwise-isEquivalence (suc k) e = record
  { refl  = E.refl , E.refl
  ; sym   = λ (h₁ , h₂) → E.sym h₁ , E.sym h₂
  ; trans = λ (h₁ , h₂) (g₁ , g₂) → E.trans h₁ g₁ , E.trans h₂ g₂
  }
  where module E = IsEquivalence (Pointwise-isEquivalence k e)

-- The operations respect a relation: the hypothesis of StarOpsCong.
record StarOpsCong {A : Set a} (o : StarOps A) (_∼_ : Rel A p) : Set (a ⊔ p) where
  open StarOps o
  field
    add-cong  : ∀ {x x′ y y′} → x ∼ x′ → y ∼ y′ → add x y ∼ add x′ y′
    mul-cong  : ∀ {x x′ y y′} → x ∼ x′ → y ∼ y′ → mul x y ∼ mul x′ y′
    neg-cong  : ∀ {x x′} → x ∼ x′ → neg x ∼ neg x′
    conj-cong : ∀ {x x′} → x ∼ x′ → conj x ∼ conj x′

-- Every doubling keeps the congruence of the four operations.
double-cong : {A : Set a} {o : StarOps A} {_∼_ : Rel A p} →
              StarOpsCong o _∼_ → StarOpsCong (double o) (Pointwise 1 _∼_)
double-cong c = record
  { add-cong  = λ (x₁ , x₂) (y₁ , y₂) → add-cong x₁ y₁ , add-cong x₂ y₂
  ; mul-cong  = λ (x₁ , x₂) (y₁ , y₂) →
      add-cong (mul-cong x₁ y₁) (neg-cong (mul-cong (conj-cong y₂) x₂)) ,
      add-cong (mul-cong y₂ x₁) (mul-cong x₂ (conj-cong y₁))
  ; neg-cong  = λ (x₁ , x₂) → neg-cong x₁ , neg-cong x₂
  ; conj-cong = λ (x₁ , x₂) → conj-cong x₁ , neg-cong x₂
  }
  where open StarOpsCong c

tower-cong : {A : Set a} {o : StarOps A} {_∼_ : Rel A p} (k : ℕ) →
             StarOpsCong o _∼_ → StarOpsCong (tower k o) (Pointwise k _∼_)
tower-cong zero    c = c
tower-cong (suc k) c = double-cong (tower-cong k c)
