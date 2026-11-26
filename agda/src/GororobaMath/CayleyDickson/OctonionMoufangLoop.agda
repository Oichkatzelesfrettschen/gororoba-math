-- SPDX-License-Identifier: Apache-2.0
{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- The unit-norm octonions over a commutative ring form a Moufang loop
--
-- Convention: R is a commutative ring with the identity as star, and
-- Octonion is Tower 3 R of GororobaMath.CayleyDickson.Doubling, with the
-- product (a , b) (c , d) = (a c - conj d b , d a + b conj c) and
-- conj (a , b) = (conj a , - b) of lean/GororobaMath/CayleyDickson/Tower.lean
-- (CayleyDickson.Tower.mk_mul_mk, CayleyDickson.Tower.star_mk) at level 3.
-- N x is the sum of the squares of the eight coordinates, Tower.dot 3 x x
-- of lean/GororobaMath/CayleyDickson/AnnihilatorSymmetry.lean.  Over the
-- real numbers the unit-norm octonions are the sphere S^7.
--
-- The loop operations are the product, the left division
-- x \\ y = conj x · y, the right division y // x = y · conj x and the
-- unit one; the Moufang loop is IsMoufangLoop of agda-stdlib
-- (Algebra.Structures: a left Bol loop with the right Bol law and the law
-- Identical), and the three Moufang identities of the claim follow from
-- Algebra.Properties.MoufangLoop.
--
-- Each octonion identity is checked coordinate by coordinate:
-- the same raw operations run on the integer-coefficient expressions of
-- GororobaMath.Solver.IntegerCoefficients, the type checker normalises the
-- difference of the two sides of each coordinate to the zero polynomial,
-- and solve-≈ evaluates the expressions at the coordinates of the
-- arguments.  No identity assumes alternativity: each is a polynomial
-- identity over every commutative ring.
--
-- Partners: the identities are the level-3 theorems of
-- lean/GororobaMath/CayleyDickson/Alternative.lean
-- (CayleyDickson.Tower.moufang_left_three, CayleyDickson.Tower.moufang_middle_three,
-- CayleyDickson.Tower.moufang_right_three), and N-mul is the level-3 case of
-- CayleyDickson.Tower.dot_mul_self_of_le_three of
-- lean/GororobaMath/CayleyDickson/NormMultiplicative.lean.  The Rocq trees
-- of this repository state no Moufang identity, and neither Mathlib v4.35.0
-- nor MathComp 2.6.0 defines a quasigroup, a loop or a Moufang loop, so no
-- partner packages the units as a loop.
--
-- Main results
--
-- * N-mul: N (x · y) ≈ N x * N y.
-- * isMoufangLoop, moufangLoop: the unit-norm octonions with the
--   operations above are a Moufang loop.
-- * moufang-left, moufang-right, moufang-middle: the three identities in
--   the form of the claim, a (x (a y)) = ((a x) a) y,
--   ((x a) y) a = x (a (y a)) and (a x) (y a) = (a (x y)) a, for units.
-- * solution-left, solution-right: a x = b and y a = b have the solutions
--   a \\ b and b // a and no others.
-- * associator-e₁e₂e₄, not-associative: the unit basis triple e₁, e₂, e₄
--   has associator 2 e₇, so the loop is a group only if 1# + 1# ≈ 0#.
------------------------------------------------------------------------

open import Algebra.Bundles using (CommutativeRing; MoufangLoop; Quasigroup)

module GororobaMath.CayleyDickson.OctonionMoufangLoop
  {c ℓ} (R : CommutativeRing c ℓ) where

open import Data.Integer.Base using (ℤ; +_)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Data.Vec.Base using (Vec; []; _∷_; _++_; take; drop; map; allFin)
open import Level using (_⊔_)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Structures using (IsEquivalence)
import Algebra.Properties.MoufangLoop
import Algebra.Properties.Quasigroup

open import GororobaMath.CayleyDickson.Doubling
open import GororobaMath.Solver.IntegerCoefficients R
open import Tactic.RingSolver.Core.Polynomial.Parameters using (Homomorphism)
open import Tactic.RingSolver.Core.Polynomial.Base (Homomorphism.from homomorphism)
  using (Zero)

open CommutativeRing R hiding (zero)
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- The octonions

scalarOps : StarOps Carrier
scalarOps = record { add = _+_ ; mul = _*_ ; neg = -_ ; conj = λ a → a }

Octonion : Set c
Octonion = Tower 3 Carrier

private
  module Oc = StarOps (tower 3 scalarOps)

infixl 7 _·_
_·_ : Octonion → Octonion → Octonion
_·_ = Oc.mul

conj : Octonion → Octonion
conj = Oc.conj

infix 4 _≋_
_≋_ : Rel Octonion ℓ
_≋_ = Pointwise 3 _≈_

≋-isEquivalence : IsEquivalence _≋_
≋-isEquivalence = Pointwise-isEquivalence 3 isEquivalence

private
  module ≋ = IsEquivalence ≋-isEquivalence

  scalarCong : StarOpsCong scalarOps _≈_
  scalarCong = record
    { add-cong = +-cong ; mul-cong = *-cong ; neg-cong = -‿cong ; conj-cong = λ h → h }

  module OcCong = StarOpsCong (tower-cong 3 scalarCong)

-- The trace form, the scalar multiple and the unit.
N : Octonion → Carrier
N x = dotT 3 _+_ _*_ x x

infixr 8 _•_
_•_ : Carrier → Octonion → Octonion
s • x = mapT 3 (s *_) x

one : Octonion
one = unitT 3 1# 0#

------------------------------------------------------------------------
-- The coordinate solver on octonion expressions

private
  exprOps : ∀ {n} → StarOps (Expr ℤ n)
  exprOps = record { add = _⊕_ ; mul = _⊗_ ; neg = ⊝_ ; conj = λ e → e }

  module OE {n} = StarOps (tower 3 (exprOps {n}))

  NE : ∀ {n} → Tower 3 (Expr ℤ n) → Expr ℤ n
  NE X = dotT 3 _⊕_ _⊗_ X X

  sE : ∀ {n} → Expr ℤ n → Tower 3 (Expr ℤ n) → Tower 3 (Expr ℤ n)
  sE s X = mapT 3 (s ⊗_) X

  oneE : ∀ {n} → Tower 3 (Expr ℤ n)
  oneE = unitT 3 (Κ (+ 1)) (Κ (+ 0))

  vars : ∀ n → Vec (Expr ℤ n) n
  vars n = map Ι (allFin n)

  -- The variables of one, two and three octonion arguments.
  X₁ : Tower 3 (Expr ℤ 8)
  X₁ = unflatten 3 (vars 8)

  X₂ Y₂ : Tower 3 (Expr ℤ 16)
  X₂ = unflatten 3 (take 8 (vars 16))
  Y₂ = unflatten 3 (drop 8 (vars 16))

  X₃ Y₃ Z₃ : Tower 3 (Expr ℤ 24)
  X₃ = unflatten 3 (take 8 (vars 24))
  Y₃ = unflatten 3 (take 8 (drop 8 (vars 24)))
  Z₃ = unflatten 3 (drop 16 (vars 24))

  ρ₂ : Octonion → Octonion → Vec Carrier 16
  ρ₂ x y = flatten 3 x ++ flatten 3 y

  ρ₃ : Octonion → Octonion → Octonion → Vec Carrier 24
  ρ₃ x y z = flatten 3 x ++ (flatten 3 y ++ flatten 3 z)

  -- Each coordinate of L - R normalises to the zero polynomial.
  Checked : ∀ {n} → Tower 3 (Expr ℤ n) → Tower 3 (Expr ℤ n) → Set
  Checked = Pointwise 3 (λ l r → Zero (norm (l ⊕ ⊝ r)))

  solveT : ∀ {n} k (L R′ : Tower k (Expr ℤ n)) →
           Pointwise k (λ l r → Zero (norm (l ⊕ ⊝ r))) L R′ → ∀ ρ →
           Pointwise k _≈_ (mapT k (λ e → ⟦ e ⟧ ρ) L) (mapT k (λ e → ⟦ e ⟧ ρ) R′)
  solveT zero    l r z ρ = solve-≈ l r z ρ
  solveT (suc k) L R′ (z₁ , z₂) ρ =
    solveT k (proj₁ L) (proj₁ R′) z₁ ρ , solveT k (proj₂ L) (proj₂ R′) z₂ ρ

  -- The eight coordinate checks, each discharged by evaluation.
  pattern ✓ = ((tt , tt) , (tt , tt)) , ((tt , tt) , (tt , tt))

------------------------------------------------------------------------
-- Octonion identities over every commutative ring

-- The eight-square identity.
N-mul : ∀ x y → N (x · y) ≈ N x * N y
N-mul x y = solve-≈ (NE (OE.mul X₂ Y₂)) (NE X₂ ⊗ NE Y₂) tt (ρ₂ x y)

N-conj : ∀ x → N (conj x) ≈ N x
N-conj x = solve-≈ (NE (OE.conj X₁)) (NE X₁) tt (flatten 3 x)

N-one : N one ≈ 1#
N-one = solve-≈ (NE (oneE {0})) (Κ (+ 1)) tt []

·-identityˡ : ∀ x → one · x ≋ x
·-identityˡ x = solveT 3 (OE.mul oneE X₁) X₁ ✓ (flatten 3 x)

·-identityʳ : ∀ x → x · one ≋ x
·-identityʳ x = solveT 3 (OE.mul X₁ oneE) X₁ ✓ (flatten 3 x)

-- The left and right inverse properties with the norm as factor.
conj-·-cancelˡ : ∀ x y → conj x · (x · y) ≋ N x • y
conj-·-cancelˡ x y =
  solveT 3 (OE.mul (OE.conj X₂) (OE.mul X₂ Y₂)) (sE (NE X₂) Y₂) ✓ (ρ₂ x y)

·-conj-cancelˡ : ∀ x y → x · (conj x · y) ≋ N x • y
·-conj-cancelˡ x y =
  solveT 3 (OE.mul X₂ (OE.mul (OE.conj X₂) Y₂)) (sE (NE X₂) Y₂) ✓ (ρ₂ x y)

conj-·-cancelʳ : ∀ x y → (y · conj x) · x ≋ N x • y
conj-·-cancelʳ x y =
  solveT 3 (OE.mul (OE.mul Y₂ (OE.conj X₂)) X₂) (sE (NE X₂) Y₂) ✓ (ρ₂ x y)

·-conj-cancelʳ : ∀ x y → (y · x) · conj x ≋ N x • y
·-conj-cancelʳ x y =
  solveT 3 (OE.mul (OE.mul Y₂ X₂) (OE.conj X₂)) (sE (NE X₂) Y₂) ✓ (ρ₂ x y)

-- The three laws of IsMoufangLoop, in the variable order of
-- Algebra.Definitions (LeftBol, RightBol, Identical).
leftBol-· : ∀ x y z → x · (y · (x · z)) ≋ (x · (y · x)) · z
leftBol-· x y z =
  solveT 3 (OE.mul X₃ (OE.mul Y₃ (OE.mul X₃ Z₃))) (OE.mul (OE.mul X₃ (OE.mul Y₃ X₃)) Z₃)
         ✓ (ρ₃ x y z)

rightBol-· : ∀ x y z → ((z · x) · y) · x ≋ z · ((x · y) · x)
rightBol-· x y z =
  solveT 3 (OE.mul (OE.mul (OE.mul Z₃ X₃) Y₃) X₃) (OE.mul Z₃ (OE.mul (OE.mul X₃ Y₃) X₃))
         ✓ (ρ₃ x y z)

identical-· : ∀ x y z → (z · x) · (y · z) ≋ z · ((x · y) · z)
identical-· x y z =
  solveT 3 (OE.mul (OE.mul Z₃ X₃) (OE.mul Y₃ Z₃)) (OE.mul Z₃ (OE.mul (OE.mul X₃ Y₃) Z₃))
         ✓ (ρ₃ x y z)

------------------------------------------------------------------------
-- Scalar multiples

private
  •-congˡ : ∀ k {s t} (y : Tower k Carrier) → s ≈ t →
            Pointwise k _≈_ (mapT k (s *_) y) (mapT k (t *_) y)
  •-congˡ zero    y h = *-congʳ h
  •-congˡ (suc k) y h = •-congˡ k (proj₁ y) h , •-congˡ k (proj₂ y) h

  •-identity : ∀ k (y : Tower k Carrier) → Pointwise k _≈_ (mapT k (1# *_) y) y
  •-identity zero    y = *-identityˡ y
  •-identity (suc k) y = •-identity k (proj₁ y) , •-identity k (proj₂ y)

  -- A unit times y is y.
  unit-• : ∀ {x} y → N x ≈ 1# → N x • y ≋ y
  unit-• y h = ≋.trans (•-congˡ 3 y h) (•-identity 3 y)

------------------------------------------------------------------------
-- The loop of unit-norm octonions

Unit : Set (c ⊔ ℓ)
Unit = Σ Octonion (λ x → N x ≈ 1#)

infix 4 _≈₁_
_≈₁_ : Rel Unit ℓ
u ≈₁ v = proj₁ u ≋ proj₁ v

private
  -- The norm of a product of units.
  unit-mul : ∀ {x y} → N x ≈ 1# → N y ≈ 1# → N (x · y) ≈ 1#
  unit-mul {x} {y} p q = begin
    N (x · y)   ≈⟨ N-mul x y ⟩
    N x * N y   ≈⟨ *-cong p q ⟩
    1# * 1#     ≈⟨ *-identityˡ 1# ⟩
    1#          ∎

  unit-conj : ∀ {x} → N x ≈ 1# → N (conj x) ≈ 1#
  unit-conj {x} p = trans (N-conj x) p

infixl 7 _∙_ _\\_ _//_

_∙_ : Unit → Unit → Unit
(x , p) ∙ (y , q) = x · y , unit-mul p q

_\\_ : Unit → Unit → Unit
(x , p) \\ (y , q) = conj x · y , unit-mul (unit-conj p) q

_//_ : Unit → Unit → Unit
(y , q) // (x , p) = y · conj x , unit-mul q (unit-conj p)

ε : Unit
ε = one , N-one

open import Algebra.Structures _≈₁_
  using (IsMagma; IsQuasigroup; IsLoop; IsLeftBolLoop; IsMoufangLoop)

≈₁-isEquivalence : IsEquivalence _≈₁_
≈₁-isEquivalence = record { refl = ≋.refl ; sym = ≋.sym ; trans = ≋.trans }

isMoufangLoop : IsMoufangLoop _∙_ _\\_ _//_ ε
isMoufangLoop = record
  { isLeftBolLoop = record
    { isLoop = record
      { isQuasigroup = record
        { isMagma = record
          { isEquivalence = ≈₁-isEquivalence
          ; ∙-cong = OcCong.mul-cong
          }
        ; \\-cong = λ h h′ → OcCong.mul-cong (OcCong.conj-cong h) h′
        ; //-cong = λ h h′ → OcCong.mul-cong h (OcCong.conj-cong h′)
        ; leftDivides =
            (λ (x , p) (y , _) → ≋.trans (·-conj-cancelˡ x y) (unit-• y p)) ,
            (λ (x , p) (y , _) → ≋.trans (conj-·-cancelˡ x y) (unit-• y p))
        ; rightDivides =
            (λ (x , p) (y , _) → ≋.trans (conj-·-cancelʳ x y) (unit-• y p)) ,
            (λ (x , p) (y , _) → ≋.trans (·-conj-cancelʳ x y) (unit-• y p))
        }
      ; identity = (λ (x , _) → ·-identityˡ x) , (λ (x , _) → ·-identityʳ x)
      }
    ; leftBol = λ (x , _) (y , _) (z , _) → leftBol-· x y z
    }
  ; rightBol = λ (x , _) (y , _) (z , _) → rightBol-· x y z
  ; identical = λ (x , _) (y , _) (z , _) → identical-· x y z
  }

moufangLoop : MoufangLoop (c ⊔ ℓ) ℓ
moufangLoop = record { isMoufangLoop = isMoufangLoop }

------------------------------------------------------------------------
-- Consequences through the library's Moufang loop theory

private
  module ML = Algebra.Properties.MoufangLoop moufangLoop
  quasigroup : Quasigroup (c ⊔ ℓ) ℓ
  quasigroup = record { isQuasigroup = IsMoufangLoop.isQuasigroup isMoufangLoop }

  module Q = Algebra.Properties.Quasigroup quasigroup

-- Left: a (x (a y)) = ((a x) a) y.
moufang-left : ∀ a x y → a ∙ (x ∙ (a ∙ y)) ≈₁ ((a ∙ x) ∙ a) ∙ y
moufang-left a x y = ML.z∙xzy≈zxz∙y x y a

-- Right: ((x a) y) a = x (a (y a)).
moufang-right : ∀ a x y → ((x ∙ a) ∙ y) ∙ a ≈₁ x ∙ (a ∙ (y ∙ a))
moufang-right a x y = ≋.sym (ML.x∙zyz≈xzy∙z x y a)

-- Middle: (a x) (y a) = (a (x y)) a.
moufang-middle : ∀ a x y → (a ∙ x) ∙ (y ∙ a) ≈₁ (a ∙ (x ∙ y)) ∙ a
moufang-middle a x y = ≋.trans (IsMoufangLoop.identical isMoufangLoop x y a) (ML.z∙xyz≈zxy∙z x y a)

-- The equations a x = b and y a = b have exactly the solutions
-- a \\ b and b // a.
solution-left : ∀ a x b → a ∙ x ≈₁ b → x ≈₁ a \\ b
solution-left = Q.y≈x\\z

solution-right : ∀ a y b → y ∙ a ≈₁ b → y ≈₁ b // a
solution-right a y b = Q.x≈z//y y a b

------------------------------------------------------------------------
-- The unit basis triple e₁, e₂, e₄ does not associate

private
  basisE : ∀ {n} → Vec (Expr ℤ n) 8 → Tower 3 (Expr ℤ n)
  basisE v = unflatten 3 v

  e₁E e₂E e₄E : Tower 3 (Expr ℤ 0)
  e₁E = basisE (Κ (+ 0) ∷ Κ (+ 1) ∷ Κ (+ 0) ∷ Κ (+ 0) ∷ Κ (+ 0) ∷ Κ (+ 0) ∷ Κ (+ 0) ∷ Κ (+ 0) ∷ [])
  e₂E = basisE (Κ (+ 0) ∷ Κ (+ 0) ∷ Κ (+ 1) ∷ Κ (+ 0) ∷ Κ (+ 0) ∷ Κ (+ 0) ∷ Κ (+ 0) ∷ Κ (+ 0) ∷ [])
  e₄E = basisE (Κ (+ 0) ∷ Κ (+ 0) ∷ Κ (+ 0) ∷ Κ (+ 0) ∷ Κ (+ 1) ∷ Κ (+ 0) ∷ Κ (+ 0) ∷ Κ (+ 0) ∷ [])

-- The basis elements of index 1, 2 and 4.
e₁ e₂ e₄ : Octonion
e₁ = mapT 3 (λ e → ⟦ e ⟧ []) e₁E
e₂ = mapT 3 (λ e → ⟦ e ⟧ []) e₂E
e₄ = mapT 3 (λ e → ⟦ e ⟧ []) e₄E

N-e₁ : N e₁ ≈ 1#
N-e₁ = solve-≈ (NE e₁E) (Κ (+ 1)) tt []

N-e₂ : N e₂ ≈ 1#
N-e₂ = solve-≈ (NE e₂E) (Κ (+ 1)) tt []

N-e₄ : N e₄ ≈ 1#
N-e₄ = solve-≈ (NE e₄E) (Κ (+ 1)) tt []

-- Coordinate 7 of the associator ((e₁ e₂) e₄) - (e₁ (e₂ e₄)) is 2:
-- (e₁ e₂) e₄ = e₇ and e₁ (e₂ e₄) = - e₇.
associator-e₁e₂e₄ :
  proj₂ (proj₂ (proj₂ ((e₁ · e₂) · e₄))) + - proj₂ (proj₂ (proj₂ (e₁ · (e₂ · e₄))))
    ≈ 1# + 1#
associator-e₁e₂e₄ =
  solve-≈ (π₇ (OE.mul (OE.mul e₁E e₂E) e₄E) ⊕ ⊝ π₇ (OE.mul e₁E (OE.mul e₂E e₄E)))
          (Κ (+ 2)) tt []
  where
  π₇ : Tower 3 (Expr ℤ 0) → Expr ℤ 0
  π₇ x = proj₂ (proj₂ (proj₂ x))

-- If the loop associates then 1# + 1# ≈ 0#.
not-associative : (∀ u v w → (u ∙ v) ∙ w ≈₁ u ∙ (v ∙ w)) → 1# + 1# ≈ 0#
not-associative assoc = begin
  1# + 1#          ≈⟨ associator-e₁e₂e₄ ⟨
  a + - b          ≈⟨ +-congʳ h ⟩
  b + - b          ≈⟨ -‿inverseʳ b ⟩
  0#               ∎
  where
  a b : Carrier
  a = proj₂ (proj₂ (proj₂ ((e₁ · e₂) · e₄)))
  b = proj₂ (proj₂ (proj₂ (e₁ · (e₂ · e₄))))
  h : a ≈ b
  h = proj₂ (proj₂ (proj₂ (assoc (e₁ , N-e₁) (e₂ , N-e₂) (e₄ , N-e₄))))
