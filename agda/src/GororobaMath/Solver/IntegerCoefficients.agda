-- SPDX-License-Identifier: Apache-2.0
{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- A ring solver with integer coefficients over every commutative ring
--
-- The reflective solver of agda-stdlib (Tactic.RingSolver) normalises with
-- the coefficients in the ring itself, so over a ring with an abstract
-- carrier a sum such as 1# + (- 1#) stays a coefficient and x - x does not
-- normalise to 0.  Here the coefficients are integers, mapped into the
-- ring R by the homomorphism n ↦ n × 1#, so cancellation happens on
-- integer literals and the Horner normal form of an expression that is
-- zero in every commutative ring is the constant polynomial 0.
--
-- An identity l = r is checked by the type checker evaluating
-- norm (l ⊕ ⊝ r) to that constant: Zero (norm (l ⊕ ⊝ r)) reduces to the
-- unit type, and solve-≈ turns its inhabitant tt into a proof of
-- ⟦ l ⟧ ρ ≈ ⟦ r ⟧ ρ for every environment ρ.
------------------------------------------------------------------------

open import Algebra.Bundles using (CommutativeRing)

module GororobaMath.Solver.IntegerCoefficients
  {c ℓ} (R : CommutativeRing c ℓ) where

open import Data.Bool.Base using (Bool; true; false; T)
open import Data.Empty using (⊥-elim)
open import Data.Integer.Base as ℤ using (ℤ; +_; -[1+_]; _⊖_; _◃_; sign; ∣_∣)
import Data.Integer.Properties as ℤP
open import Data.Maybe.Base using (nothing)
open import Data.Nat.Base as ℕ using (ℕ; zero; suc; z≤n; z<s)
import Data.Nat.Properties as ℕP
open import Data.Sign.Base as Sign using (Sign)
open import Data.Vec.Base using (Vec)
open import Function.Base using (_⟨_⟩_)
open import Level using (0ℓ)
import Relation.Binary.PropositionalEquality.Core as ≡
open import Tactic.RingSolver.Core.AlmostCommutativeRing
  using (AlmostCommutativeRing; fromCommutativeRing; _-Raw-AlmostCommutative⟶_)
open import Tactic.RingSolver.Core.Polynomial.Parameters
  using (RawCoeff; Homomorphism)
open import Tactic.RingSolver.Core.Expression public
  using (Expr; Κ; Ι; _⊕_; _⊗_; _⊛_; ⊝_)
open import Tactic.RingSolver.Core.Expression using (module Eval)

open CommutativeRing R hiding (zero)
open import Algebra.Properties.Ring ring
  using (-‿distribˡ-*; -‿distribʳ-*; [-x][-y]≈xy)
open import Algebra.Properties.AbelianGroup +-abelianGroup
  using (ε⁻¹≈ε; ⁻¹-involutive; ⁻¹-∙-comm; x∙y⁻¹≈ε⇒x≈y)
open import Algebra.Properties.Semiring.Mult.TCOptimised semiring
  using (_×_; ×-homo-+; ×1-homo-*)
open import Algebra.Properties.Monoid.Mult.TCOptimised +-monoid
  using (1+×)
open import Relation.Binary.Reasoning.Setoid setoid

------------------------------------------------------------------------
-- The homomorphism from the integers

-- The image of a natural number: n × 1#, with 0 ↦ 0# and 1 ↦ 1# by
-- definition.
nat : ℕ → Carrier
nat n = n × 1#

⟦_⟧ℤ : ℤ → Carrier
⟦ + n      ⟧ℤ = nat n
⟦ -[1+ n ] ⟧ℤ = - nat (suc n)

private
  nat-cong : ∀ {m n} → m ≡.≡ n → nat m ≈ nat n
  nat-cong ≡.refl = refl

  -- (1 + a) - (1 + b) = a - b, the step of the difference lemma.
  shift : ∀ a b → (1# + a) + - (1# + b) ≈ a + - b
  shift a b = begin
    (1# + a) + - (1# + b)        ≈⟨ +-congˡ (⁻¹-∙-comm 1# b) ⟨
    (1# + a) + (- 1# + - b)      ≈⟨ +-assoc 1# a (- 1# + - b) ⟩
    1# + (a + (- 1# + - b))      ≈⟨ +-congˡ (+-assoc a (- 1#) (- b)) ⟨
    1# + ((a + - 1#) + - b)      ≈⟨ +-congˡ (+-congʳ (+-comm a (- 1#))) ⟩
    1# + ((- 1# + a) + - b)      ≈⟨ +-congˡ (+-assoc (- 1#) a (- b)) ⟩
    1# + (- 1# + (a + - b))      ≈⟨ +-assoc 1# (- 1#) (a + - b) ⟨
    (1# + - 1#) + (a + - b)      ≈⟨ +-congʳ (-‿inverseʳ 1#) ⟩
    0# + (a + - b)               ≈⟨ +-identityˡ (a + - b) ⟩
    a + - b                      ∎

  ⊖-hom : ∀ m n → ⟦ m ⊖ n ⟧ℤ ≈ nat m + - nat n
  ⊖-hom m zero = begin
    ⟦ m ⊖ zero ⟧ℤ  ≡⟨ ≡.cong ⟦_⟧ℤ (ℤP.⊖-≥ {m = m} {n = zero} z≤n) ⟩
    nat m          ≈⟨ +-identityʳ (nat m) ⟨
    nat m + 0#     ≈⟨ +-congˡ ε⁻¹≈ε ⟨
    nat m + - 0#   ∎
  ⊖-hom zero (suc n) = begin
    ⟦ zero ⊖ suc n ⟧ℤ   ≡⟨ ≡.cong ⟦_⟧ℤ (ℤP.⊖-< {m = zero} {n = suc n} z<s) ⟩
    - nat (suc n)       ≈⟨ +-identityˡ (- nat (suc n)) ⟨
    0# + - nat (suc n)  ∎
  ⊖-hom (suc m) (suc n) = begin
    ⟦ suc m ⊖ suc n ⟧ℤ                ≡⟨ ≡.cong ⟦_⟧ℤ (ℤP.[1+m]⊖[1+n]≡m⊖n m n) ⟩
    ⟦ m ⊖ n ⟧ℤ                        ≈⟨ ⊖-hom m n ⟩
    nat m + - nat n                   ≈⟨ shift (nat m) (nat n) ⟨
    (1# + nat m) + - (1# + nat n)     ≈⟨ +-cong (1+× m 1#) (-‿cong (1+× n 1#)) ⟨
    nat (suc m) + - nat (suc n)       ∎

  +-hom : ∀ i j → ⟦ i ℤ.+ j ⟧ℤ ≈ ⟦ i ⟧ℤ + ⟦ j ⟧ℤ
  +-hom -[1+ m ] -[1+ n ] = begin
    - nat (suc (suc (m ℕ.+ n)))        ≈⟨ -‿cong (nat-cong (≡.cong suc (ℕP.+-suc m n))) ⟨
    - nat (suc m ℕ.+ suc n)            ≈⟨ -‿cong (×-homo-+ 1# (suc m) (suc n)) ⟩
    - (nat (suc m) + nat (suc n))      ≈⟨ ⁻¹-∙-comm (nat (suc m)) (nat (suc n)) ⟨
    - nat (suc m) + - nat (suc n)      ∎
  +-hom -[1+ m ] (+ n) = begin
    ⟦ n ⊖ suc m ⟧ℤ                     ≈⟨ ⊖-hom n (suc m) ⟩
    nat n + - nat (suc m)              ≈⟨ +-comm (nat n) (- nat (suc m)) ⟩
    - nat (suc m) + nat n              ∎
  +-hom (+ m) -[1+ n ] = ⊖-hom m (suc n)
  +-hom (+ m) (+ n) = ×-homo-+ 1# m n

  neg-hom : ∀ i → ⟦ ℤ.- i ⟧ℤ ≈ - ⟦ i ⟧ℤ
  neg-hom (+ zero)   = sym ε⁻¹≈ε
  neg-hom (+ suc n)  = refl
  neg-hom -[1+ n ]   = sym (⁻¹-involutive (nat (suc n)))

  -- The sign of an integer acting on the ring.
  sgn : Sign → Carrier → Carrier
  sgn Sign.+ x = x
  sgn Sign.- x = - x

  sgn-cong : ∀ s {x y} → x ≈ y → sgn s x ≈ sgn s y
  sgn-cong Sign.+ h = h
  sgn-cong Sign.- h = -‿cong h

  sgn-* : ∀ s t x y → sgn (s Sign.* t) (x * y) ≈ sgn s x * sgn t y
  sgn-* Sign.+ Sign.+ x y = refl
  sgn-* Sign.+ Sign.- x y = -‿distribʳ-* x y
  sgn-* Sign.- Sign.+ x y = -‿distribˡ-* x y
  sgn-* Sign.- Sign.- x y = sym ([-x][-y]≈xy x y)

  ◃-hom : ∀ s n → ⟦ s ◃ n ⟧ℤ ≈ sgn s (nat n)
  ◃-hom Sign.+ zero    = refl
  ◃-hom Sign.+ (suc n) = refl
  ◃-hom Sign.- zero    = sym ε⁻¹≈ε
  ◃-hom Sign.- (suc n) = refl

  sign-hom : ∀ i → ⟦ i ⟧ℤ ≈ sgn (sign i) (nat ∣ i ∣)
  sign-hom (+ n)      = refl
  sign-hom -[1+ n ]   = refl

  *-hom : ∀ i j → ⟦ i ℤ.* j ⟧ℤ ≈ ⟦ i ⟧ℤ * ⟦ j ⟧ℤ
  *-hom i j = begin
    ⟦ (sign i Sign.* sign j) ◃ (∣ i ∣ ℕ.* ∣ j ∣) ⟧ℤ
      ≈⟨ ◃-hom (sign i Sign.* sign j) (∣ i ∣ ℕ.* ∣ j ∣) ⟩
    sgn (sign i Sign.* sign j) (nat (∣ i ∣ ℕ.* ∣ j ∣))
      ≈⟨ sgn-cong (sign i Sign.* sign j) (×1-homo-* ∣ i ∣ ∣ j ∣) ⟩
    sgn (sign i Sign.* sign j) (nat ∣ i ∣ * nat ∣ j ∣)
      ≈⟨ sgn-* (sign i) (sign j) (nat ∣ i ∣) (nat ∣ j ∣) ⟩
    sgn (sign i) (nat ∣ i ∣) * sgn (sign j) (nat ∣ j ∣)
      ≈⟨ *-cong (sign-hom i) (sign-hom j) ⟨
    ⟦ i ⟧ℤ * ⟦ j ⟧ℤ
      ∎

  isZeroℤ : ℤ → Bool
  isZeroℤ (+ zero) = true
  isZeroℤ _        = false

  zero-hom : ∀ x → T (isZeroℤ x) → 0# ≈ ⟦ x ⟧ℤ
  zero-hom (+ zero)  _ = refl
  zero-hom (+ suc n) ()
  zero-hom -[1+ n ]  ()

-- R as the target of the solver: its own operations, no zero test.
target : AlmostCommutativeRing c ℓ
target = fromCommutativeRing R (λ _ → nothing)

homomorphism : Homomorphism 0ℓ 0ℓ c ℓ
homomorphism = record
  { from = record { rawRing = ℤ.+-*-rawRing ; isZero = isZeroℤ }
  ; to = target
  ; morphism = record
    { ⟦_⟧    = ⟦_⟧ℤ
    ; +-homo = +-hom
    ; *-homo = *-hom
    ; -‿homo = neg-hom
    ; 0-homo = refl
    ; 1-homo = refl
    }
  ; Zero-C⟶Zero-R = zero-hom
  }

------------------------------------------------------------------------
-- Normalisation and its correctness (the construction of
-- Tactic.RingSolver.NonReflective, with integer coefficients)

open import Tactic.RingSolver.Core.Polynomial.Base (Homomorphism.from homomorphism)
  using (Poly; Zero; κ; ι; _⊞_; _⊠_; ⊟_; _⊡_)
open Eval rawRing ⟦_⟧ℤ public using (⟦_⟧)

norm : ∀ {n} → Expr ℤ n → Poly n
norm (Κ x)   = κ x
norm (Ι x)   = ι x
norm (x ⊕ y) = norm x ⊞ norm y
norm (x ⊗ y) = norm x ⊠ norm y
norm (⊝ x)   = ⊟ norm x
norm (x ⊛ i) = norm x ⊡ i

private
  open import Tactic.RingSolver.Core.Polynomial.Semantics homomorphism
    renaming (⟦_⟧ to ⟦_⟧ₚ)
  open import Tactic.RingSolver.Core.Polynomial.Homomorphism homomorphism
  open import Tactic.RingSolver.Core.Polynomial.Homomorphism.Lemmas homomorphism
    using () renaming (zero-hom to poly-zero-hom)
  open import Algebra.Properties.Semiring.Exp.TCOptimised semiring
    using (^-congˡ)

  correct : ∀ {n} (e : Expr ℤ n) ρ → ⟦ norm e ⟧ₚ ρ ≈ ⟦ e ⟧ ρ
  correct (Κ x)   ρ = κ-hom x ρ
  correct (Ι x)   ρ = ι-hom x ρ
  correct (x ⊕ y) ρ = ⊞-hom (norm x) (norm y) ρ ⟨ trans ⟩ (correct x ρ ⟨ +-cong ⟩ correct y ρ)
  correct (x ⊗ y) ρ = ⊠-hom (norm x) (norm y) ρ ⟨ trans ⟩ (correct x ρ ⟨ *-cong ⟩ correct y ρ)
  correct (⊝ x)   ρ = ⊟-hom (norm x) ρ ⟨ trans ⟩ -‿cong (correct x ρ)
  correct (x ⊛ i) ρ = ⊡-hom (norm x) i ρ ⟨ trans ⟩ ^-congˡ i (correct x ρ)

-- An expression whose normal form is the zero polynomial is zero in R.
solve-0 : ∀ {n} (e : Expr ℤ n) → Zero (norm e) → ∀ ρ → ⟦ e ⟧ ρ ≈ 0#
solve-0 e z ρ = sym (trans (poly-zero-hom (norm e) z ρ) (correct e ρ))

-- Two expressions whose difference normalises to zero are equal in R.
solve-≈ : ∀ {n} (l r : Expr ℤ n) → Zero (norm (l ⊕ ⊝ r)) → ∀ ρ → ⟦ l ⟧ ρ ≈ ⟦ r ⟧ ρ
solve-≈ l r z ρ = x∙y⁻¹≈ε⇒x≈y (⟦ l ⟧ ρ) (⟦ r ⟧ ρ) (solve-0 (l ⊕ ⊝ r) z ρ)
