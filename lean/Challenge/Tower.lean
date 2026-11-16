/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Basic

/-!
# Challenge: basis signs of the Cayley-Dickson tower

This file restates, with `sorry` as each proof, the headline theorems that
`GororobaMath.CayleyDickson.Tower` proves and that the "Lean library" table of `README.md` names, together with the definitions that
`GororobaMath.CayleyDickson.Tower` introduces and those statements use.
This file imports the library module that the solution module itself imports, so `CayleyDickson` and its
product are the library's own; a restated definition copies the solution's text and must elaborate to the
same constant.
`lake comparator --config` with the JSON file beside this one checks that each named theorem of the
solution module has the statement written here and depends only on `propext`, `Classical.choice` and
`Quot.sound`. No library module imports this file, and the admission gate does not build it.
-/

@[expose] public section

namespace CayleyDickson

universe u

/-- The `k`-fold Cayley-Dickson double of `R`. -/
def Tower (R : Type u) : ℕ → Type u
  | 0 => R
  | k + 1 => CayleyDickson (Tower R k)

namespace Tower

variable (R : Type u) [NonAssocRing R] [StarRing R]

/-- The ring and star structures of every level, built together because the
star structure of level `k + 1` is stated over the ring structure of
level `k`. -/
def levelStructure : (k : ℕ) → Σ' _ : NonAssocRing (Tower R k), StarRing (Tower R k)
  | 0 => ⟨inferInstanceAs (NonAssocRing R), inferInstanceAs (StarRing R)⟩
  | k + 1 =>
    ⟨@CayleyDickson.instNonAssocRing _ (levelStructure k).1 (levelStructure k).2,
      @CayleyDickson.instStarRing _ (levelStructure k).1 (levelStructure k).2⟩

instance instNonAssocRing (k : ℕ) : NonAssocRing (Tower R k) := (levelStructure R k).1

instance instStarRing (k : ℕ) : StarRing (Tower R k) := (levelStructure R k).2

variable {R}

/-- The element `(a, b)` of level `k + 1`. -/
def mk {k : ℕ} (a b : Tower R k) : Tower R (k + 1) := CayleyDickson.mk a b

variable (R) in
/-- The basis element of index `p`. The top bit of `p` selects the half of
the outermost double; the remaining bits index the level below. -/
def e : (k : ℕ) → BitVec k → Tower R k
  | 0, _ => (1 : Tower R 0)
  | k + 1, p =>
    if p.msb then mk 0 (e k (p.setWidth k)) else mk (e k (p.setWidth k)) 0

/-- `true` when `e k p * e k q = -e k (p ^^^ q)`. The four branches are the
four top-bit cases of `cd_core.cd_sign`. -/
def negSign : (k : ℕ) → BitVec k → BitVec k → Bool
  | 0, _, _ => false
  | k + 1, p, q =>
    match p.msb, q.msb with
    | false, false => negSign k (p.setWidth k) (q.setWidth k)
    | false, true => negSign k (q.setWidth k) (p.setWidth k)
    | true, false =>
      xor (decide (q.setWidth k ≠ 0#k)) (negSign k (p.setWidth k) (q.setWidth k))
    | true, true =>
      if q.setWidth k = 0#k then true else negSign k (q.setWidth k) (p.setWidth k)

/-- The sign of `e k p * e k q` as an integer, `cd_core.cd_sign`. -/
def sign (k : ℕ) (p q : BitVec k) : ℤ := if negSign k p q then -1 else 1

/-- Conjugation fixes `e k 0 = 1` and negates every other basis element. -/
theorem star_e : ∀ (k : ℕ) (p : BitVec k),
    star (e R k p) = if p = 0#k then e R k p else -e R k p := by
  sorry

/-- The product of two basis elements is a basis element up to sign: the
index is the bitwise exclusive or and the sign is `negSign`. -/
theorem e_mul_e : ∀ (k : ℕ) (p q : BitVec k),
    e R k p * e R k q = if negSign k p q then -e R k (p ^^^ q) else e R k (p ^^^ q) := by
  sorry

/-- `e k p * e k q` as a signed basis element, in the form of
`cd_core.cd_sign`. -/
theorem e_mul_e_sign (k : ℕ) (p q : BitVec k) :
    e R k p * e R k q = sign k p q • e R k (p ^^^ q) := by
  sorry

/-- Every basis element other than `1` squares to `-1`. -/
theorem e_mul_self (k : ℕ) {p : BitVec k} (h : p ≠ 0#k) : e R k p * e R k p = -1 := by
  sorry

/-- Left multiplication by `e k p` applied twice: the sign of
`e k p * e k (p ^^^ q)` is that of `e k p * e k q`, reversed when `p ≠ 0`.
It is the basis form of `e p * (e p * e q) = -e q` for `p ≠ 0`. -/
theorem negSign_xor_right : ∀ (k : ℕ) (p q : BitVec k),
    negSign k p (p ^^^ q) = xor (decide (p ≠ 0#k)) (negSign k p q) := by
  sorry

/-- Two distinct basis elements other than `1` anticommute. -/
theorem e_mul_e_anticomm (k : ℕ) {p q : BitVec k} (hp : p ≠ 0#k) (hq : q ≠ 0#k)
    (hpq : p ≠ q) :
    e R k q * e R k p = -(e R k p * e R k q) := by
  sorry

end Tower

end CayleyDickson
