/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Tower

/-!
# Challenge: the basis and the coordinates of the Cayley-Dickson tower

This file restates, with `sorry` as each proof, the headline theorems that
`GororobaMath.CayleyDickson.TowerModule` proves and that the "Lean library" table of `README.md` names, together with the definitions that
`GororobaMath.CayleyDickson.TowerModule` introduces and those statements use (the module structure, the
reindexing equivalence `sumEquiv` and the basis).
This file imports the library module that the solution module itself imports, so `Tower`, `e` and
`negSign` are the library's own; a restated definition copies the solution's text and must elaborate to
the same constant.
`lake comparator --config` with the JSON file beside this one checks that each named theorem of the
solution module has the statement written here and depends only on `propext`, `Classical.choice` and
`Quot.sound`. No library module imports this file, and the admission gate does not build it.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

open Module

section Module

variable (R : Type u) [CommRing R] [StarRing R]

/-- The module structure of every level: multiplication at level `0`, the
componentwise action of `CayleyDickson.instModule` above it. -/
@[instance_reducible]
def moduleStructure : (k : ℕ) → Module R (Tower R k)
  | 0 => inferInstanceAs (Module R R)
  | k + 1 =>
    letI := moduleStructure k
    inferInstanceAs (Module R (CayleyDickson (Tower R k)))

instance instModule (k : ℕ) : Module R (Tower R k) := moduleStructure R k

end Module

section Basis

/-- `BitVec (k + 1)` splits by its top bit into two copies of `BitVec k`:
`Sum.inl q` is `q` with top bit `0`, `Sum.inr q` is `q` with top bit `1`. -/
def sumEquiv (k : ℕ) : BitVec k ⊕ BitVec k ≃ BitVec (k + 1) where
  toFun := Sum.elim (BitVec.cons false) (BitVec.cons true)
  invFun p := if p.msb then Sum.inr (p.setWidth k) else Sum.inl (p.setWidth k)
  left_inv s := by
    cases s <;> simp [BitVec.msb_cons, BitVec.setWidth_cons]
  right_inv p := by
    cases h : p.msb
    · simp only [h, Bool.false_eq_true, ↓reduceIte, Sum.elim_inl]
      rw [← h, BitVec.cons_msb_setWidth]
    · simp only [h, ↓reduceIte, Sum.elim_inr]
      rw [← h, BitVec.cons_msb_setWidth]

/-- `BitVec 0` has the one element `0#0`. -/
@[instance_reducible]
def uniqueBitVecZero : Unique (BitVec 0) := ⟨⟨0#0⟩, fun _ => BitVec.of_length_zero⟩

variable (R : Type u) [CommRing R] [StarRing R]

/-- The basis of `Tower R k` indexed by `BitVec k`: the unit at level `0`,
and above it the product basis of the two halves reindexed by the top bit. -/
noncomputable def basis : (k : ℕ) → Basis (BitVec k) R (Tower R k)
  | 0 =>
    @Basis.singleton (BitVec 0) R uniqueBitVecZero _
  | k + 1 =>
    (((basis k).prod (basis k)).map (linearEquivProd (Tower R k) R).symm).reindex (sumEquiv k)

/-- `Tower R k` has rank `2 ^ k` over a nontrivial commutative ring. -/
theorem finrank_eq [Nontrivial R] (k : ℕ) : finrank R (Tower R k) = 2 ^ k := by
  sorry

variable {R}

variable [TrivialStar R]

/-- Left multiplication by `e i` is a signed permutation of coordinates: the
coordinate of `e i * y` at `w` is the coordinate of `y` at `i ^^^ w`, with
the sign of `e i * e (i ^^^ w)`. -/
theorem repr_e_mul {k : ℕ} (i w : BitVec k) (y : Tower R k) :
    (basis R k).repr (e R k i * y) w =
      if negSign k i (i ^^^ w) then -(basis R k).repr y (i ^^^ w)
      else (basis R k).repr y (i ^^^ w) := by
  sorry

end Basis

end Tower

end CayleyDickson
