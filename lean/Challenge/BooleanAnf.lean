/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TowerModule

/-!
# Challenge: the algebraic normal form of a Boolean function

This file restates, with `sorry` as each proof, the headline theorems that the solution
module proves and that the "Lean library" table of `README.md` names, with the
definitions those statements use. It imports the library modules that the solution
module imports. `lake comparator --config` with the JSON file beside this one checks
that each named theorem of the solution module has the statement written here and
depends only on `propext`, `Classical.choice` and `Quot.sound`. No library module
imports this file, and the admission gate does not build it.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

/-- The coefficient of the monomial `∏ i ∈ s, x i` in the algebraic normal form of
`f`: the parity of the number of masks `t` under `s` with `f t`. -/
def anfCoeff {k : ℕ} (f : BitVec k → Bool) (s : BitVec k) : Bool :=
  decide (Odd (Finset.univ.filter fun t => t &&& s = t ∧ f t = true).card)

/-- The sum at `x` of the monomials that the table `c` selects: the parity of the
number of masks `s` under `x` with `c s`. -/
def anfEval {k : ℕ} (c : BitVec k → Bool) (x : BitVec k) : Bool :=
  decide (Odd (Finset.univ.filter fun s => s &&& x = s ∧ c s = true).card)

/-- A Boolean as an element of `ZMod 2`. -/
def boolZMod (b : Bool) : ZMod 2 := if b then 1 else 0

/-- Moebius inversion: the normal form with the coefficients `anfCoeff f` evaluates
to `f`. The Rocq original is `anf_inversion` of `rocq/quantum/CdSignRowAnf.v`. -/
theorem anfEval_anfCoeff {k : ℕ} (f : BitVec k → Bool) (x : BitVec k) :
    anfEval (anfCoeff f) x = f x := by
  sorry

/-- A coefficient table whose normal form evaluates to `f` is the canonical one. The
Rocq original is `canonical_anf_unique` of `rocq/open/theories/BooleanANFDegree.v`. -/
theorem anfCoeff_unique {k : ℕ} (f c : BitVec k → Bool) (h : ∀ x, anfEval c x = f x) :
    c = anfCoeff f := by
  sorry

/-- A mask as the set of its set bits has `weight s` elements. -/
def weight {k : ℕ} (s : BitVec k) : ℕ := (Finset.univ.filter fun i : Fin k => s.getLsbD i).card

/-- The algebraic degree of `f`: the largest weight of a monomial with coefficient `true`; the
zero function has degree `0`. -/
def anfDegree {k : ℕ} (f : BitVec k → Bool) : ℕ :=
  (Finset.univ.filter fun s => anfCoeff f s = true).sup weight

/-- The sum of the indicators of two distinct points has degree `k - 1`. The Rocq original is
`two_point_indicator_degree` of `rocq/open/theories/BooleanANFDegree.v`. -/
theorem anfDegree_two_point {k : ℕ} {a b : BitVec k} (h : a ≠ b) :
    anfDegree (fun x => decide (x = a) ^^ decide (x = b)) = k - 1 := by
  sorry

/-- Every nonzero left sign row of level `k` at least `2` has algebraic degree `k - 1`. The Rocq
originals are `sign_row_degree` of `rocq/open/theories/CDPhaseDegree.v` and
`sign_row_degree_is` of `rocq/quantum/CdSignRowAnf.v`, whose left sign row
`sign_row k m x = am_exponent k x m` is `negSign k m x`. -/
theorem anfDegree_negSign_left {k : ℕ} (hk : 2 ≤ k) {m : BitVec k} (hm : m ≠ 0#k) :
    anfDegree (negSign k m) = k - 1 := by
  sorry

/-- The right sign row `x ↦ negSign k x m` has degree `1` when `m` is a power of two and
`max 1 (log2 m - 1)` otherwise. The Rocq original is `right_row_degree` of
`rocq/quantum/CdSignRowAnf.v`. -/
theorem anfDegree_negSign_right {k : ℕ} {m : BitVec k} (hm : m ≠ 0#k) :
    anfDegree (fun x => negSign k x m) =
      if m.toNat = 2 ^ Nat.log2 m.toNat then 1 else max 1 (Nat.log2 m.toNat - 1) := by
  sorry

end Tower

end CayleyDickson
