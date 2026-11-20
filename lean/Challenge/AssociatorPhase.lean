/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AssociatorSpace
public import GororobaMath.CayleyDickson.BooleanAnf
public import GororobaMath.CayleyDickson.SignLaws

/-!
# Challenge: the associator phase of basis elements

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

universe u

/-- `true` when `e p * (e q * e x)` and `(e p * e q) * e x` carry opposite signs. -/
def assocPhase {k : ℕ} (p q x : BitVec k) : Bool := !associates p x q

/-- `true` when `e a * e b` and `e b * e a` carry opposite signs. -/
def commPhase {k : ℕ} (a b : BitVec k) : Bool := negSign k a b ^^ negSign k b a

section Ring

variable {R : Type u} [NonAssocRing R] [StarRing R]

/-- `e p * (e q * e x) = ±(e p * e q) * e x`, negated exactly when
`assocPhase p q x` holds. The Rocq original is `assoc_basis` of
`rocq/quantum/CdAssociatorAnf.v`. -/
theorem e_mul_e_mul_e {k : ℕ} (p q x : BitVec k) :
    e R k p * (e R k q * e R k x) =
      if assocPhase p q x then -(e R k p * e R k q * e R k x)
      else e R k p * e R k q * e R k x := by
  sorry

end Ring

/-- The associator phase at level `k + 1`. The products of two top bits cancel
among the four signs; what remains is the phase of the low parts, the left top
bit times the indicators of the nonzero indices among `m`, `r`, `m ^^^ r`, and the
middle and right top bits times sums of commutation phases. The Rocq original is
`associator_doubling` of `rocq/open/theories/CDAssociatorDoubling.v`. -/
theorem assocPhase_cons {k : ℕ} (L M N : Bool) (l m r : BitVec k) :
    assocPhase (BitVec.cons L l) (BitVec.cons M m) (BitVec.cons N r) =
      (assocPhase l m r ^^
        (L && (decide (m ≠ 0#k) ^^ decide (r ≠ 0#k) ^^ decide (m ^^^ r ≠ 0#k))) ^^
        (M && (commPhase l m ^^ commPhase l (m ^^^ r))) ^^
        (N && (commPhase (l ^^^ m) r ^^ commPhase m r ^^ commPhase l (m ^^^ r)))) := by
  sorry

/-- A basis triple with a zero member, a repeated member or `r = l ^^^ m` associates: the
associator phase vanishes. The Rocq original is `dependent_basis_triple_associates` of
`rocq/open/theories/CDAssociatorCensus.v`, whose `associator_phase` is `assocPhase l m r`
through `cube_encode`. -/
theorem assocPhase_eq_false_of_dependent {k : ℕ} {l m r : BitVec k}
    (h : l = 0#k ∨ m = 0#k ∨ r = 0#k ∨ l = m ∨ l = r ∨ m = r ∨ l ^^^ m = r) :
    assocPhase l m r = false := by
  sorry

/-- The associator phase vanishes when `p = 0`, `q = 0` or `p = q`. The Rocq original is
`assoc_degenerate` of `rocq/quantum/CdAssociatorAnf.v`. -/
theorem assocPhase_eq_false_of_degenerate {k : ℕ} {p q : BitVec k}
    (h : p = 0#k ∨ q = 0#k ∨ p = q) (x : BitVec k) : assocPhase p q x = false := by
  sorry

/-- Every basis triple of the quaternions associates. The Rocq original is
`quaternion_associator_all` of `rocq/open/theories/CDPhaseDegree.v`. -/
theorem assocPhase_two (p q x : BitVec 2) : assocPhase p q x = false := by
  sorry

/-- For distinct nonzero `l` and `r` the pair coefficient is `1`. The Rocq original is
`independent_pair_coefficient` of `rocq/open/theories/CDAssociatorDoubling.v`. -/
theorem pairCoeff_eq_true {k : ℕ} {l r : BitVec k} (hl : l ≠ 0#k) (hr : r ≠ 0#k) (hlr : l ≠ r) :
    (decide (l ≠ 0#k) ^^ decide (r ≠ 0#k) ^^ decide (l ^^^ r ≠ 0#k)) = true := by
  sorry

section Degree

end Degree

section DegreeSteps

end DegreeSteps

/-- For `k ≥ 3` and distinct nonzero `p`, `q` the associator phase has algebraic degree
`max 1 (bitlen (max p q) - 2)`, independent of `k`, where `bitlen n - 2 = Nat.log2 n - 1` for
`n ≥ 1`. The Rocq originals are `assoc_degree_is` of `rocq/quantum/CdAssociatorAnf.v` (row 87)
and `associator_phase_degree` of `rocq/open/theories/CDPhaseDegree.v` (row 88), the second with
the same statement in the open tree's vocabulary; the first reads
(`degree_is k (assoc k p q) (assoc_degree p q)`, whose `assoc k p q x` is `assocPhase` at
`p.toNat`, `q.toNat`, `x.toNat`). The proof inducts on the level: a pair in the low half keeps the
degree of the level below, since the top bit of `x` adds a constant; a pair reaching the top
half adds two distinct point indicators, of degree `k - 2`, to the phase of the low parts, whose
degree is at most `k - 3`. -/
theorem anfDegree_assocPhase {k : ℕ} (hk : 3 ≤ k) {p q : BitVec k} (hp : p ≠ 0#k) (hq : q ≠ 0#k)
    (hpq : p ≠ q) :
    anfDegree (assocPhase p q) = max 1 (Nat.log2 (max p.toNat q.toNat) - 1) := by
  sorry

/-- For `i = 2^(n-1) + m` and `j = i + 2^(n-2)` the associator phase is a point indicator in
`x mod 2^(n-2)`, plus the top bit of `x` when `m` is nonzero. The Rocq original is
`point_indicator_pairs` of `rocq/quantum/CdAssociatorPointIndicators.v`. The proof writes both
indices as top bits over `μ`, applies `assocPhase_cons` twice, and the degenerate phase
`assocPhase μ μ _ = false` removes the low part. -/
theorem assocPhase_point_pair {n m : ℕ} (hn : 3 ≤ n) (hm : m < 2 ^ (n - 2)) (x : BitVec n) :
    assocPhase (BitVec.ofNat n (2 ^ (n - 1) + m)) (BitVec.ofNat n (2 ^ (n - 1) + m + 2 ^ (n - 2)))
        x =
      if m = 0 then decide (x.toNat % 2 ^ (n - 2) ≠ 0)
      else (x.msb ^^ decide (x.toNat % 2 ^ (n - 2) = m)) := by
  sorry

end Tower

end CayleyDickson
