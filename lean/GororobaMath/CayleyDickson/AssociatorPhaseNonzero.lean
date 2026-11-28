/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.Alternative
public import GororobaMath.CayleyDickson.AssociatorCensus

/-!
# Basis triples with a nonzero associator

Convention: `Tower R k` and its basis `Tower.e R k p` are those of
`GororobaMath.CayleyDickson.Tower`, the associator is
`associator a b c = (a * b) * c - a * (b * c)` (`Associator.lean`), and
`Tower.assocPhase p q x` is `true` when `e p * (e q * e x)` and `(e p * e q) * e x` carry
opposite signs (`AssociatorPhase.lean`). The results read over every nonassociative ring with
a star in which `2 ≠ 0`.

By `Tower.e_mul_e_mul_e` the associator of three basis elements is twice `(e p * e q) * e x`
when the phase holds and zero otherwise, and `(e p * e q) * e x` is a signed basis element, so
with `2 ≠ 0` the associator is nonzero exactly at the phase-true triples. A triple with an index
`0` holds the identity `e 0 = 1` and has associator zero, so every triple with a nonzero
associator is a triple of imaginary units, and the census `Tower.card_assocPhase_true` counts
the ordered triples of imaginary basis units with a nonzero associator.

## Main results

* `Tower.associator_e_e_e_eq_ite`: the associator of `e p`, `e q`, `e x` is
  `2 • ((e p * e q) * e x)` when `assocPhase p q x` holds and `0` otherwise.
* `Tower.associator_e_e_e_ne_zero_iff`: with `2 ≠ 0`, the associator is nonzero exactly
  when `assocPhase p q x` holds.
* `Tower.ne_zero_of_associator_e_e_e_ne_zero`: a nonzero associator of basis elements has
  three nonzero indices.
* `Tower.card_associator_e_e_e_ne_zero`: at level `k + 1`, with `2 ≠ 0`, twice the number of
  ordered index triples with a nonzero associator is `(D - 2) (D - 4) (D + 6)` for
  `D = 2^(k+1)`, the count of gororoba-quantum's findings row A5-649 over every such ring.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

universe u

variable {R : Type u} [NonAssocRing R] [StarRing R]

/-- The associator of three basis elements is twice `(e p * e q) * e x` at a phase-true triple
and zero at every other triple. -/
theorem associator_e_e_e_eq_ite {k : ℕ} (p q x : BitVec k) :
    associator (e R k p) (e R k q) (e R k x) =
      if assocPhase p q x then (2 : ℤ) • (e R k p * e R k q * e R k x) else 0 := by
  unfold associator
  rw [e_mul_e_mul_e]
  split_ifs
  · rw [sub_neg_eq_add, two_zsmul]
  · exact sub_self _

/-- The product `(e p * e q) * e x` is the basis element of index `p ^^^ q ^^^ x` or its
negative. -/
theorem e_mul_e_mul_e_eq_or_eq_neg {k : ℕ} (p q x : BitVec k) :
    e R k p * e R k q * e R k x = e R k (p ^^^ q ^^^ x) ∨
      e R k p * e R k q * e R k x = -e R k (p ^^^ q ^^^ x) := by
  rw [e_mul_e k p q]
  split_ifs
  · rw [neg_mul, e_mul_e k (p ^^^ q) x]
    split_ifs
    · exact Or.inl (neg_neg _)
    · exact Or.inr rfl
  · rw [e_mul_e k (p ^^^ q) x]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- With `2 ≠ 0`, the associator of three basis elements is nonzero exactly at the phase-true
triples. -/
theorem associator_e_e_e_ne_zero_iff (h2 : (2 : R) ≠ 0) {k : ℕ} (p q x : BitVec k) :
    associator (e R k p) (e R k q) (e R k x) ≠ 0 ↔ assocPhase p q x = true := by
  rw [associator_e_e_e_eq_ite]
  cases hph : assocPhase p q x
  · simp
  · simp only [↓reduceIte, ne_eq, iff_true]
    rcases e_mul_e_mul_e_eq_or_eq_neg (R := R) p q x with h | h
    · rw [h]
      exact two_zsmul_e_ne_zero h2 k _
    · rw [h, smul_neg, neg_eq_zero]
      exact two_zsmul_e_ne_zero h2 k _

/-- A nonzero associator of three basis elements has three nonzero indices: the basis element of
index `0` is the identity. -/
theorem ne_zero_of_associator_e_e_e_ne_zero {k : ℕ} {p q x : BitVec k}
    (h : associator (e R k p) (e R k q) (e R k x) ≠ 0) : p ≠ 0#k ∧ q ≠ 0#k ∧ x ≠ 0#k := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> simp at h

open Classical in
/-- At level `k + 1`, with `2 ≠ 0`, twice the number of ordered index triples whose basis
elements have a nonzero associator is `(D - 2) (D - 4) (D + 6)`, `D = 2^(k+1)`. Each such
triple consists of imaginary units (`ne_zero_of_associator_e_e_e_ne_zero`). -/
theorem card_associator_e_e_e_ne_zero (h2 : (2 : R) ≠ 0) (k : ℕ) :
    2 * ((Finset.univ.filter fun t : BitVec (k + 1) × BitVec (k + 1) × BitVec (k + 1) =>
        associator (e R (k + 1) t.1) (e R (k + 1) t.2.1) (e R (k + 1) t.2.2) ≠ 0).card : ℤ) =
      (2 ^ (k + 1) - 2) * (2 ^ (k + 1) - 4) * (2 ^ (k + 1) + 6) := by
  rw [Finset.filter_congr fun t _ => associator_e_e_e_ne_zero_iff h2 t.1 t.2.1 t.2.2]
  exact card_assocPhase_true k

end Tower

end CayleyDickson
