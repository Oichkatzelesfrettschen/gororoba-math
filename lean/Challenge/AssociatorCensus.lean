/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.AssociatorPhase

/-!
# Challenge: the census of associator phases by degree

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

/-- For `3 ≤ k` and `2 ≤ d ≤ k - 2`, exactly `3 * 2^d * (2^(d+1) - 1)` pairs `0 < p < q < 2^k`
have associator-phase degree `d`. The Rocq original is `census_degree` of
`rocq/quantum/CdAssociatorCensus.v`: by `anfDegree_assocPhase` the degree is `d` exactly when
`log2 q = d + 1`, and `card_pairs_log2` counts those pairs. -/
theorem card_anfDegree_assocPhase_eq {k d : ℕ} (hk : 3 ≤ k) (hd : 2 ≤ d) (hdk : d + 2 ≤ k) :
    (Finset.univ.filter fun pq : BitVec k × BitVec k =>
        0 < pq.1.toNat ∧ pq.1.toNat < pq.2.toNat ∧
          anfDegree (assocPhase pq.1 pq.2) = d).card =
      3 * 2 ^ d * (2 ^ (d + 1) - 1) := by
  sorry

/-- For `3 ≤ k` exactly `21` pairs `0 < p < q < 2^k` have associator-phase degree `1`. The Rocq
original is `census_degree_one` of `rocq/quantum/CdAssociatorCensus.v`: the degree is `1`
exactly when `q < 8`. -/
theorem card_anfDegree_assocPhase_eq_one {k : ℕ} (hk : 3 ≤ k) :
    (Finset.univ.filter fun pq : BitVec k × BitVec k =>
        0 < pq.1.toNat ∧ pq.1.toNat < pq.2.toNat ∧
          anfDegree (assocPhase pq.1 pq.2) = 1).card = 21 := by
  sorry

/-- Twice the sum over all degrees of the number of pairs `0 < p < q < 2^k` of that degree is
`(2^k - 1) (2^k - 2)`, the number of ordered pairs of distinct nonzero indices. The Rocq original is
`census_total` of `rocq/quantum/CdAssociatorCensus.v`. -/
theorem sum_card_anfDegree_assocPhase {k : ℕ} (hk : 3 ≤ k) :
    2 * ∑ d ∈ Finset.range k,
      (Finset.univ.filter fun pq : BitVec k × BitVec k =>
        0 < pq.1.toNat ∧ pq.1.toNat < pq.2.toNat ∧
          anfDegree (assocPhase pq.1 pq.2) = d).card = (2 ^ k - 1) * (2 ^ k - 2) := by
  sorry

section Triples

/-- At order `k + 1` with `n = 2^(k+1)` the number of non-associating ordered basis triples is
`(n - 2) (n - 4) (n + 6) / 2`, stated as twice the count, the denominator-cleared form of
`associator_census_integrality` of `rocq/open/theories/CDAssociatorCensus.v`, from which the
divided formula `associator_census_formula` of the same file follows; there
`associator_phase order l m r` is `assocPhase l m r` (value `168` at the octonions). The proof sums
over the three top bits: by `assocPhase_cons` a triple of the low parts contributes `4` unless its
three pairs are degenerate, in which case it contributes `0`, and `7 * 2^k - 6` triples are of the
second kind (`sum_thin`). -/
theorem card_assocPhase_true (k : ℕ) :
    2 * ((Finset.univ.filter fun t : BitVec (k + 1) × BitVec (k + 1) × BitVec (k + 1) =>
        assocPhase t.1 t.2.1 t.2.2 = true).card : ℤ) =
      (2 ^ (k + 1) - 2) * (2 ^ (k + 1) - 4) * (2 ^ (k + 1) + 6) := by
  sorry

end Triples

end Tower

end CayleyDickson
