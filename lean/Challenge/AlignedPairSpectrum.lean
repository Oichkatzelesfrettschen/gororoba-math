/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TwoTermRecursion

/-!
# Challenge: the spectrum and the mirror of the aligned-pair count

This file restates, with `sorry` as each proof, the headline theorems that
`GororobaMath.CayleyDickson.AlignedPairSpectrum` proves and that the "Lean library" table of `README.md` names, together
with the definitions that `GororobaMath.CayleyDickson.AlignedPairSpectrum` introduces and those statements use.
It imports the library modules that the solution module itself imports, so the
earlier definitions (`Tower`, `negSign`, `alignedPairCount`, ...) are the
library's own; a restated definition copies the solution's text and must
elaborate to the same constant. `lake comparator --config` with the JSON file
beside this one checks that each named theorem of the solution module has the
statement written here and depends only on `propext`, `Classical.choice` and
`Quot.sound`. No library module imports this file, and the admission gate does
not build it.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

/-- **Bound.** From `k = 3` on every count satisfies
`N k i j + 4 ≤ 2 ^ (k - 1)`, the value `0` included. -/
theorem alignedPairCount_add_four_le_of_three_le {k : ℕ} (hk : 3 ≤ k) (i j : BitVec k) :
    alignedPairCount k i j + 4 ≤ 2 ^ (k - 1) := by
  sorry

/-- **Every value occurs.** Every multiple `4 v` with `4 v + 4 ≤ 2 ^ (k - 1)` is
the count of a pair of nonzero distinct indices, at every level `k` (the
hypothesis has no solution for `k ≤ 2`). -/
theorem exists_alignedPairCount_eq :
    ∀ (k v : ℕ), 4 * v + 4 ≤ 2 ^ (k - 1) →
      ∃ i j : BitVec k, i ≠ 0#k ∧ j ≠ 0#k ∧ i ≠ j ∧ alignedPairCount k i j = 4 * v := by
  sorry

/-- **Spectrum.** For `k ≥ 3` the counts of all pairs are exactly the
multiples of `4` from `0` to `2 ^ (k - 1) - 4`. -/
theorem range_alignedPairCount {k : ℕ} (hk : 3 ≤ k) :
    Set.range (fun p : BitVec k × BitVec k => alignedPairCount k p.1 p.2) =
      {n | 4 ∣ n ∧ n + 4 ≤ 2 ^ (k - 1)} := by
  sorry

/-- Moving the second term of the operand to the other half of level
`k + 1` mirrors a nonzero count about `2 ^ k - 4`. -/
theorem alignedPairCount_add_flip {k : ℕ} (i j : BitVec (k + 1))
    (h : alignedPairCount (k + 1) i j ≠ 0) :
    alignedPairCount (k + 1) i j + alignedPairCount (k + 1) i (j ^^^ BitVec.cons true 0#k) + 4 =
      2 ^ k := by
  sorry

/-- The number of ordered pairs of indices at level `k` whose count is `n`. -/
def alignedPairCountMultiplicity (k n : ℕ) : ℕ :=
  (Finset.univ.filter fun p : BitVec k × BitVec k => alignedPairCount k p.1 p.2 = n).card

/-- **Mirror of multiplicities.** For `0 < n` and `n + 4 < 2 ^ (k - 1)`, as many
ordered pairs have count `n` as have count `2 ^ (k - 1) - 4 - n`. -/
theorem multiplicity_mirror (k n : ℕ) (hn : n ≠ 0) (hn' : n + 4 < 2 ^ (k - 1)) :
    alignedPairCountMultiplicity k n = alignedPairCountMultiplicity k (2 ^ (k - 1) - 4 - n) := by
  sorry

end Tower

end CayleyDickson
