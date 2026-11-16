/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TwoTermRecursion

/-!
# Challenge: the closed form of the aligned-pair count

This file restates, with `sorry` as each proof, the headline theorems that
`GororobaMath.CayleyDickson.AlignedPairClosedForm` proves and that the "Lean library" table of `README.md` names, together
with the definitions that `GororobaMath.CayleyDickson.AlignedPairClosedForm` introduces and those statements use.
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

/-- The split of `(i, j)` at bit `p` is degenerate: bit `p` of `i` and of
`j` differ, and below bit `p` the index `i` is zero, `j` is zero, or the
two agree. -/
def DegenerateSplit {k : ℕ} (i j : BitVec k) (p : ℕ) : Prop :=
  i.getLsbD p ≠ j.getLsbD p ∧
    ((∀ s < p, i.getLsbD s = false) ∨ (∀ s < p, j.getLsbD s = false) ∨
      ∀ s < p, i.getLsbD s = j.getLsbD s)

instance {k : ℕ} (i j : BitVec k) : DecidablePred (DegenerateSplit i j) := fun p => by
  unfold DegenerateSplit
  infer_instance

/-- Bit `s` of `m'`: bit `s` of `i ^^^ j`, kept when every degenerate split
lies below position `s`. -/
def clearedXorBit {k : ℕ} (i j : BitVec k) (s : ℕ) : Bool :=
  (i.getLsbD s ^^ j.getLsbD s) && decide (∀ p < k, DegenerateSplit i j p → p < s)

/-- The parity of the set bits of `m'` at positions `t` to `k - 1`. -/
def clearedXorParity {k : ℕ} (i j : BitVec k) (t : ℕ) : ℕ :=
  (∑ s ∈ Finset.Ico t k, (clearedXorBit i j s).toNat) % 2

/-- The closed form `4 * ∑ t ∈ [3, k), 2 ^ (k - 1 - t) * parity t`. -/
def closedForm (k : ℕ) (i j : BitVec k) : ℕ :=
  4 * ∑ t ∈ Finset.Ico 3 k, 2 ^ (k - 1 - t) * clearedXorParity i j t

/-- **Closed form of the aligned-pair count.** At every level and for all
indices, `alignedPairCount k i j` is `4 * ∑ t ∈ [3, k), 2 ^ (k - 1 - t) * parity t`,
with `parity t` the parity of `m' >>> t` and `m'` the exclusive or of the
indices with every bit at or below the highest degenerate split cleared. -/
theorem alignedPairCount_eq_closedForm : ∀ (k : ℕ) (i j : BitVec k),
    alignedPairCount k i j = closedForm k i j := by
  sorry

end Tower

end CayleyDickson
