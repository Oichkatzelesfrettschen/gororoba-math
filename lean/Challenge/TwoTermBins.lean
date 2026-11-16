/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TwoTermRecursion
public import GororobaMath.KernelMap.Estimator

/-!
# Challenge: the exact nullity of a two-term kernel map

This file restates, with `sorry` as each proof, the headline theorems that
`GororobaMath.KernelMap.TwoTermBins` proves and that the "Lean library" table of `README.md` names, together
with the definitions that `GororobaMath.KernelMap.TwoTermBins` introduces and those statements use.
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

namespace KernelMap

open CayleyDickson.Tower

variable {K : Type*} [Field K] [CharZero K]

/-- **Exact nullity of a two-term kernel map.** If every index of an aligned
pair of `e i + e j` is a `+1` bin and every misaligned pair holds one `+1`
bin and one `-1` bin, the exact nullity of the block of all `2 ^ k` bins is
the aligned-pair count. -/
theorem nullity_eq_alignedPairCount {k : ℕ} {i j : BitVec k} (hij : i ≠ j)
    (pos : BitVec k → Prop) [DecidablePred pos]
    (hal : ∀ x, misaligned k i j x = false → pos x)
    (hmis : ∀ x, misaligned k i j x = true → (pos (partner i j x) ↔ ¬pos x)) :
    nullity (K := K) Finset.univ pos = alignedPairCount k i j := by
  sorry

/-- The bin contract of `nullity_eq_alignedPairCount` as a Boolean on a
labelling `pos` of the bins: an index of an aligned pair is a `+1` bin, and
the two indices of a misaligned pair carry different labels. -/
def binContract (k : ℕ) (i j : BitVec k) (pos : BitVec k → Bool) : Bool :=
  decide (∀ x : BitVec k,
    if misaligned k i j x then pos (partner i j x) ≠ pos x else pos x = true)

/-- **Exact nullity from the Boolean bin contract.** A labelling for which
`binContract` evaluates to `true` has exact nullity `alignedPairCount k i j`. -/
theorem nullity_eq_alignedPairCount_of_binContract {k : ℕ} {i j : BitVec k} (hij : i ≠ j)
    (pos : BitVec k → Bool) (h : binContract k i j pos = true) :
    nullity (K := K) Finset.univ (fun x => pos x = true) = alignedPairCount k i j := by
  sorry

end KernelMap
