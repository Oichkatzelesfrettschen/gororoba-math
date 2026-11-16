/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TwoTermNullity

/-!
# Challenge: the recursion of the aligned-pair count on the top bit

This file restates, with `sorry` as each proof, the headline theorems that
`GororobaMath.CayleyDickson.TwoTermRecursion` proves and that the "Lean library" table of `README.md` names.
The solution module introduces definitions (`misaligned`, `alignedCount`, `consEquiv`) that these
statements do not use.
This file imports the library module that the solution module itself imports, so `partner` and
`alignedPairCount` are the library's own.
`lake comparator --config` with the JSON file beside this one checks that each named theorem of the
solution module has the statement written here and depends only on `propext`, `Classical.choice` and
`Quot.sound`. No library module imports this file, and the admission gate does not build it.
-/

@[expose] public section

namespace CayleyDickson

namespace Tower

/-- For `i` and `j` in the same half, the aligned-pair count of level
`k + 1` is twice that of the low parts. -/
theorem alignedPairCount_succ_of_msb_eq {k : ℕ} {i j : BitVec (k + 1)} (h : i.msb = j.msb) :
    alignedPairCount (k + 1) i j = 2 * alignedPairCount k (i.setWidth k) (j.setWidth k) := by
  sorry

/-- For `i` and `j` in different halves with low parts `a = 0`, `b = 0` or
`a = b`, the operand has no aligned pair. -/
theorem alignedPairCount_succ_eq_zero {k : ℕ} {i j : BitVec (k + 1)} (h : i.msb ≠ j.msb)
    (hd : i.setWidth k = 0#k ∨ j.setWidth k = 0#k ∨ i.setWidth k = j.setWidth k) :
    alignedPairCount (k + 1) i j = 0 := by
  sorry

/-- For `i` and `j` in different halves with nonzero distinct low parts
`a` and `b`, the aligned-pair counts of the two levels satisfy
`N (k + 1) i j + 2 * N k a b + 4 = 2 ^ k`. -/
theorem alignedPairCount_succ_add {k : ℕ} {i j : BitVec (k + 1)} (h : i.msb ≠ j.msb)
    (ha : i.setWidth k ≠ 0#k) (hb : j.setWidth k ≠ 0#k) (hab : i.setWidth k ≠ j.setWidth k) :
    alignedPairCount (k + 1) i j + 2 * alignedPairCount k (i.setWidth k) (j.setWidth k) + 4 =
      2 ^ k := by
  sorry

end Tower

end CayleyDickson
