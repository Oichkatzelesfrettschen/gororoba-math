/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib

/-!
# Challenge: the bias of the kernel-map nullity estimator

This file restates, with `sorry` as each proof, the headline theorems that
`GororobaMath.KernelMap.Estimator` proves and that the "Lean library" table of `README.md` names, together with the definitions that
`GororobaMath.KernelMap.Estimator` introduces and those statements use.
The solution module imports only Mathlib, so this file restates every such definition; each copies the
solution's text and elaborates to the same constant.
`lake comparator --config` with the JSON file beside this one checks that each named theorem of the
solution module has the statement written here and depends only on `propext`, `Classical.choice` and
`Quot.sound`. No library module imports this file, and the admission gate does not build it.
-/

@[expose] public section

namespace KernelMap

variable {K : Type*} [Field K] [CharZero K]

variable {ι : Type*} (B : Finset ι) (c : ι → K) (pos : ι → Prop) [DecidablePred pos]

/-- The bins of ideal contrast `+1`. -/
def posBins : Finset ι := B.filter pos

/-- The bins of ideal contrast `-1`. -/
def negBins : Finset ι := B.filter fun y => ¬pos y

/-- The mean of the observed contrast against the ideal sign. -/
def vHat : K := (∑ y ∈ B, c y * if pos y then 1 else -1) / B.card

/-- The nullity estimator. -/
def nHat : K := (∑ y ∈ B, c y) / 2 / vHat B c pos

/-- The exact nullity of the block: half the excess of `+1` bins. -/
def nullity : K := (((posBins B pos).card : K) - (negBins B pos).card) / 2

/-- The mean observed contrast over the `+1` bins. -/
def vBarPos : K := (∑ y ∈ posBins B pos, c y) / (posBins B pos).card

/-- The mean of the negated observed contrast over the `-1` bins. -/
def vBarNeg : K := (∑ y ∈ negBins B pos, -c y) / (negBins B pos).card

/-- **Bias identity of the nullity estimator.** For every observed contrast
with `vHat ≠ 0`, the estimator misses the nullity by the class gap
`vBarPos - vBarNeg` scaled by `|B+| |B-| / (|B| vHat)`. No assumption on the
noise enters. -/
theorem nHat_sub_nullity (hV : vHat B c pos ≠ 0) :
    nHat B c pos - nullity B pos =
      (posBins B pos).card * (negBins B pos).card / B.card *
        (vBarPos B c pos - vBarNeg B c pos) / vHat B c pos := by
  sorry

/-- The forced reading in the block's own count: `|B| / 2`, which is `4` for
a block of eight bins. -/
theorem nHat_eq_card_div_two_of_negBins_eq_empty (hV : vHat B c pos ≠ 0)
    (hneg : negBins B pos = ∅) : nHat B c pos = B.card / 2 := by
  sorry

end KernelMap
