/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.KernelMap.Estimator

/-!
# Block readings of the kernel-map nullity estimator

Convention: the bins, the observed contrast `c`, the classes `posBins` and `negBins`, the
estimator `nHat`, the mean `vHat`, the class means `vBarPos` and `vBarNeg` and the exact value
`nullity = (|B+| - |B-|) / 2` are those of `GororobaMath.KernelMap.Estimator`, over a field of
characteristic zero.

The bias identity `KernelMap.nHat_sub_nullity` carries the factor `|B+| |B-| / |B|`. The class
sizes are `|B| / 2 + nullity` and `|B| / 2 - nullity`, so the factor is
`(|B|^2 - (2 nullity)^2) / (4 |B|)`: `(16 - N^2) / 8` on a block of 8 bins and
`(256 - N^2) / 32` on the map of 32 bins, the two block readings of row A5-228 of the findings
ledger of gororoba-quantum (`docs/evidence/a5-exceptional-fibers/ledger.tsv`). Row A5-229 reads
the two forced blocks: `KernelMap.nHat_eq_card_div_two_of_negBins_eq_empty` is the block with
`B-` empty, and the block with `B+` empty is here.

## Main results

* `KernelMap.card_posBins_mul_card_negBins`: `|B+| |B-| = (|B|^2 - (2 nullity)^2) / 4`.
* `KernelMap.nHat_sub_nullity_of_card_eq_eight`, `KernelMap.nHat_sub_nullity_of_card_eq_thirtyTwo`:
  the bias on 8 and on 32 bins.
* `KernelMap.nHat_eq_nullity_iff`: with both classes inhabited and `vHat ≠ 0`, the estimator is
  exact exactly when the two class means agree.
* `KernelMap.nHat_eq_neg_card_div_two_of_posBins_eq_empty`: a block with no bin of ideal contrast
  `+1` reads `-|B| / 2` on every contrast with `vHat ≠ 0`.
-/

@[expose] public section

namespace KernelMap

variable {K : Type*} [Field K] [CharZero K]

variable {ι : Type*} (B : Finset ι) (c : ι → K) (pos : ι → Prop) [DecidablePred pos]

/-- The product of the class sizes in the block size and the nullity. -/
theorem card_posBins_mul_card_negBins :
    ((posBins B pos).card : K) * (negBins B pos).card =
      ((B.card : K) ^ 2 - (2 * nullity B pos) ^ 2) / 4 := by
  rw [nullity, card_eq_posBins_add_negBins B pos]
  ring

/-- The bias identity with its scale written in the block size and the nullity. -/
theorem nHat_sub_nullity_card (hV : vHat B c pos ≠ 0) :
    nHat B c pos - nullity B pos =
      ((B.card : K) ^ 2 - (2 * nullity B pos) ^ 2) / 4 / B.card *
        (vBarPos B c pos - vBarNeg B c pos) / vHat B c pos := by
  rw [nHat_sub_nullity B c pos hV, card_posBins_mul_card_negBins]

/-- The bias of a block of 8 bins of nullity `N` is `(16 - N^2) / 8` times the class gap over
`vHat`. -/
theorem nHat_sub_nullity_of_card_eq_eight (hV : vHat B c pos ≠ 0) (h8 : B.card = 8) :
    nHat B c pos - nullity B pos =
      (16 - nullity B pos ^ 2) / 8 * (vBarPos B c pos - vBarNeg B c pos) / vHat B c pos := by
  rw [nHat_sub_nullity_card B c pos hV, h8]
  push_cast
  ring

/-- The bias of the map of 32 bins of nullity `N` is `(256 - N^2) / 32` times the class gap over
`vHat`. -/
theorem nHat_sub_nullity_of_card_eq_thirtyTwo (hV : vHat B c pos ≠ 0) (h32 : B.card = 32) :
    nHat B c pos - nullity B pos =
      (256 - nullity B pos ^ 2) / 32 * (vBarPos B c pos - vBarNeg B c pos) / vHat B c pos := by
  rw [nHat_sub_nullity_card B c pos hV, h32]
  push_cast
  ring

/-- With a bin in each class and `vHat ≠ 0`, the estimator equals the nullity exactly when the
class means agree. -/
theorem nHat_eq_nullity_iff (hV : vHat B c pos ≠ 0) (hp : (posBins B pos).Nonempty)
    (hn : (negBins B pos).Nonempty) :
    nHat B c pos = nullity B pos ↔ vBarPos B c pos = vBarNeg B c pos := by
  have ha : ((posBins B pos).card : K) ≠ 0 := Nat.cast_ne_zero.mpr hp.card_ne_zero
  have hb : ((negBins B pos).card : K) ≠ 0 := Nat.cast_ne_zero.mpr hn.card_ne_zero
  have hB : (B.card : K) ≠ 0 := by
    rw [card_eq_posBins_add_negBins B pos, ← Nat.cast_add]
    exact Nat.cast_ne_zero.mpr (Nat.add_pos_left hp.card_pos _).ne'
  rw [← sub_eq_zero, nHat_sub_nullity B c pos hV, ← sub_eq_zero (a := vBarPos B c pos)]
  simp [ha, hb, hB, hV]

/-- A block whose bins all carry ideal contrast `-1` reads its nullity on every contrast with
`vHat ≠ 0`. -/
theorem nHat_eq_nullity_of_posBins_eq_empty (hV : vHat B c pos ≠ 0)
    (hpos : posBins B pos = ∅) : nHat B c pos = nullity B pos := by
  have h := nHat_sub_nullity B c pos hV
  rw [hpos] at h
  simpa [sub_eq_zero] using h

/-- The forced reading of a block with no bin of ideal contrast `+1`: `-|B| / 2`. -/
theorem nHat_eq_neg_card_div_two_of_posBins_eq_empty (hV : vHat B c pos ≠ 0)
    (hpos : posBins B pos = ∅) : nHat B c pos = -(B.card : K) / 2 := by
  rw [nHat_eq_nullity_of_posBins_eq_empty B c pos hV hpos, nullity,
    card_eq_posBins_add_negBins B pos, hpos]
  simp

end KernelMap
