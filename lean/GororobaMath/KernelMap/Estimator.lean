/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib

/-!
# The kernel-map nullity estimator

gororoba-quantum reads the nullity of a left-multiplication operator of
`A_5` on hardware from a contrast `c y` over output bins `y`
(`docs/evidence/pathion-kernel-map/nhat-bias/README.md`, with the code in
`pathion_kernel_map._pair_summary`, compared with the definitions below by
`ci/compare_estimator.sh`). Every bin carries an ideal contrast
`+1` or `-1`; the bins of ideal contrast `+1` are `posBins`, the others
`negBins`. The estimator is

  `vHat = (∑ y, c y * ideal y) / |B|`,  `nHat = (∑ y, c y / 2) / vHat`,

against the exact value `nullity = (|B+| - |B-|) / 2`.

## Main results

* `KernelMap.nHat_sub_nullity`: the bias identity
  `nHat - nullity = |B+| |B-| / |B| * (vBarPos - vBarNeg) / vHat`, for any
  contrast whatever with `vHat ≠ 0`. The estimator is exact when the mean
  contrast on the two classes of bins agrees, and its error is the class gap
  scaled by `|B+| |B-| / (|B| vHat)`.
* `KernelMap.nHat_eq_nullity_of_negBins_eq_empty`: a block with no bin of
  ideal contrast `-1` reads `nHat = |B+| / 2` on every device, whatever the
  noise, as long as `vHat ≠ 0`. With eight bins this is the reading `4`.

The statements hold over any field of characteristic zero: the rationals
for the exact replay of retained counts, the reals for a noise model. They
cover a block in which every bin is decided (ideal contrast `+1` or `-1`)
and take `vHat ≠ 0` exactly; `_pair_summary` reports no estimate when
`|vHat| ≤ 1e-9`, a guard on floating-point division that the theorems
leave to the caller.
-/

@[expose] public section

namespace KernelMap

variable {K : Type*} [Field K] [CharZero K]

/-- The bias identity on the five numbers it depends on: `a = |B+|`,
`b = |B-|`, `u` and `v` the class means. -/
theorem nHat_sub_nullity_scalar (a b u v : K) (hn : a + b ≠ 0) (hV : a * u + b * v ≠ 0) :
    (a * u - b * v) / 2 / ((a * u + b * v) / (a + b)) - (a - b) / 2 =
      a * b / (a + b) * (u - v) / ((a * u + b * v) / (a + b)) := by
  field_simp
  ring

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

theorem card_mul_vBarPos :
    ((posBins B pos).card : K) * vBarPos B c pos = ∑ y ∈ posBins B pos, c y := by
  unfold vBarPos
  rcases Finset.eq_empty_or_nonempty (posBins B pos) with h | h
  · simp [h]
  · have hc : ((posBins B pos).card : K) ≠ 0 := Nat.cast_ne_zero.mpr h.card_ne_zero
    field_simp

theorem card_mul_vBarNeg :
    ((negBins B pos).card : K) * vBarNeg B c pos = -∑ y ∈ negBins B pos, c y := by
  unfold vBarNeg
  rw [Finset.sum_neg_distrib]
  rcases Finset.eq_empty_or_nonempty (negBins B pos) with h | h
  · simp [h]
  · have hc : ((negBins B pos).card : K) ≠ 0 := Nat.cast_ne_zero.mpr h.card_ne_zero
    field_simp

omit [CharZero K] in
theorem sum_eq_posBins_add_negBins :
    ∑ y ∈ B, c y = ∑ y ∈ posBins B pos, c y + ∑ y ∈ negBins B pos, c y :=
  (Finset.sum_filter_add_sum_filter_not B pos c).symm

omit [CharZero K] in
theorem signed_sum_eq_posBins_sub_negBins :
    (∑ y ∈ B, c y * if pos y then 1 else -1) =
      ∑ y ∈ posBins B pos, c y - ∑ y ∈ negBins B pos, c y := by
  rw [← Finset.sum_filter_add_sum_filter_not B pos, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun y hy => by simp [(Finset.mem_filter.1 hy).2]
  · exact Finset.sum_congr rfl fun y hy => by simp [(Finset.mem_filter.1 hy).2]

omit [CharZero K] in
theorem card_eq_posBins_add_negBins :
    (B.card : K) = (posBins B pos).card + (negBins B pos).card := by
  rw [← Nat.cast_add, posBins, negBins, Finset.card_filter_add_card_filter_not]

/-- The observed contrast against the ideal sign, in the class sizes and
class means. -/
theorem vHat_eq :
    vHat B c pos =
      ((posBins B pos).card * vBarPos B c pos + (negBins B pos).card * vBarNeg B c pos) /
        ((posBins B pos).card + (negBins B pos).card) := by
  rw [vHat, signed_sum_eq_posBins_sub_negBins, card_eq_posBins_add_negBins B pos,
    card_mul_vBarPos, card_mul_vBarNeg, sub_eq_add_neg]

/-- **Bias identity of the nullity estimator.** For every observed contrast
with `vHat ≠ 0`, the estimator misses the nullity by the class gap
`vBarPos - vBarNeg` scaled by `|B+| |B-| / (|B| vHat)`. No assumption on the
noise enters. -/
theorem nHat_sub_nullity (hV : vHat B c pos ≠ 0) :
    nHat B c pos - nullity B pos =
      (posBins B pos).card * (negBins B pos).card / B.card *
        (vBarPos B c pos - vBarNeg B c pos) / vHat B c pos := by
  have hV' := hV
  rw [vHat_eq] at hV'
  have hn : ((posBins B pos).card : K) + (negBins B pos).card ≠ 0 := fun h =>
    hV' (by rw [h, div_zero])
  have hS : ((posBins B pos).card : K) * vBarPos B c pos +
      (negBins B pos).card * vBarNeg B c pos ≠ 0 := fun h => hV' (by rw [h, zero_div])
  have key := nHat_sub_nullity_scalar ((posBins B pos).card : K) (negBins B pos).card
    (vBarPos B c pos) (vBarNeg B c pos) hn hS
  rw [nHat, nullity, vHat_eq, sum_eq_posBins_add_negBins B c pos,
    card_eq_posBins_add_negBins B pos, ← card_mul_vBarPos, ← neg_neg (∑ y ∈ negBins B pos, c y),
    ← card_mul_vBarNeg, ← sub_eq_add_neg]
  exact key

/-- **Forced reading.** A block whose bins all carry ideal contrast `+1`
reads its nullity exactly on every device with `vHat ≠ 0`: the estimator
divides the contrast sum by its own mean. -/
theorem nHat_eq_nullity_of_negBins_eq_empty (hV : vHat B c pos ≠ 0)
    (hneg : negBins B pos = ∅) : nHat B c pos = nullity B pos := by
  have h := nHat_sub_nullity B c pos hV
  rw [hneg] at h
  simpa [sub_eq_zero] using h

/-- The forced reading in the block's own count: `|B| / 2`, which is `4` for
a block of eight bins. -/
theorem nHat_eq_card_div_two_of_negBins_eq_empty (hV : vHat B c pos ≠ 0)
    (hneg : negBins B pos = ∅) : nHat B c pos = B.card / 2 := by
  rw [nHat_eq_nullity_of_negBins_eq_empty B c pos hV hneg, nullity,
    card_eq_posBins_add_negBins B pos, hneg]
  simp

end KernelMap
