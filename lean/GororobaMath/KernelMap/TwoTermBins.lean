/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.CayleyDickson.TwoTermRecursion
public import GororobaMath.KernelMap.Estimator

/-!
# The exact nullity of a two-term kernel map and the aligned-pair count

`KernelMap.nullity B pos` is half the excess of bins of ideal contrast `+1`
over bins of ideal contrast `-1`. For the kernel map of the operand
`e i + e j` at level `k` the bins are the `2 ^ k` output basis states,
indexed here by `BitVec k` with the index convention of
`GororobaMath.CayleyDickson.Tower` (top bit outermost; gororoba-quantum
puts algebra index bit `b` on qubit `b`). The module docstring of
`gororoba_quantum/pathion_kernel_map.py` states the bin contract of the
ideal circuit: the contrast is `+1` at both outputs of an aligned pair and
`+1` at one, `-1` at the other output of a misaligned pair.

`KernelMap.nullity_eq_alignedPairCount` proves that every labelling of the
bins that meets this contract has exact nullity `alignedPairCount k i j`.
The contract is a hypothesis: no definition here mirrors the circuit or
`output_contrast`. `ci/compare_kernel_map_bins.sh` evaluates
`KernelMap.binContract` at level `5` on the ideal output contrast of
`kernel_map_circuit` of `pathion_kernel_map` in gororoba-quantum, with output bin `y` read as index
`y`, for every operand `e i + t e j` with `i ≠ j` and `t = ±1`; a run that
returns `true` for an operand gives its exact nullity through
`KernelMap.nullity_eq_alignedPairCount_of_binContract`. The comparison
rejects the member `kmap_flip3_e1pe18` and a contrast with one bin negated.

## Main results

* `KernelMap.nullity_eq_alignedPairCount`: under the bin contract,
  `nullity univ pos = alignedPairCount k i j` over every field of
  characteristic zero.
* `KernelMap.binContract`, `KernelMap.nullity_eq_alignedPairCount_of_binContract`:
  the contract as a decidable Boolean on a labelling `pos : BitVec k → Bool`,
  the form that `ci/compare_kernel_map_bins.sh` evaluates, and the same
  conclusion from `binContract k i j pos = true`.
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
  set Mp := Finset.univ.filter fun x => misaligned k i j x = true ∧ pos x
  set Mn := Finset.univ.filter fun x => misaligned k i j x = true ∧ ¬pos x
  have hbij : Mp.card = Mn.card := by
    refine Finset.card_bij' (fun x _ => partner i j x) (fun x _ => partner i j x) ?_ ?_
      (fun x _ => partner_partner i j x) (fun x _ => partner_partner i j x)
    · intro x hx
      simp only [Mp, Mn, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [misaligned_partner]
      exact ⟨hx.1, fun h => (hmis x hx.1).1 h hx.2⟩
    · intro x hx
      simp only [Mp, Mn, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [misaligned_partner]
      exact ⟨hx.1, (hmis x hx.1).2 hx.2⟩
  have hpos : (posBins Finset.univ pos).card = alignedCount k i j + Mp.card := by
    unfold posBins alignedCount
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [Mp, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      cases h : misaligned k i j x
      · simp [hal x h]
      · simp
    · rw [Finset.disjoint_filter]
      intro x _ h1 h2
      rw [h1] at h2
      exact Bool.false_ne_true h2.1
  have hneg : (negBins Finset.univ pos).card = Mn.card := by
    unfold negBins
    congr 1
    ext x
    simp only [Mn, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      refine ⟨?_, h⟩
      cases hm : misaligned k i j x
      · exact absurd (hal x hm) h
      · rfl
    · exact fun h => h.2
  rw [nullity, hpos, hneg, alignedCount_eq_two_mul hij, hbij]
  push_cast
  ring

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
  have hc := of_decide_eq_true h
  refine nullity_eq_alignedPairCount hij _ (fun x hx => ?_) (fun x hx => ?_)
  · have hx' := hc x
    rw [hx] at hx'
    simpa using hx'
  · have hx' := hc x
    rw [hx] at hx'
    simp only [↓reduceIte] at hx'
    cases hp : pos x <;> cases hq : pos (partner i j x) <;> simp_all

end KernelMap
