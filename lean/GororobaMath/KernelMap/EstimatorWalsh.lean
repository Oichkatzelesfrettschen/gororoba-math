/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib
public import GororobaMath.KernelMap.Estimator

/-!
# The nullity estimator in a character basis

Convention. A block `B` of output bins carries a finite family of
characters `χ a : ι → K`, indexed by `a : A`, with a distinguished index
`a₀` whose character is `1` on `B`. The family is orthogonal for the sum
over `B`: `∑ y ∈ B, χ a y * χ b y = n` when `a = b` and `0` otherwise, with
`n = |B|` read in `K`. The coefficient of a function `f` is
`coeff f a = (∑ y ∈ B, f y * χ a y) / n`. The ideal contrast is
`sgn pos y = if pos y then 1 else -1`, the sign of the estimator of
`GororobaMath.KernelMap.Estimator`. A function expanded as
`f y = ∑ a, γ a * χ a y` on `B` has coefficients `γ a`. A channel is
diagonal on the characters when `γ a = lam a * σ a`, where `σ` expands
`sgn pos` and `γ` expands the observed contrast.

The Walsh characters of `Fin d → Bool` form such a family
(`KernelMap.walshChar`), and every statement below is stated for an
abstract family, so no Fourier library is needed.

## Main results

* `KernelMap.nullity_eq_card_mul_coeff`: `nullity = n * coeff (sgn pos) a₀ / 2`.
* `KernelMap.vHat_eq_sum_mul`: Plancherel, `vHat = ∑ a, γ a * σ a` for
  `n ≠ 0`.
* `KernelMap.sum_sq_eq_one`: the weights `σ a ^ 2` of the ideal sum to `1`.
* `KernelMap.nHat_eq_card_mul_div`: `nHat = n * γ a₀ / (2 * vHat)`, with no
  hypothesis on `n`, `vHat` or the channel.
* `KernelMap.nHat_eq_spectral`: under a diagonal channel,
  `nHat = nullity * lam a₀ / ∑ a, σ a ^ 2 * lam a`.
* `KernelMap.nHat_eq_nullity_of_support_eq_single` and
  `KernelMap.nHat_eq_zero_of_coeff_zero`: an ideal on the single character
  `a₀` is read exactly, and an ideal with no `a₀` component reads `0`.
* `KernelMap.walshChar_orthogonal`: the Walsh characters satisfy the
  orthogonality hypothesis for every `d`.
-/

@[expose] public section

namespace KernelMap

variable {K : Type*} [Field K] [CharZero K]
variable {ι : Type*} (B : Finset ι) (pos : ι → Prop) [DecidablePred pos]

/-- The ideal contrast of a bin: `+1` on `posBins`, `-1` elsewhere. -/
def sgn (y : ι) : K := if pos y then 1 else -1

section Characters

variable {A : Type*} (χ : A → ι → K)

/-- The coefficient of `f` on the character `a`: the mean of `f * χ a` over `B`. -/
def coeff (f : ι → K) (a : A) : K := (∑ y ∈ B, f y * χ a y) / B.card

variable {B χ}

omit [CharZero K] in
/-- The estimator numerator `vHat` as the mean of `c * sgn`. -/
theorem vHat_eq_sum_div (c : ι → K) :
    vHat B c pos = (∑ y ∈ B, c y * sgn pos y) / B.card := rfl

omit [CharZero K] in
/-- The ideal contrast squares to `1`. -/
theorem sgn_mul_self (y : ι) : sgn pos y * sgn pos y = (1 : K) := by
  unfold sgn
  split_ifs <;> simp

/-- The sum of the ideal contrast is twice the nullity. -/
theorem sum_sgn_eq_two_mul_nullity : ∑ y ∈ B, sgn pos y = 2 * nullity B pos (K := K) := by
  have h := signed_sum_eq_posBins_sub_negBins B (fun _ => (1 : K)) pos
  simp only [one_mul, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  unfold nullity
  rw [← h]
  unfold sgn
  ring

omit [CharZero K] in
/-- The mean of the squared observed contrast against itself: the ideal has
unit mean square. -/
theorem vHat_sgn (hn : (B.card : K) ≠ 0) : vHat B (sgn pos) pos = (1 : K) := by
  rw [vHat_eq_sum_div, Finset.sum_congr rfl fun y _ => sgn_mul_self pos y, Finset.sum_const,
    nsmul_eq_mul, mul_one, div_self hn]

omit [CharZero K] in
/-- The sum of any function over `B` is `n` times its zeroth coefficient. -/
theorem sum_eq_card_mul_coeff (hn : (B.card : K) ≠ 0) {a₀ : A} (h0 : ∀ y ∈ B, χ a₀ y = 1)
    (f : ι → K) : ∑ y ∈ B, f y = B.card * coeff B χ f a₀ := by
  unfold coeff
  rw [Finset.sum_congr rfl (fun y hy => by rw [h0 y hy, mul_one] :
    ∀ y ∈ B, f y * χ a₀ y = f y)]
  field_simp

/-- The zeroth coefficient of the ideal contrast is `2 * nullity / n`. -/
theorem coeff_sgn_zero (hn : (B.card : K) ≠ 0) {a₀ : A} (h0 : ∀ y ∈ B, χ a₀ y = 1) :
    coeff B χ (sgn pos) a₀ = 2 * nullity B pos / B.card := by
  have h := sum_eq_card_mul_coeff (B := B) (χ := χ) hn h0 (sgn pos)
  rw [sum_sgn_eq_two_mul_nullity] at h
  field_simp
  linear_combination -h

/-- The nullity is `n * coeff (sgn pos) a₀ / 2`. -/
theorem nullity_eq_card_mul_coeff (hn : (B.card : K) ≠ 0) {a₀ : A}
    (h0 : ∀ y ∈ B, χ a₀ y = 1) :
    nullity B pos = B.card * coeff B χ (sgn pos) a₀ / 2 := by
  rw [coeff_sgn_zero pos hn h0]
  field_simp

variable [Fintype A] [DecidableEq A]

omit [CharZero K] in
/-- A function expanded in the characters has the sum against `χ b` equal to its
coefficient times `n`: orthogonality collapses the double sum. -/
theorem sum_mul_char_of_expansion (hχ : ∀ a b,
      ∑ y ∈ B, χ a y * χ b y = if a = b then (B.card : K) else 0)
    {f : ι → K} {γ : A → K} (hf : ∀ y ∈ B, f y = ∑ a, γ a * χ a y) (b : A) :
    ∑ y ∈ B, f y * χ b y = γ b * B.card := by
  calc ∑ y ∈ B, f y * χ b y
      = ∑ y ∈ B, ∑ a, γ a * (χ a y * χ b y) :=
        Finset.sum_congr rfl fun y hy => by
          rw [hf y hy, Finset.sum_mul]
          exact Finset.sum_congr rfl fun a _ => by ring
    _ = ∑ a, ∑ y ∈ B, γ a * (χ a y * χ b y) := Finset.sum_comm
    _ = ∑ a, γ a * if a = b then (B.card : K) else 0 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.mul_sum, hχ a b]
    _ = γ b * B.card := by
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

omit [CharZero K] in
/-- The coefficient of an expanded function is its expansion coefficient. -/
theorem coeff_eq_of_expansion (hn : (B.card : K) ≠ 0)
    (hχ : ∀ a b,
      ∑ y ∈ B, χ a y * χ b y = if a = b then (B.card : K) else 0)
    {f : ι → K} {γ : A → K} (hf : ∀ y ∈ B, f y = ∑ a, γ a * χ a y) (a : A) :
    coeff B χ f a = γ a := by
  unfold coeff
  rw [sum_mul_char_of_expansion hχ hf a]
  field_simp

omit [CharZero K] in
/-- The sum of an expanded function is `n` times its coefficient on the
distinguished character, since that character is `1` on `B`. -/
theorem sum_eq_coeff_mul_card (hχ : ∀ a b,
      ∑ y ∈ B, χ a y * χ b y = if a = b then (B.card : K) else 0)
    {a₀ : A} (h0 : ∀ y ∈ B, χ a₀ y = 1)
    {f : ι → K} {γ : A → K} (hf : ∀ y ∈ B, f y = ∑ a, γ a * χ a y) :
    ∑ y ∈ B, f y = γ a₀ * B.card := by
  rw [← sum_mul_char_of_expansion hχ hf a₀]
  exact Finset.sum_congr rfl fun y hy => by rw [h0 y hy, mul_one]

/-- The nullity of a block whose ideal is expanded with coefficients `σ` is
`n * σ a₀ / 2`. -/
theorem nullity_eq_card_mul_div_two
    (hχ : ∀ a b,
      ∑ y ∈ B, χ a y * χ b y = if a = b then (B.card : K) else 0)
    {a₀ : A} (h0 : ∀ y ∈ B, χ a₀ y = 1) {σ : A → K}
    (hs : ∀ y ∈ B, sgn pos y = ∑ a, σ a * χ a y) :
    nullity B pos = B.card * σ a₀ / 2 := by
  have h := sum_eq_coeff_mul_card hχ h0 hs
  rw [sum_sgn_eq_two_mul_nullity] at h
  linear_combination (1 / 2 : K) * h

omit [CharZero K] in
/-- **Plancherel.** For expanded `c` and `sgn pos`, `vHat = ∑ a, γ a * σ a`. -/
theorem vHat_eq_sum_mul (hn : (B.card : K) ≠ 0)
    (hχ : ∀ a b,
      ∑ y ∈ B, χ a y * χ b y = if a = b then (B.card : K) else 0)
    {c : ι → K} {γ σ : A → K} (hc : ∀ y ∈ B, c y = ∑ a, γ a * χ a y)
    (hs : ∀ y ∈ B, sgn pos y = ∑ a, σ a * χ a y) :
    vHat B c pos = ∑ a, γ a * σ a := by
  rw [vHat_eq_sum_div]
  have h : ∑ y ∈ B, c y * sgn pos y = (∑ a, γ a * σ a) * B.card := by
    calc ∑ y ∈ B, c y * sgn pos y
        = ∑ y ∈ B, ∑ b, σ b * (c y * χ b y) :=
          Finset.sum_congr rfl fun y hy => by
            rw [hs y hy, Finset.mul_sum]
            exact Finset.sum_congr rfl fun b _ => by ring
      _ = ∑ b, σ b * ∑ y ∈ B, c y * χ b y := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => by rw [Finset.mul_sum]
      _ = ∑ b, σ b * (γ b * B.card) :=
          Finset.sum_congr rfl fun b _ => by rw [sum_mul_char_of_expansion hχ hc b]
      _ = (∑ a, γ a * σ a) * B.card := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun b _ => by ring
  rw [h]
  field_simp

omit [CharZero K] in
/-- The weights `σ a ^ 2` of the ideal contrast sum to `1`. -/
theorem sum_sq_eq_one (hn : (B.card : K) ≠ 0)
    (hχ : ∀ a b,
      ∑ y ∈ B, χ a y * χ b y = if a = b then (B.card : K) else 0)
    {σ : A → K} (hs : ∀ y ∈ B, sgn pos y = ∑ a, σ a * χ a y) :
    ∑ a, σ a ^ 2 = 1 := by
  have h := vHat_eq_sum_mul pos hn hχ hs hs
  rw [vHat_sgn pos hn] at h
  rw [h]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **The general form of the estimator.** `nHat = n * γ a₀ / (2 * vHat)`; the
proof needs neither `n ≠ 0` nor `vHat ≠ 0` nor any structure of the channel. -/
theorem nHat_eq_card_mul_div
    (hχ : ∀ a b,
      ∑ y ∈ B, χ a y * χ b y = if a = b then (B.card : K) else 0)
    {a₀ : A} (h0 : ∀ y ∈ B, χ a₀ y = 1) {c : ι → K} {γ : A → K}
    (hc : ∀ y ∈ B, c y = ∑ a, γ a * χ a y) :
    nHat B c pos = B.card * γ a₀ / (2 * vHat B c pos) := by
  rw [nHat, sum_eq_coeff_mul_card hχ h0 hc]
  ring

/-- **Spectral form of the estimator.** Under a channel diagonal on the characters,
`nHat = nullity * lam a₀ / ∑ a, σ a ^ 2 * lam a`. -/
theorem nHat_eq_spectral
    (hχ : ∀ a b,
      ∑ y ∈ B, χ a y * χ b y = if a = b then (B.card : K) else 0)
    {a₀ : A} (h0 : ∀ y ∈ B, χ a₀ y = 1) {c : ι → K} {γ σ lam : A → K}
    (hc : ∀ y ∈ B, c y = ∑ a, γ a * χ a y) (hs : ∀ y ∈ B, sgn pos y = ∑ a, σ a * χ a y)
    (hd : ∀ a, γ a = lam a * σ a) :
    nHat B c pos = nullity B pos * lam a₀ / ∑ a, σ a ^ 2 * lam a := by
  by_cases hn : (B.card : K) = 0
  · have hB : B = ∅ := Finset.card_eq_zero.mp (Nat.cast_eq_zero.mp hn)
    subst hB
    simp [nHat, nullity, posBins, negBins]
  · rw [nHat_eq_card_mul_div pos hχ h0 hc, vHat_eq_sum_mul pos hn hχ hc hs,
      nullity_eq_card_mul_div_two pos hχ h0 hs, hd a₀]
    have hS : ∑ a, γ a * σ a = ∑ a, σ a ^ 2 * lam a :=
      Finset.sum_congr rfl fun a _ => by rw [hd a]; ring
    rw [hS]
    by_cases hz : ∑ a, σ a ^ 2 * lam a = 0
    · simp [hz]
    · field_simp

/-- **Forced reading on one character.** An ideal supported on the character `a₀`
alone is read as its nullity whenever `vHat ≠ 0`, for every channel. -/
theorem nHat_eq_nullity_of_support_eq_single
    (hχ : ∀ a b,
      ∑ y ∈ B, χ a y * χ b y = if a = b then (B.card : K) else 0)
    {a₀ : A} (h0 : ∀ y ∈ B, χ a₀ y = 1) {c : ι → K} {γ σ : A → K}
    (hc : ∀ y ∈ B, c y = ∑ a, γ a * χ a y) (hs : ∀ y ∈ B, sgn pos y = ∑ a, σ a * χ a y)
    (hσ : ∀ a, a ≠ a₀ → σ a = 0) (hV : vHat B c pos ≠ 0) :
    nHat B c pos = nullity B pos := by
  have hn : (B.card : K) ≠ 0 := fun h => hV (by simp [vHat, h])
  have h1 : σ a₀ ^ 2 = 1 := by
    rw [← sum_sq_eq_one pos hn hχ hs,
      Finset.sum_eq_single a₀ _ (fun h => absurd (Finset.mem_univ _) h)]
    intro a _ ha
    rw [hσ a ha]
    ring
  have hP : vHat B c pos = γ a₀ * σ a₀ := by
    rw [vHat_eq_sum_mul pos hn hχ hc hs,
      Finset.sum_eq_single a₀ _ (fun h => absurd (Finset.mem_univ _) h)]
    intro a _ ha
    rw [hσ a ha, mul_zero]
  have hγ : γ a₀ ≠ 0 := fun h => hV (by rw [hP, h, zero_mul])
  have hσ0 : σ a₀ ≠ 0 := fun h => by rw [h] at h1; simp at h1
  rw [nHat_eq_card_mul_div pos hχ h0 hc, hP, nullity_eq_card_mul_div_two pos hχ h0 hs,
    div_eq_iff (mul_ne_zero two_ne_zero (mul_ne_zero hγ hσ0))]
  linear_combination (-((B.card : K) * γ a₀)) * h1

/-- **Zero reading.** An ideal with no component on `a₀` is read as `0` by every
channel that is diagonal at `a₀`, with no hypothesis on `vHat`. -/
theorem nHat_eq_zero_of_coeff_zero
    (hχ : ∀ a b,
      ∑ y ∈ B, χ a y * χ b y = if a = b then (B.card : K) else 0)
    {a₀ : A} (h0 : ∀ y ∈ B, χ a₀ y = 1) {c : ι → K} {γ σ lam : A → K}
    (hc : ∀ y ∈ B, c y = ∑ a, γ a * χ a y) (hd : γ a₀ = lam a₀ * σ a₀) (hz : σ a₀ = 0) :
    nHat B c pos = 0 := by
  rw [nHat_eq_card_mul_div pos hχ h0 hc, hd, hz]
  simp

end Characters

section Walsh

/-- The Walsh character of index `a` at the bin `y`: `-1` to the number of positions
where both bit vectors are set. -/
def walshChar (L : Type*) [Field L] (d : ℕ) (a y : Fin d → Bool) : L :=
  ∏ i, if a i && y i then (-1 : L) else 1

omit [CharZero K] in
/-- The character of the zero index is `1` at every bin. -/
theorem walshChar_zero (d : ℕ) (y : Fin d → Bool) :
    walshChar K d (fun _ => false) y = 1 := by
  simp [walshChar]

omit [CharZero K] in
/-- **Orthogonality of the Walsh characters.** Over all `2 ^ d` bins, two characters
have inner product `2 ^ d` when they agree and `0` otherwise, for every `d`. -/
theorem walshChar_orthogonal (d : ℕ) (a b : Fin d → Bool) :
    ∑ y : Fin d → Bool, walshChar K d a y * walshChar K d b y =
      if a = b then ((Finset.univ : Finset (Fin d → Bool)).card : K) else 0 := by
  have hbit : ∀ p q : Bool, ∑ t : Bool,
      (if p && t then (-1 : K) else 1) * (if q && t then (-1 : K) else 1) =
        if p = q then 2 else 0 := by
    intro p q
    cases p <;> cases q <;> norm_num [Fintype.sum_bool]
  have h1 : ∑ y : Fin d → Bool, walshChar K d a y * walshChar K d b y =
      ∏ i, if a i = b i then (2 : K) else 0 := by
    calc ∑ y : Fin d → Bool, walshChar K d a y * walshChar K d b y
        = ∑ y : Fin d → Bool, ∏ i, ((if a i && y i then (-1 : K) else 1) *
            (if b i && y i then (-1 : K) else 1)) :=
          Finset.sum_congr rfl fun y _ => by
            unfold walshChar
            rw [← Finset.prod_mul_distrib]
      _ = ∏ i, ∑ t : Bool, ((if a i && t then (-1 : K) else 1) *
            (if b i && t then (-1 : K) else 1)) := (Fintype.prod_sum (fun (i : Fin d) (t : Bool) =>
            (if a i && t then (-1 : K) else 1) * (if b i && t then (-1 : K) else 1))).symm
      _ = ∏ i, if a i = b i then (2 : K) else 0 :=
          Finset.prod_congr rfl fun i _ => hbit (a i) (b i)
  rw [h1]
  by_cases h : a = b
  · subst h
    simp only [↓reduceIte, Finset.prod_const, Finset.card_univ, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin]
    push_cast
    rfl
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    simp only [h, ↓reduceIte]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [hi, ↓reduceIte])

end Walsh

end KernelMap
