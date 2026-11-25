/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib

/-!
# Numerical core of the Eisenbud-Goto bounds for minimal multiplicity

Convention: a graded algebra of codimension `c` and Krull dimension `d + 1` with minimal
multiplicity has Hilbert series `(1 + c t) / (1 - t) ^ (d + 1)`, so `h(1) = 1 + c` is its
multiplicity. Hilbert functions are the coefficients of this series, with
`PowerSeries.invOneSubPow S (d + 1)` the inverse of `(1 - t) ^ (d + 1)`. The Betti numbers
of the 2-linear resolution of a variety of minimal degree (Eagon-Northcott complex) are
`betti c q = q * C(c + 1, q + 1)` for `1 ≤ q ≤ c`, with `betti c 0 = 0` standing for the
free module in degree 0 (whose rank 1 is the leading `1` of `numerator`).

Eisenbud and Goto, "Linear free resolutions and minimal multiplicity", J. Algebra 88 (1984),
Proposition 1.7 and Corollary 1.11: for `R = S / I` homogeneous of codimension `c` with a
`p`-linear resolution, `R` is Cohen-Macaulay if and only if the minimal number of generators
of `I` is at most `C(c + p - 1, c - 1)`, if and only if the multiplicity is at least
`C(c + p - 1, c)`, and then both are equalities. At `p = 2` the two numbers are
`C(c + 1, 2) = betti c 1` and `c + 1 = h(1)`.

## Main results

* `EisenbudGoto.coeff_hilbertSeries`: the Hilbert function at `n + 1` is
  `C(d + n + 1, d) + c C(d + n, d)`, over every commutative ring.
* `EisenbudGoto.eval_hilbertPoly`: the Mathlib Hilbert polynomial of `1 + c t` takes that value
  at every `n ≥ 2`.
* `EisenbudGoto.hilbertFn_one_add_betti_one`: the Hilbert function at 2 plus the number of
  quadrics is `C(c + d + 2, 2)`, the dimension of the quadrics of the ambient polynomial ring.
* `EisenbudGoto.numerator_eq`: `1 + Σ_q (-1)^q betti c q t^(q+1) = (1 - t)^c (1 + c t)`, the
  Betti numbers recover the Hilbert series numerator.
* `EisenbudGoto.alternating_betti`: the alternating sum of the Betti numbers, with the leading 1,
  is 0 for `c ≥ 1`.
* `EisenbudGoto.e8_hilbertFn`, `EisenbudGoto.e8_betti`: the instance `c = 6`, `d + 1 = 4`
  (Hilbert series `(1 + 6 t) / (1 - t) ^ 4`): values 10, 34, 80, 155, 266, 420, 624, 885 at
  `n = 1 .. 8` and Betti numbers 21, 70, 105, 84, 35, 6.

## What this file does not prove

Mathlib v4.35.0 holds no `IsCohenMacaulay`, no depth or regular-sequence theory over graded
rings, no Castelnuovo-Mumford regularity, no minimal graded free resolution or graded Betti
table, no Eagon-Northcott complex and no multiplicity of a graded module (a search of the tree for
`CohenMacaulay` finds nothing, and `hilbertPoly` only turns a numerator into a polynomial). The
equivalences of Corollary 1.11 therefore need these definitions, in this order: graded depth and
`IsCohenMacaulay` for a graded ring; a minimal graded free resolution and its graded Betti numbers;
the property "`p`-linear resolution"; the multiplicity `e(R)` as `h(1)` of the Hilbert series
numerator; the Eagon-Northcott complex as an explicit resolution; and the Hilbert-series
additivity along that resolution. This file proves the arithmetic that those statements reduce
to once they exist.
-/

@[expose] public section

open Polynomial

namespace EisenbudGoto

/-- The Hilbert-series numerator of minimal multiplicity: `1 + c t`. -/
noncomputable def hilbertNumerator (S : Type*) [CommRing S] (c : ℕ) : S[X] :=
  1 + C (c : S) * X

/-- The Hilbert series `(1 + c t) / (1 - t) ^ (d + 1)`. -/
noncomputable def hilbertSeries (S : Type*) [CommRing S] (c d : ℕ) : PowerSeries S :=
  (hilbertNumerator S c : PowerSeries S) * (PowerSeries.invOneSubPow S (d + 1)).val

/-- The Betti number `q C(c + 1, q + 1)` of the Eagon-Northcott resolution in homological
degree `q` (degree `q + 1`). -/
def betti (c q : ℕ) : ℕ := q * (c + 1).choose (q + 1)

/-- The Hilbert function `C(d + n, d) + c C(d + n - 1, d)` at `n + 1`, written without
truncated subtraction. -/
def hilbertFn (c d n : ℕ) : ℕ := (d + (n + 1)).choose d + c * (d + n).choose d

/-- The coefficient of `t ^ (n + 1)` in `(1 + c t) / (1 - t) ^ (d + 1)` is the Hilbert function
of minimal multiplicity. -/
theorem coeff_hilbertSeries (S : Type*) [CommRing S] (c d n : ℕ) :
    (hilbertSeries S c d).coeff (n + 1) = (hilbertFn c d n : S) := by
  have h1 : (hilbertNumerator S c : PowerSeries S)
      = 1 + PowerSeries.C (c : S) * PowerSeries.X := by
    simp only [hilbertNumerator, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_mul,
      Polynomial.coe_C, Polynomial.coe_X]
  have h2 : (hilbertSeries S c d) = (PowerSeries.invOneSubPow S (d + 1)).val
      + PowerSeries.C (c : S) * (PowerSeries.X * (PowerSeries.invOneSubPow S (d + 1)).val) := by
    unfold hilbertSeries; rw [h1]; ring
  rw [h2, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
    PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose, PowerSeries.coeff_mk,
    PowerSeries.coeff_mk]
  simp [hilbertFn]

/-- The Mathlib Hilbert polynomial of `1 + c t` with `d + 1` factors of `1 - t` takes the
Hilbert function as value at every `n ≥ 2`. -/
theorem eval_hilbertPoly (F : Type*) [Field F] [CharZero F] (c d n : ℕ) :
    (hilbertPoly (hilbertNumerator F c) (d + 1)).eval ((n + 1 + 1 : ℕ) : F)
      = (hilbertFn c d (n + 1) : F) := by
  have hdeg : (hilbertNumerator F c).natDegree < n + 1 + 1 := by
    have : (hilbertNumerator F c).natDegree ≤ 1 := by
      unfold hilbertNumerator; compute_degree
    omega
  rw [← coeff_mul_invOneSubPow_eq_hilbertPoly_eval (d + 1) hdeg]
  exact coeff_hilbertSeries F c d (n + 1)

/-- The coefficient identity `j C(c + 1, j + 1) = c C(c, j) - C(c, j + 1)` behind the
numerator. -/
theorem betti_identity (c j : ℕ) :
    (j : ℤ) * ((c + 1).choose (j + 1) : ℕ) = c * (c.choose j : ℕ) - (c.choose (j + 1) : ℕ) := by
  rcases le_or_gt j c with h | h
  · have h1 := congrArg (Nat.cast : ℕ → ℤ) (Nat.choose_succ_right_eq c j)
    push_cast [Nat.cast_sub h] at h1
    rw [Nat.choose_succ_succ']
    push_cast
    linarith
  · rw [Nat.choose_eq_zero_of_lt (show c + 1 < j + 1 by omega),
      Nat.choose_eq_zero_of_lt h, Nat.choose_eq_zero_of_lt (show c < j + 1 by omega)]
    simp

/-- The Hilbert function at 2 plus the number of quadrics is `C(c + d + 2, 2)`. -/
theorem hilbertFn_one_add_betti_one (c d : ℕ) :
    hilbertFn c d 1 + betti c 1 = (c + d + 2).choose 2 := by
  unfold hilbertFn betti
  have e1 : (d + (1 + 1)).choose d = (d + 2).choose 2 := Nat.choose_symm_add
  have e2 : (d + 1).choose d = d + 1 := Nat.choose_succ_self_right d
  have e3 : (c + 1).choose (1 + 1) = c.choose 2 + c := by
    rw [Nat.choose_succ_succ', Nat.choose_one_right]; ring
  rw [e1, e2, one_mul, e3, show c + d + 2 = c + (d + 2) by ring, Nat.add_choose_eq c (d + 2) 2]
  simp [Finset.Nat.antidiagonal_succ]
  ring

/-- The coefficient of `(1 - t) ^ c` at `t ^ k` is `(-1) ^ k C(c, k)`. -/
theorem coeff_one_sub_X_pow (c k : ℕ) :
    ((1 - X : ℤ[X]) ^ c).coeff k = (-1) ^ k * (c.choose k : ℤ) := by
  rcases le_or_gt k c with h | h
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
    have e : (1 - X : ℤ[X]) ^ (k + m) = C ((-1) ^ (k + m)) * (X + C (-1)) ^ (k + m) := by
      rw [C_pow, C_neg, C_1, ← mul_pow]; congr 1; ring
    rw [e, coeff_C_mul, coeff_X_add_C_pow, Nat.add_sub_cancel_left]
    have : ((-1 : ℤ) ^ (k + m)) * ((-1) ^ m * ((k + m).choose k : ℤ))
        = (-1) ^ k * ((k + m).choose k : ℤ) := by
      rw [pow_add]
      have : ((-1 : ℤ) ^ m) * (-1) ^ m = 1 := by rw [← mul_pow]; simp
      calc (-1 : ℤ) ^ k * (-1) ^ m * ((-1) ^ m * ((k + m).choose k : ℤ))
          = (-1) ^ k * (((-1) ^ m * (-1) ^ m) * ((k + m).choose k : ℤ)) := by ring
        _ = _ := by rw [this]; ring
    simpa using this
  · rw [Nat.choose_eq_zero_of_lt h]
    have : ((1 - X : ℤ[X]) ^ c).coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      calc ((1 - X : ℤ[X]) ^ c).natDegree ≤ c * (1 - X : ℤ[X]).natDegree := natDegree_pow_le
        _ ≤ c * 1 := by
          gcongr; compute_degree
        _ < k := by omega
    simpa using this

/-- The polynomial `1 + Σ_(q ≤ c) (-1) ^ q betti c q t ^ (q + 1)` read off the Betti table. -/
noncomputable def numerator (c : ℕ) : ℤ[X] :=
  1 + ∑ q ∈ Finset.range (c + 1), C ((-1) ^ q * (betti c q : ℤ)) * X ^ (q + 1)

/-- The Betti numbers of the Eagon-Northcott resolution recover the Hilbert-series numerator:
`1 + Σ (-1)^q betti c q t^(q + 1) = (1 - t)^c (1 + c t)`. -/
theorem numerator_eq (c : ℕ) : numerator c = (1 - X) ^ c * hilbertNumerator ℤ c := by
  have e : (1 - X : ℤ[X]) ^ c * hilbertNumerator ℤ c
      = (1 - X) ^ c + C (c : ℤ) * ((1 - X) ^ c * X) := by
    unfold hilbertNumerator; ring
  rw [e]
  ext k
  rw [coeff_add, coeff_C_mul, numerator, coeff_add, coeff_one, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, coeff_one_sub_X_pow]
  rcases k with _ | j
  · simp
  · rw [coeff_mul_X]
    simp only [coeff_one_sub_X_pow, Nat.add_one_ne_zero, ite_false, zero_add,
      Nat.add_right_cancel_iff, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_range]
    have hid := betti_identity c j
    by_cases hj : j < c + 1
    · simp only [hj, ite_true]
      unfold betti
      push_cast
      rw [pow_succ]
      linear_combination ((-1 : ℤ) ^ j) * hid
    · simp only [hj, ite_false]
      rw [Nat.choose_eq_zero_of_lt (show c < j by omega),
        Nat.choose_eq_zero_of_lt (show c < j + 1 by omega)]
      simp

/-- The alternating sum of the Betti numbers, with the leading `1`, is `0` for `c ≥ 1`: the
resolved quotient has rank `0`. -/
theorem alternating_betti (c : ℕ) (hc : 1 ≤ c) :
    1 + ∑ q ∈ Finset.range (c + 1), (-1 : ℤ) ^ q * (betti c q : ℤ) = 0 := by
  have h := congrArg (Polynomial.eval 1) (numerator_eq c)
  simpa [numerator, hilbertNumerator, eval_finsetSum, zero_pow (by omega : c ≠ 0)] using h

/-- The Eisenbud-Goto numbers at `p = 2`: `betti c 1 = C(c + 1, c - 1)` generators of the ideal
and multiplicity `1 + c = C(c + 1, c)`. -/
theorem eisenbudGoto_numbers_two (c : ℕ) (hc : 1 ≤ c) :
    betti c 1 = (c + 1).choose (c - 1) ∧ 1 + c = (c + 1).choose c := by
  constructor
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hc
    rw [show 1 + m - 1 = m by omega]
    unfold betti
    rw [show 1 + m + 1 = m + 2 by ring, one_mul]
    simpa using (Nat.choose_symm_add (a := m) (b := 2)).symm
  · rw [Nat.choose_succ_self_right]
    ring

/-- The Hilbert function of the instance `c = 6`, `d + 1 = 4` at `n = 1 .. 8`. -/
theorem e8_hilbertFn :
    (List.range 8).map (fun n => hilbertFn 6 3 n) = [10, 34, 80, 155, 266, 420, 624, 885] := by
  decide

/-- The Betti numbers of the instance `c = 6` in degrees `q = 1 .. 6`. -/
theorem e8_betti : (List.range 6).map (fun q => betti 6 (q + 1)) = [21, 70, 105, 84, 35, 6] := by
  decide

end EisenbudGoto
