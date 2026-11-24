/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.LinearAlgebra.Pfaffian
public import GororobaMath.LinearAlgebra.PfaffianForm
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The Pfaffian of a block-diagonal list and the determinant of a skew matrix

Convention: as in `GororobaMath.LinearAlgebra.Pfaffian`, a matrix `A` is a function
`ι → ι → R` over a commutative ring and `pfaffianAux A l` is the Pfaffian on the indices of the
list `l`, in list order. A square matrix `A : Matrix (Fin n) (Fin n) R` is called alternating
when `A i j = -A j i` for all `i j` and `A i i = 0` for all `i`; `Matrix.pfaffian A` is its
Pfaffian on `List.finRange n`.

## Main results

* `Matrix.pfaffianAux_append_of_zero`: if `A x y = 0` for every `x` in `l₁` and `y` in
  `l₂`, then `pfaffianAux A (l₁ ++ l₂) = pfaffianAux A l₁ * pfaffianAux A l₂`; no skewness and no
  parity hypothesis enters.
* `Matrix.pfaffianAux_six`: the fifteen-term expansion of the Pfaffian on six indices.
* `Matrix.det_eq_pfaffian_sq_fin_two`, `Matrix.det_eq_pfaffian_sq_fin_four`,
  `Matrix.det_eq_pfaffian_sq_fin_six`: `det A = pfaffian A ^ 2` for an alternating `2 × 2`,
  `4 × 4` and `6 × 6` matrix over a commutative ring.
-/

@[expose] public section

namespace Matrix

variable {ι R : Type*} [CommRing R]

private theorem pfaffianAux_cons_dite (A : ι → ι → R) (x : ι) (L : List ι) :
    pfaffianAux A (x :: L) = ∑ k ∈ Finset.range L.length,
      if h : k < L.length then (-1) ^ k * A x L[k] * pfaffianAux A (L.eraseIdx k) else 0 := by
  rw [pfaffianAux_cons]
  refine Eq.trans ?_ (Fin.sum_univ_eq_sum_range (fun k =>
    if h : k < L.length then (-1) ^ k * A x L[k] * pfaffianAux A (L.eraseIdx k) else 0) L.length)
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [k.isLt]

/-- A zero block between two index lists factors the Pfaffian: when `A x y = 0` for every `x` in
`l₁` and `y` in `l₂`, the expansion along each index of `l₁` meets only positions of `l₁`. -/
theorem pfaffianAux_append_of_zero (A : ι → ι → R) :
    ∀ (l₁ l₂ : List ι), (∀ x ∈ l₁, ∀ y ∈ l₂, A x y = 0) →
      pfaffianAux A (l₁ ++ l₂) = pfaffianAux A l₁ * pfaffianAux A l₂ := by
  suffices H : ∀ n (l₁ : List ι), l₁.length = n → ∀ l₂ : List ι,
      (∀ x ∈ l₁, ∀ y ∈ l₂, A x y = 0) →
        pfaffianAux A (l₁ ++ l₂) = pfaffianAux A l₁ * pfaffianAux A l₂ from
    fun l₁ l₂ h => H _ l₁ rfl l₂ h
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l₁ hn l₂ h
    cases l₁ with
    | nil => simp only [List.nil_append, pfaffianAux_nil, one_mul]
    | cons i r =>
      have key : ∀ f : ℕ → R, ∑ k ∈ Finset.range (r ++ l₂).length, f k =
          ∑ k ∈ Finset.range r.length, f k + ∑ x ∈ Finset.range l₂.length, f (r.length + x) := by
        intro f
        rw [List.length_append, Finset.sum_range_add]
      rw [List.cons_append, pfaffianAux_cons_dite, pfaffianAux_cons_dite, Finset.sum_mul, key]
      have h2 : ∑ x ∈ Finset.range l₂.length, (if hx : r.length + x < (r ++ l₂).length then
          (-1) ^ (r.length + x) * A i (r ++ l₂)[r.length + x] *
            pfaffianAux A ((r ++ l₂).eraseIdx (r.length + x)) else 0) = 0 := by
        refine Finset.sum_eq_zero fun x hx => ?_
        have hx' := Finset.mem_range.mp hx
        have hlt : r.length + x < (r ++ l₂).length := by simp only [List.length_append]; omega
        simp only [hlt, ↓reduceDIte]
        have hget : (r ++ l₂)[r.length + x]'hlt = l₂[x] := by
          rw [List.getElem_append_right (by omega)]
          simp only [Nat.add_sub_cancel_left]
        rw [hget, h i List.mem_cons_self _ (List.getElem_mem hx'), mul_zero, zero_mul]
      rw [h2, add_zero]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      have hlt : k < (r ++ l₂).length := by simp only [List.length_append]; omega
      simp only [hlt, hk', ↓reduceDIte]
      rw [List.getElem_append_left hk', List.eraseIdx_append_of_lt_length hk']
      have hlen : (r.eraseIdx k).length < n := by
        rw [List.length_eraseIdx_of_lt hk']; simp only [List.length_cons] at hn; omega
      rw [ih _ hlen (r.eraseIdx k) rfl l₂ fun x hx y hy =>
        h x (List.mem_cons_of_mem _ (List.mem_of_mem_eraseIdx hx)) y hy]
      ring

/-- The determinant of an alternating `2 × 2` matrix is the square of its Pfaffian. -/
theorem det_eq_pfaffian_sq_fin_two (A : Matrix (Fin 2) (Fin 2) R) (hA : ∀ i j, A i j = -A j i)
    (hd : ∀ i, A i i = 0) : A.det = pfaffian A ^ 2 := by
  have e : pfaffian A = A 0 1 := pfaffianAux_pair A 0 1
  rw [e, Matrix.det_fin_two, hd 0, hd 1, hA 1 0]
  ring

/-- The determinant of an alternating `4 × 4` matrix is the square of its Pfaffian. -/
theorem det_eq_pfaffian_sq_fin_four (A : Matrix (Fin 4) (Fin 4) R) (hA : ∀ i j, A i j = -A j i)
    (hd : ∀ i, A i i = 0) : A.det = pfaffian A ^ 2 := by
  have e : pfaffian A = A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2 := pfaffianAux_four A 0 1 2 3
  rw [e, Matrix.det_succ_row_zero]
  simp +decide [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove, hd, hA 1 0, hA 2 0, hA 3 0,
    hA 2 1, hA 3 1, hA 3 2]
  ring

/-- The Pfaffian on six indices expands into its fifteen products of three entries. -/
theorem pfaffianAux_six (A : Fin 6 → Fin 6 → R) :
    pfaffianAux A [0, 1, 2, 3, 4, 5] = A 0 1 * (A 2 3 * A 4 5 - A 2 4 * A 3 5 + A 2 5 * A 3 4) -
      A 0 2 * (A 1 3 * A 4 5 - A 1 4 * A 3 5 + A 1 5 * A 3 4) +
      A 0 3 * (A 1 2 * A 4 5 - A 1 4 * A 2 5 + A 1 5 * A 2 4) -
      A 0 4 * (A 1 2 * A 3 5 - A 1 3 * A 2 5 + A 1 5 * A 2 3) +
      A 0 5 * (A 1 2 * A 3 4 - A 1 3 * A 2 4 + A 1 4 * A 2 3) := by
  rw [pfaffianAux_cons_dite]
  simp [Finset.sum_range_succ, pfaffianAux_four]
  ring

/-- The determinant of an alternating `6 × 6` matrix is the square of its Pfaffian. -/
theorem det_eq_pfaffian_sq_fin_six (A : Matrix (Fin 6) (Fin 6) R) (hA : ∀ i j, A i j = -A j i)
    (hd : ∀ i, A i i = 0) : A.det = pfaffian A ^ 2 := by
  have e : pfaffian A = _ := pfaffianAux_six A
  rw [e, Matrix.det_succ_row_zero]
  simp +decide [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Fin.succAbove, hd,
    hA 1 0, hA 2 0, hA 3 0, hA 4 0, hA 5 0, hA 2 1, hA 3 1, hA 4 1, hA 5 1, hA 3 2, hA 4 2,
    hA 5 2, hA 4 3, hA 5 3, hA 5 4]
  ring

end Matrix
