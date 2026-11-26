/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.LinearAlgebra.Pfaffian
public import GororobaMath.LinearAlgebra.PfaffianForm
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.Data.Matrix.Block

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
* `Matrix.pfaffianAux_six`, `Matrix.pfaffianAux_six_indices`: the fifteen-term expansion of the
  Pfaffian on six indices, of `Fin 6` and of any index type.
* `Matrix.pfaffianAux_eight_indices`: the expansion on eight indices into six-index Pfaffians.
* `Matrix.pfaffianAux_append_swap_blocks`: swapping two blocks of a list multiplies the Pfaffian
  of a skew matrix by `(-1) ^ (|blk| * |l|)`.
* `Matrix.det_eq_pfaffian_sq_fin_two`, `Matrix.det_eq_pfaffian_sq_fin_four`,
  `Matrix.det_eq_pfaffian_sq_fin_six`: `det A = pfaffian A ^ 2` for an alternating `2 × 2`,
  `4 × 4` and `6 × 6` matrix over a commutative ring.
* `Matrix.schur_cleared_of_mul`: for `T = [[B, X], [-Xᵀ, D]]` with `B`, `D` skew, `2`
  left-regular and any `M` with `B * M = c • X`,
  `c ^ |q| * Pf T = Pf B * c ^ (|q| / 2) * Pf (c • D + Xᵀ * M) q` for even `|q|`; a block whose
  square is a scalar, `B * B = -s • 1`, clears with `c = s` and `M = -(B * X)`.
* `Matrix.schur_cleared`: for `T = [[B, X], [-Xᵀ, D]]` with `B` of size `n`, `B`, `D` skew and `2`
  left-regular, the Pfaffian of `T` on the `n` leading indices followed by a list `q` of
  complement indices satisfies
  `det B ^ |q| * Pf T = Pf B * det B ^ (|q| / 2) * Pf (det B • D + Xᵀ * adjugate B * X) q`
  for even `|q|`, over any commutative ring and without an inverse of `B`.
* `Matrix.schur_pfaffian_six`: over a domain with `2 ≠ 0`, for alternating `6 × 6` `B` with
  `Pf B ≠ 0` and four complement indices, `Pf W = Pf B ^ 3 * Pf T` for `W = det B • D + Xᵀ *
  adjugate B * X`.
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

/-- The Pfaffian on six indices of any type is the fifteen-term sum over the matchings of the
first index, from two expansions along the head. -/
theorem pfaffianAux_six_indices (A : ι → ι → R) (i₀ i₁ i₂ i₃ i₄ i₅ : ι) :
    pfaffianAux A [i₀, i₁, i₂, i₃, i₄, i₅] =
      A i₀ i₁ * (A i₂ i₃ * A i₄ i₅ - A i₂ i₄ * A i₃ i₅ + A i₂ i₅ * A i₃ i₄) -
      A i₀ i₂ * (A i₁ i₃ * A i₄ i₅ - A i₁ i₄ * A i₃ i₅ + A i₁ i₅ * A i₃ i₄) +
      A i₀ i₃ * (A i₁ i₂ * A i₄ i₅ - A i₁ i₄ * A i₂ i₅ + A i₁ i₅ * A i₂ i₄) -
      A i₀ i₄ * (A i₁ i₂ * A i₃ i₅ - A i₁ i₃ * A i₂ i₅ + A i₁ i₅ * A i₂ i₃) +
      A i₀ i₅ * (A i₁ i₂ * A i₃ i₄ - A i₁ i₃ * A i₂ i₄ + A i₁ i₄ * A i₂ i₃) := by
  rw [pfaffianAux_cons_dite]
  simp [Finset.sum_range_succ, pfaffianAux_four]
  ring

/-- The Pfaffian on eight indices of any type, expanded along the first index into six-index
Pfaffians. -/
theorem pfaffianAux_eight_indices (A : ι → ι → R) (i₀ i₁ i₂ i₃ i₄ i₅ i₆ i₇ : ι) :
    pfaffianAux A [i₀, i₁, i₂, i₃, i₄, i₅, i₆, i₇] =
      A i₀ i₁ * pfaffianAux A [i₂, i₃, i₄, i₅, i₆, i₇] -
      A i₀ i₂ * pfaffianAux A [i₁, i₃, i₄, i₅, i₆, i₇] +
      A i₀ i₃ * pfaffianAux A [i₁, i₂, i₄, i₅, i₆, i₇] -
      A i₀ i₄ * pfaffianAux A [i₁, i₂, i₃, i₅, i₆, i₇] +
      A i₀ i₅ * pfaffianAux A [i₁, i₂, i₃, i₄, i₆, i₇] -
      A i₀ i₆ * pfaffianAux A [i₁, i₂, i₃, i₄, i₅, i₇] +
      A i₀ i₇ * pfaffianAux A [i₁, i₂, i₃, i₄, i₅, i₆] := by
  rw [pfaffianAux_cons_dite]
  simp [Finset.sum_range_succ, pfaffianAux_six_indices]
  ring

/-- Swapping two blocks of a list multiplies the Pfaffian of a skew matrix by `(-1)` to the product
of their lengths, one index moved past the first block at a time. -/
theorem pfaffianAux_append_swap_blocks (A : ι → ι → R) (hA : ∀ a b, A a b = -A b a)
    (blk l : List ι) :
    pfaffianAux A (blk ++ l) = (-1) ^ (blk.length * l.length) * pfaffianAux A (l ++ blk) := by
  suffices H : ∀ (l pre : List ι), pfaffianAux A (pre ++ blk ++ l) =
      (-1) ^ (blk.length * l.length) * pfaffianAux A (pre ++ l ++ blk) by
    simpa using H l []
  intro l
  induction l with
  | nil => intro pre; simp
  | cons y l ih =>
    intro pre
    rw [pfaffianAux_move_left A hA pre blk y l]
    have e1 : pre ++ y :: (blk ++ l) = pre ++ [y] ++ blk ++ l := by simp
    have e2 : pre ++ [y] ++ l ++ blk = pre ++ y :: l ++ blk := by simp
    rw [e1, ih (pre ++ [y]), e2, List.length_cons]
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

section Transvect

variable {V : Type*} [AddCommGroup V] [Module R V]

private theorem pfaffianAux_append_add_sum_of_mem (ω : V → V → R)
    (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z) (hsmul : ∀ (c : R) x z, ω (c • x) z = c * ω x z)
    (hskew : ∀ x y, ω x y = -ω y x) (hreg : IsLeftRegular (2 : R)) (pre rest : List V) (x : V) :
    ∀ s : List (R × V), (∀ p ∈ s, p.2 ∈ pre ++ rest) →
      pfaffianAux ω (pre ++ (x + (s.map fun p => p.1 • p.2).sum) :: rest) =
        pfaffianAux ω (pre ++ x :: rest) := by
  intro s
  induction s with
  | nil => intro _; simp only [List.map_nil, List.sum_nil, add_zero]
  | cons p s ih =>
    intro hs
    have h1 : x + ((p :: s).map fun p => p.1 • p.2).sum =
        (x + (s.map fun p => p.1 • p.2).sum) + p.1 • p.2 := by
      simp only [List.map_cons, List.sum_cons]
      abel
    rw [h1, pfaffianAux_append_add_smul_of_mem ω hadd hsmul hskew hreg pre _ p.2 p.1 rest
      (hs p List.mem_cons_self)]
    exact ih fun q hq => hs q (List.mem_cons_of_mem _ hq)

/-- Replacing each tail entry `t j` by `t j` plus a combination of vectors of `vl` leaves the
Pfaffian unchanged when `vl` lies in the leading list. -/
theorem pfaffianAux_append_map_of_combination (ω : V → V → R)
    (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z) (hsmul : ∀ (c : R) x z, ω (c • x) z = c * ω x z)
    (hskew : ∀ x y, ω x y = -ω y x) (hreg : IsLeftRegular (2 : R)) {α : Type*} (vl : List V)
    (t u : α → V) (hu : ∀ j, ∃ s : List (R × V), (∀ p ∈ s, p.2 ∈ vl) ∧
      u j = t j + (s.map fun p => p.1 • p.2).sum) :
    ∀ (q : List α) (pre : List V), (∀ y ∈ vl, y ∈ pre) →
      pfaffianAux ω (pre ++ q.map t) = pfaffianAux ω (pre ++ q.map u) := by
  intro q
  induction q with
  | nil => intro pre _; rfl
  | cons x q ih =>
    intro pre hpre
    obtain ⟨s, hs, hux⟩ := hu x
    have hmem : ∀ p ∈ s, p.2 ∈ pre ++ q.map t := fun p hp =>
      List.mem_append_left _ (hpre _ (hs p hp))
    calc pfaffianAux ω (pre ++ (List.map t (x :: q)))
        = pfaffianAux ω (pre ++ (t x + (s.map fun p => p.1 • p.2).sum) :: q.map t) :=
          (pfaffianAux_append_add_sum_of_mem ω hadd hsmul hskew hreg pre (q.map t) (t x) s
            hmem).symm
      _ = pfaffianAux ω ((pre ++ [u x]) ++ q.map t) := by
          rw [← hux]; simp only [List.append_assoc, List.singleton_append]
      _ = pfaffianAux ω ((pre ++ [u x]) ++ q.map u) :=
          ih _ fun y hy => List.mem_append_left _ (hpre y hy)
      _ = pfaffianAux ω (pre ++ (List.map u (x :: q))) := by
          simp only [List.append_assoc, List.singleton_append, List.map_cons]

/-- Scaling every tail entry by `c` scales the Pfaffian by `c` to the number of tail entries. -/
theorem pfaffianAux_append_map_smul (ω : V → V → R) (hsmul : ∀ (c : R) x z, ω (c • x) z = c * ω x z)
    (hskew : ∀ x y, ω x y = -ω y x) (c : R) {α : Type*} (t : α → V) :
    ∀ (q : List α) (pre : List V),
      pfaffianAux ω (pre ++ q.map fun j => c • t j) =
        c ^ q.length * pfaffianAux ω (pre ++ q.map t) := by
  intro q
  induction q with
  | nil => intro pre; simp
  | cons x q ih =>
    intro pre
    have h := ih (pre ++ [t x])
    simp only [List.append_assoc, List.singleton_append] at h
    simp only [List.map_cons, List.length_cons]
    rw [pfaffianAux_append_smul ω hsmul hskew, h]
    ring

end Transvect

section Schur

variable {n : ℕ} {κ : Type*} [Finite κ]

/-- The bilinear form `x ⬝ T y` of a matrix on coordinate vectors. -/
def skewForm {ι : Type*} [Fintype ι] (T : Matrix ι ι R) (x y : ι → R) : R :=
  dotProduct x (T.mulVec y)

private theorem skewForm_add {ι : Type*} [Fintype ι] (T : Matrix ι ι R) (x y z : ι → R) :
    skewForm T (x + y) z = skewForm T x z + skewForm T y z := by
  simp only [skewForm, add_dotProduct]

private theorem skewForm_smul {ι : Type*} [Fintype ι] (T : Matrix ι ι R) (c : R) (x z : ι → R) :
    skewForm T (c • x) z = c * skewForm T x z := by
  simp only [skewForm, smul_dotProduct, smul_eq_mul]

private theorem skewForm_skew {ι : Type*} [Fintype ι] (T : Matrix ι ι R) (hT : Tᵀ = -T)
    (x y : ι → R) : skewForm T x y = -skewForm T y x := by
  simp only [skewForm]
  rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hT,
    Matrix.neg_mulVec, dotProduct_neg]

private theorem skewForm_single {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Matrix ι ι R)
    (i j : ι) : skewForm T (Pi.single i 1) (Pi.single j 1) = T i j := by
  simp [skewForm, dotProduct, Matrix.mulVec, Pi.single_apply]

/-- The cleared Schur-complement law of the Pfaffian with a chosen clearing matrix: if
`B * M = c • X`, replacing each tail generator by `c` times itself minus the combination `M` of the
leading generators makes it pair to zero with them, so the tail Pfaffian becomes that of
`c • D + Xᵀ * M`. -/
theorem schur_cleared_of_mul (h2 : IsLeftRegular (2 : R)) (B : Matrix (Fin n) (Fin n) R)
    (X : Matrix (Fin n) κ R) (D : Matrix κ κ R) (hB : Bᵀ = -B) (hD : Dᵀ = -D) (c : R)
    (M : Matrix (Fin n) κ R) (hBM : B * M = c • X) (q : List κ) (hq : q.length % 2 = 0) :
    c ^ q.length * pfaffianAux (Matrix.fromBlocks B X (-Xᵀ) D)
        ((List.finRange n).map Sum.inl ++ q.map Sum.inr) =
      pfaffian B * c ^ (q.length / 2) * pfaffianAux (c • D + Xᵀ * M) q := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  set T : Matrix (Fin n ⊕ κ) (Fin n ⊕ κ) R := Matrix.fromBlocks B X (-Xᵀ) D with hTdef
  have hT : Tᵀ = -T := by
    rw [hTdef, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg, hB, hD]
    simp
  set ω : (Fin n ⊕ κ → R) → (Fin n ⊕ κ → R) → R := skewForm T with hω
  have hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z := skewForm_add T
  have hsmul : ∀ (a : R) x z, ω (a • x) z = a * ω x z := skewForm_smul T
  have hskew : ∀ x y, ω x y = -ω y x := skewForm_skew T hT
  set g : Fin n ⊕ κ → (Fin n ⊕ κ → R) := fun i => Pi.single i 1 with hg
  set vl : List (Fin n ⊕ κ → R) := (List.finRange n).map fun a => g (Sum.inl a) with hvl
  set u : κ → (Fin n ⊕ κ → R) := fun j =>
    Sum.elim (fun a => -(M a j)) (c • Pi.single j (1 : R)) with hu
  set W : Matrix κ κ R := c • D + Xᵀ * M with hW
  -- the Pfaffian of T on the index list is the Pfaffian of the form on the basis vectors
  have hPT : pfaffianAux T ((List.finRange n).map Sum.inl ++ q.map Sum.inr) =
      pfaffianAux ω (vl ++ q.map fun j => g (Sum.inr j)) := by
    have := pfaffianAux_reindex ω g _ ((List.finRange n).map Sum.inl ++ q.map Sum.inr) rfl
    have e : (fun a b => ω (g a) (g b)) = T := funext fun a => funext fun b => skewForm_single T a b
    rw [e] at this
    rw [this]
    simp only [List.map_append, List.map_map, hvl]
    rfl
  have hPB : pfaffian B = pfaffianAux ω vl := by
    have := pfaffianAux_reindex ω (fun a => g (Sum.inl a)) _ (List.finRange n) rfl
    have e : (fun a b => ω (g (Sum.inl a)) (g (Sum.inl b))) = B := by
      funext a b
      exact (skewForm_single T (Sum.inl a) (Sum.inl b)).trans (by simp [hTdef])
    rw [e] at this
    exact this
  -- the generators of the tail are combinations of the leading vectors
  have hrep : ∀ j, u j = c • g (Sum.inr j) +
      (((List.finRange n).map fun a => (-(M a j), g (Sum.inl a))).map fun p => p.1 • p.2).sum := by
    intro j
    rw [List.map_map, ← Fin.sum_univ_def]
    funext x
    rcases x with a | i
    · simp [hu, hg, Finset.sum_apply, Pi.single_apply]
    · simp [hu, hg, Finset.sum_apply, Pi.single_apply]
  -- the product of T with each tail generator
  have hdot : ∀ (z : Fin n ⊕ κ → R) (i : Fin n ⊕ κ), dotProduct (Pi.single i (1 : R)) z = z i := by
    intro z i
    simp [dotProduct, Pi.single_apply]
  have hl : ∀ k j, (T.mulVec (u j)) (Sum.inl k) = 0 := by
    intro k j
    have e := congrFun (congrFun hBM k) j
    simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at e
    rw [show u j = Sum.elim (fun a => -(M a j)) (c • Pi.single j (1 : R)) from rfl, hTdef,
      Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_inl, Pi.add_apply]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    linear_combination (-1 : R) * e
  have hr : ∀ i j, (T.mulVec (u j)) (Sum.inr i) = W i j := by
    intro i j
    rw [show u j = Sum.elim (fun a => -(M a j)) (c • Pi.single j (1 : R)) from rfl, hTdef,
      Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_inr, Pi.add_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.neg_apply, Matrix.transpose_apply,
      Function.comp_apply, Sum.elim_inl, mul_neg, neg_mul, neg_neg, Sum.elim_inr, Pi.smul_apply,
      Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, hW, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply]
    ring
  have hcross : ∀ x ∈ vl, ∀ y ∈ q.map u, ω x y = 0 := by
    intro x hx y hy
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
    simp only [hω, skewForm, hg]
    rw [hdot]
    exact hl a j
  have hgram : ∀ i j, ω (u i) (u j) = c * W i j := by
    intro i j
    simp only [hω, skewForm, dotProduct, Fintype.sum_sum_type, hl, hr, mul_zero,
      Finset.sum_const_zero, zero_add]
    simp [hu, Pi.single_apply]
  have s1 := pfaffianAux_append_map_smul ω hsmul hskew c (fun j => g (Sum.inr j)) q vl
  have s2 := pfaffianAux_append_map_of_combination ω hadd hsmul hskew h2 vl
    (fun j => c • g (Sum.inr j)) u
    (fun j => ⟨_, fun p hp => by
      obtain ⟨a, -, rfl⟩ := List.mem_map.mp hp
      exact List.mem_map.mpr ⟨a, List.mem_finRange a, rfl⟩, hrep j⟩) q vl fun y hy => hy
  have s3 := pfaffianAux_append_of_zero ω vl (q.map u) hcross
  have s4 := pfaffianAux_reindex ω u _ q rfl
  have e4 : (fun a b => ω (u a) (u b)) = fun a b => c * W a b := funext fun a => funext fun b =>
    hgram a b
  rw [e4, pfaffianAux_smul_of_even c W q hq] at s4
  rw [hPT, ← s1, s2, s3, hPB, ← s4]
  ring

/-- The cleared Schur-complement law of the Pfaffian: no inverse of `B` and no cancellation. -/
theorem schur_cleared (h2 : IsLeftRegular (2 : R)) (B : Matrix (Fin n) (Fin n) R)
    (X : Matrix (Fin n) κ R) (D : Matrix κ κ R) (hB : Bᵀ = -B) (hD : Dᵀ = -D) (q : List κ)
    (hq : q.length % 2 = 0) :
    B.det ^ q.length * pfaffianAux (Matrix.fromBlocks B X (-Xᵀ) D)
        ((List.finRange n).map Sum.inl ++ q.map Sum.inr) =
      pfaffian B * B.det ^ (q.length / 2) *
        pfaffianAux (B.det • D + Xᵀ * B.adjugate * X) q := by
  have h := schur_cleared_of_mul h2 B X D hB hD B.det (B.adjugate * X)
    (by rw [← Matrix.mul_assoc, Matrix.mul_adjugate, smul_mul, Matrix.one_mul]) q hq
  rwa [← Matrix.mul_assoc] at h

/-- Over a domain with `2 ≠ 0`, for an alternating `6 × 6` block `B` with nonzero Pfaffian, the
Pfaffian on four complement indices of `det B • D + Xᵀ * adjugate B * X` is `Pf B ^ 3` times the
Pfaffian of `T = [[B, X], [-Xᵀ, D]]` on the six leading indices followed by those four. -/
theorem schur_pfaffian_six [IsDomain R] (h2 : (2 : R) ≠ 0) (B : Matrix (Fin 6) (Fin 6) R)
    (X : Matrix (Fin 6) κ R) (D : Matrix κ κ R) (hBs : ∀ i j, B i j = -B j i)
    (hBd : ∀ i, B i i = 0) (hDs : ∀ i j, D i j = -D j i) (hPf : pfaffian B ≠ 0) (a b c d : κ) :
    pfaffianAux (B.det • D + Xᵀ * B.adjugate * X) [a, b, c, d] =
      pfaffian B ^ 3 * pfaffianAux (Matrix.fromBlocks B X (-Xᵀ) D)
        ((List.finRange 6).map Sum.inl ++ [Sum.inr a, Sum.inr b, Sum.inr c, Sum.inr d]) := by
  have hB : Bᵀ = -B := Matrix.ext fun i j => by simp [hBs j i]
  have hD : Dᵀ = -D := Matrix.ext fun i j => by simp [hDs j i]
  have h0 := schur_cleared (mul_right_injective₀ h2) B X D hB hD [a, b, c, d] (by simp)
  have e2 : [a, b, c, d].length / 2 = 2 := by simp
  have e1 : [a, b, c, d].length = 4 := by simp
  rw [e2, e1] at h0
  have h : B.det ^ 4 * pfaffianAux (Matrix.fromBlocks B X (-Xᵀ) D)
        ((List.finRange 6).map Sum.inl ++ [Sum.inr a, Sum.inr b, Sum.inr c, Sum.inr d]) =
      pfaffian B * B.det ^ 2 * pfaffianAux (B.det • D + Xᵀ * B.adjugate * X) [a, b, c, d] := h0
  have hdet := det_eq_pfaffian_sq_fin_six B hBs hBd
  generalize pfaffianAux (B.det • D + Xᵀ * B.adjugate * X) [a, b, c, d] = W at h ⊢
  generalize pfaffianAux (Matrix.fromBlocks B X (-Xᵀ) D)
        ((List.finRange 6).map Sum.inl ++ [Sum.inr a, Sum.inr b, Sum.inr c, Sum.inr d]) = P at h ⊢
  rw [hdet] at h
  refine mul_left_cancel₀ (pow_ne_zero 5 hPf) ?_
  linear_combination (-1 : R) * h

end Schur

end Matrix
