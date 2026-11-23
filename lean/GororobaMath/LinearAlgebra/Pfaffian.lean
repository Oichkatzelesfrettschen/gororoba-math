/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# The Pfaffian of a matrix over a commutative ring

Convention: a matrix `A` over a commutative ring `R` is read as a function `ι → ι → R`, and a
list `l` of indices names the rows and columns kept, in list order. `pfaffianAux A l` expands
along the first index of `l`: it is `1` on the empty list, and on `i :: rest` it is the sum over
the positions `k` of `rest` of `(-1) ^ k * A i rest[k] * pfaffianAux A (rest.eraseIdx k)`, so the
`k`-th remaining index carries the sign `(-1) ^ k`. The definition assumes no skewness of `A`; for
a skew matrix of even size it is the classical Pfaffian, and a list of odd length gives `0`.
`Matrix.pfaffian A` is `pfaffianAux A` on the list `List.finRange n` of all indices of an
`n × n` matrix. The recursion runs on a natural-number fuel bounded below by the length of the
list, so the definition is structural and reduces in the kernel on small literals.

## Main results

* `Matrix.pfaffianAux_nil`, `Matrix.pfaffianAux_singleton`, `Matrix.pfaffianAux_cons`,
  `Matrix.pfaffianAux_pair`: the unfolding lemmas.
* `Matrix.pfaffianAux_four`: `A i j * A k l - A i k * A j l + A i l * A j k` on four indices.
* `Matrix.map_pfaffianAux`: naturality along a ring homomorphism.
* `Matrix.pfaffianAux_eq_zero_of_odd`: a list of odd length has Pfaffian `0`.
* `Matrix.pfaffianAux_smul_of_even`: scaling the entries by `c` scales a list of even length
  `2 m` by `c ^ m`.
* `Matrix.pfaffianAux_swap`, `Matrix.pfaffianAux_swap_of_skew`: swapping the first two indices
  negates the Pfaffian when `A j i = -A i j`, in particular for skew `A`.
* `Matrix.pfaffianAux_eq_zero_of_repeat`: a list that starts with the same index twice has
  Pfaffian `0` when `2` is left-regular and `A i i = -A i i`.
-/

@[expose] public section

namespace Matrix

variable {ι R S : Type*} [CommRing R] [CommRing S]

/-- The expansion along the first index with a fuel `n` that bounds the recursion depth; a
fuel of at least the length of the list gives the Pfaffian. -/
def pfaffianFuel (A : ι → ι → R) : ℕ → List ι → R
  | _, [] => 1
  | 0, _ :: _ => 0
  | n + 1, i :: rest =>
      ∑ k : Fin rest.length, (-1) ^ (k : ℕ) * A i rest[k] * pfaffianFuel A n (rest.eraseIdx k)

/-- The Pfaffian of the entries of `A` on the indices of a list, by expansion along the first
index. -/
def pfaffianAux (A : ι → ι → R) (l : List ι) : R :=
  pfaffianFuel A l.length l

/-- The Pfaffian of an `n × n` matrix, taken on the list of all indices in increasing order. -/
def pfaffian {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : R :=
  pfaffianAux A (List.finRange n)

private theorem length_eraseIdx_fin (rest : List ι) (k : Fin rest.length) :
    (rest.eraseIdx k).length = rest.length - 1 :=
  List.length_eraseIdx_of_lt k.isLt

private theorem pfaffianFuel_stable (A : ι → ι → R) :
    ∀ (n m : ℕ) (l : List ι), l.length ≤ n → l.length ≤ m →
      pfaffianFuel A n l = pfaffianFuel A m l := by
  intro n
  induction n with
  | zero =>
    intro m l hn _
    have hl : l = [] := List.length_eq_zero_iff.mp (by omega)
    subst hl
    simp only [pfaffianFuel]
  | succ n ih =>
    intro m l hn hm
    cases l with
    | nil => simp only [pfaffianFuel]
    | cons i rest =>
      cases m with
      | zero => simp at hm
      | succ m =>
        simp only [List.length_cons] at hn hm
        simp only [pfaffianFuel]
        refine Finset.sum_congr rfl fun k _ => ?_
        have hk := length_eraseIdx_fin rest k
        have hk' := k.isLt
        rw [ih m _ (by omega) (by omega)]

/-- The Pfaffian on the empty list is `1`. -/
theorem pfaffianAux_nil (A : ι → ι → R) : pfaffianAux A [] = 1 := by
  simp only [pfaffianAux, pfaffianFuel]

/-- The Pfaffian on a one-element list is `0`. -/
theorem pfaffianAux_singleton (A : ι → ι → R) (i : ι) : pfaffianAux A [i] = 0 := by
  simp [pfaffianAux, pfaffianFuel]

/-- The expansion along the first index: the sum over the positions `k` of the remaining list of
`(-1) ^ k * A i rest[k]` times the Pfaffian with that position removed. -/
theorem pfaffianAux_cons (A : ι → ι → R) (i : ι) (rest : List ι) :
    pfaffianAux A (i :: rest) =
      ∑ k : Fin rest.length, (-1) ^ (k : ℕ) * A i rest[k] * pfaffianAux A (rest.eraseIdx k) := by
  unfold pfaffianAux
  rw [List.length_cons, pfaffianFuel]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := length_eraseIdx_fin rest k
  have hk' := k.isLt
  rw [pfaffianFuel_stable A rest.length _ _ (by omega) le_rfl]

/-- The Pfaffian on two indices is the entry between them. -/
theorem pfaffianAux_pair (A : ι → ι → R) (i j : ι) : pfaffianAux A [i, j] = A i j := by
  rw [pfaffianAux_cons]
  simp [pfaffianAux_nil]

/-- The Pfaffian on four indices is `A i j * A k l - A i k * A j l + A i l * A j k`. -/
theorem pfaffianAux_four (A : ι → ι → R) (i j k l : ι) :
    pfaffianAux A [i, j, k, l] = A i j * A k l - A i k * A j l + A i l * A j k := by
  rw [pfaffianAux_cons]
  change (∑ m : Fin 3, (-1) ^ (m : ℕ) * A i [j, k, l][m] * pfaffianAux A ([j, k, l].eraseIdx m)) = _
  rw [Fin.sum_univ_three]
  simp [pfaffianAux_pair]
  ring

example : pfaffianAux (fun a b : Fin 4 => ((a : ℕ) : ℤ) + 2 * ((b : ℕ) : ℤ)) [0, 1, 2, 3] = 18 := by
  decide

private theorem map_pfaffianFuel (f : R →+* S) (A : ι → ι → R) :
    ∀ (n : ℕ) (l : List ι),
      f (pfaffianFuel A n l) = pfaffianFuel (fun a b => f (A a b)) n l := by
  intro n
  induction n with
  | zero =>
    intro l
    cases l with
    | nil => simp only [pfaffianFuel, map_one]
    | cons i rest => simp only [pfaffianFuel, map_zero]
  | succ n ih =>
    intro l
    cases l with
    | nil => simp only [pfaffianFuel, map_one]
    | cons i rest =>
      simp only [pfaffianFuel, map_sum, map_mul, map_pow, map_neg, map_one, ih]

/-- A ring homomorphism carries the Pfaffian of a list to the Pfaffian of the mapped entries. -/
theorem map_pfaffianAux (f : R →+* S) (A : ι → ι → R) (l : List ι) :
    f (pfaffianAux A l) = pfaffianAux (fun a b => f (A a b)) l :=
  map_pfaffianFuel f A l.length l

private theorem pfaffianFuel_eq_zero_of_odd (A : ι → ι → R) :
    ∀ (n : ℕ) (l : List ι), l.length % 2 = 1 → pfaffianFuel A n l = 0 := by
  intro n
  induction n with
  | zero =>
    intro l h
    cases l with
    | nil => simp at h
    | cons i rest => simp only [pfaffianFuel]
  | succ n ih =>
    intro l h
    cases l with
    | nil => simp at h
    | cons i rest =>
      simp only [pfaffianFuel]
      refine Finset.sum_eq_zero fun k _ => ?_
      have hk := length_eraseIdx_fin rest k
      have hk' := k.isLt
      simp only [List.length_cons] at h
      rw [ih _ (by omega), mul_zero]

/-- A list of odd length has Pfaffian `0`: every term of the expansion removes one index from an
even-length remainder and leaves an odd-length list. -/
theorem pfaffianAux_eq_zero_of_odd (A : ι → ι → R) (l : List ι) (h : l.length % 2 = 1) :
    pfaffianAux A l = 0 :=
  pfaffianFuel_eq_zero_of_odd A l.length l h

private theorem pfaffianFuel_smul_of_even (c : R) (A : ι → ι → R) :
    ∀ (n : ℕ) (l : List ι), l.length % 2 = 0 →
      pfaffianFuel (fun a b => c * A a b) n l = c ^ (l.length / 2) * pfaffianFuel A n l := by
  intro n
  induction n with
  | zero =>
    intro l h
    cases l with
    | nil => simp only [pfaffianFuel, List.length_nil, Nat.zero_div, pow_zero, mul_one]
    | cons i rest => simp only [pfaffianFuel, mul_zero]
  | succ n ih =>
    intro l h
    cases l with
    | nil => simp only [pfaffianFuel, List.length_nil, Nat.zero_div, pow_zero, mul_one]
    | cons i rest =>
      simp only [pfaffianFuel]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk := length_eraseIdx_fin rest k
      have hk' := k.isLt
      simp only [List.length_cons] at h ⊢
      have e : (rest.eraseIdx k).length / 2 + 1 = (rest.length + 1) / 2 := by omega
      rw [ih _ (by omega), ← e]
      ring

/-- Scaling every entry by `c` scales the Pfaffian of a list of even length `2 m` by `c ^ m`. -/
theorem pfaffianAux_smul_of_even (c : R) (A : ι → ι → R) (l : List ι) (h : l.length % 2 = 0) :
    pfaffianAux (fun a b => c * A a b) l = c ^ (l.length / 2) * pfaffianAux A l :=
  pfaffianFuel_smul_of_even c A l.length l h

private def evalAt (A : ι → ι → R) (i : ι) : Option ι → R
  | none => 0
  | some x => A i x

private theorem pfaffianAux_cons_range (A : ι → ι → R) (i : ι) (rest : List ι) :
    pfaffianAux A (i :: rest) = ∑ k ∈ Finset.range rest.length,
      (-1) ^ k * evalAt A i rest[k]? * pfaffianAux A (rest.eraseIdx k) := by
  rw [pfaffianAux_cons]
  refine Eq.trans ?_ (Fin.sum_univ_eq_sum_range (fun k => (-1) ^ k * evalAt A i rest[k]? *
    pfaffianAux A (rest.eraseIdx k)) rest.length)
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [evalAt]

private def pfTerm (A : ι → ι → R) (i j : ι) (r : List ι) (m p : ℕ) : R :=
  (-1) ^ (m + 1) * evalAt A i r[m]? *
    ((-1) ^ p * evalAt A j (r.eraseIdx m)[p]? * pfaffianAux A ((r.eraseIdx m).eraseIdx p))

private theorem pfaffianAux_double (A : ι → ι → R) (i j : ι) (r : List ι) :
    pfaffianAux A (i :: j :: r) = A i j * pfaffianAux A r +
      ∑ m ∈ Finset.range r.length, ∑ p ∈ Finset.range (r.length - 1), pfTerm A i j r m p := by
  unfold pfTerm
  rw [pfaffianAux_cons_range, List.length_cons, Finset.sum_range_succ', add_comm]
  congr 1
  · simp [evalAt]
  · refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := Finset.mem_range.mp hm
    simp only [List.getElem?_cons_succ, List.eraseIdx_cons_succ]
    rw [pfaffianAux_cons_range, List.length_eraseIdx_of_lt hm', Finset.mul_sum]

private theorem eraseIdx_eraseIdx_succ (l : List ι) {p m : ℕ} (h : p ≤ m) :
    (l.eraseIdx (m + 1)).eraseIdx p = (l.eraseIdx p).eraseIdx m := by
  apply List.ext_getElem?
  intro q
  simp only [List.getElem?_eraseIdx]
  split_ifs <;> first | rfl | (exfalso; omega)

private theorem pfTerm_lt (A : ι → ι → R) (i j : ι) (r : List ι) {p m : ℕ} (h : p ≤ m) :
    pfTerm A j i r (m + 1) p = -pfTerm A i j r p m := by
  unfold pfTerm
  rw [List.getElem?_eraseIdx_of_lt (by omega : p < m + 1), eraseIdx_eraseIdx_succ r h,
    List.getElem?_eraseIdx_of_ge h]
  ring

private theorem pfTerm_ge (A : ι → ι → R) (i j : ι) (r : List ι) {m p : ℕ} (h : m ≤ p) :
    pfTerm A j i r m p = -pfTerm A i j r (p + 1) m := by
  unfold pfTerm
  rw [List.getElem?_eraseIdx_of_ge h, List.getElem?_eraseIdx_of_lt (by omega : m < p + 1),
    eraseIdx_eraseIdx_succ r h]
  ring

private def swapIdx (x : ℕ × ℕ) : ℕ × ℕ :=
  if x.2 < x.1 then (x.2, x.1 - 1) else (x.2 + 1, x.1)

private theorem swapIdx_lt {m p : ℕ} (h : p < m) : swapIdx (m, p) = (p, m - 1) := by
  simp [swapIdx, h]

private theorem swapIdx_ge {m p : ℕ} (h : m ≤ p) : swapIdx (m, p) = (p + 1, m) := by
  simp [swapIdx, not_lt.mpr h]

private theorem sum_pfTerm_swap (A : ι → ι → R) (i j : ι) (r : List ι) :
    ∑ m ∈ Finset.range r.length, ∑ p ∈ Finset.range (r.length - 1), pfTerm A j i r m p =
      -∑ m ∈ Finset.range r.length, ∑ p ∈ Finset.range (r.length - 1), pfTerm A i j r m p := by
  rw [← Finset.sum_product' (f := fun m p => pfTerm A j i r m p),
    ← Finset.sum_product' (f := fun m p => pfTerm A i j r m p), ← Finset.sum_neg_distrib]
  refine Finset.sum_nbij' swapIdx swapIdx ?_ ?_ ?_ ?_ ?_
  · rintro ⟨m, p⟩ hx
    simp only [Finset.mem_product, Finset.mem_range] at hx ⊢
    rcases lt_or_ge p m with h | h
    · rw [swapIdx_lt h]; dsimp only; omega
    · rw [swapIdx_ge h]; dsimp only; omega
  · rintro ⟨m, p⟩ hx
    simp only [Finset.mem_product, Finset.mem_range] at hx ⊢
    rcases lt_or_ge p m with h | h
    · rw [swapIdx_lt h]; dsimp only; omega
    · rw [swapIdx_ge h]; dsimp only; omega
  · rintro ⟨m, p⟩ _
    rcases lt_or_ge p m with h | h
    · rw [swapIdx_lt h, swapIdx_ge (by omega : p ≤ m - 1)]
      refine Prod.ext ?_ rfl
      dsimp only; omega
    · rw [swapIdx_ge h, swapIdx_lt (by omega : m < p + 1)]
      refine Prod.ext rfl ?_
      dsimp only; omega
  · rintro ⟨m, p⟩ _
    rcases lt_or_ge p m with h | h
    · rw [swapIdx_lt h, swapIdx_ge (by omega : p ≤ m - 1)]
      refine Prod.ext ?_ rfl
      dsimp only; omega
    · rw [swapIdx_ge h, swapIdx_lt (by omega : m < p + 1)]
      refine Prod.ext rfl ?_
      dsimp only; omega
  · rintro ⟨m, p⟩ _
    rcases lt_or_ge p m with h | h
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [swapIdx_lt h]
      simp only [Nat.add_sub_cancel]
      exact pfTerm_lt A i j r (by omega)
    · rw [swapIdx_ge h]
      exact pfTerm_ge A i j r h

/-- Swapping the first two indices of a list negates the Pfaffian when the entry between them
changes sign under the swap. -/
theorem pfaffianAux_swap (A : ι → ι → R) (i j : ι) (rest : List ι) (h : A j i = -A i j) :
    pfaffianAux A (j :: i :: rest) = -pfaffianAux A (i :: j :: rest) := by
  rw [pfaffianAux_double A j i rest, pfaffianAux_double A i j rest, sum_pfTerm_swap A i j rest, h]
  ring

/-- For a skew matrix, swapping the first two indices of a list negates the Pfaffian. -/
theorem pfaffianAux_swap_of_skew (A : ι → ι → R) (hA : ∀ a b, A a b = -A b a) (i j : ι)
    (rest : List ι) :
    pfaffianAux A (j :: i :: rest) = -pfaffianAux A (i :: j :: rest) :=
  pfaffianAux_swap A i j rest (hA j i)

/-- A list that starts with the same index twice has Pfaffian `0` when `2` is left-regular and
`A i i = -A i i`. -/
theorem pfaffianAux_eq_zero_of_repeat (A : ι → ι → R) (hreg : IsLeftRegular (2 : R)) (i : ι)
    (rest : List ι) (h : A i i = -A i i) : pfaffianAux A (i :: i :: rest) = 0 := by
  have hs := pfaffianAux_swap A i i rest h
  refine hreg ?_
  change 2 * _ = 2 * 0
  linear_combination hs

end Matrix
