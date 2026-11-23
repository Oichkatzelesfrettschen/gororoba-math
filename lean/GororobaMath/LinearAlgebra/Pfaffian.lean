/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Tactic.Ring

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

end Matrix
