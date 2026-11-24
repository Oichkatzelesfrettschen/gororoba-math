/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.LinearAlgebra.Pfaffian
public import Mathlib.Algebra.Module.Defs

/-!
# The Pfaffian of a list of vectors under a skew form

Convention: for a function `ω : V → V → R` on an `R`-module `V`, `Matrix.pfaffianAux ω l` on a
list `l` of vectors is the Pfaffian of the Gram matrix `ω l[i] l[j]` in list order, with the sign
convention of `GororobaMath.LinearAlgebra.Pfaffian`. The hypotheses on `ω` are stated as plain
arguments: `hadd` and `hsmul` (linearity in the first argument) and `hskew` (`ω x y = -ω y x`).

## Main results

* `Matrix.pfaffianAux_cons_add`, `Matrix.pfaffianAux_cons_smul`: linearity of the Pfaffian in the
  head vector.
* `Matrix.pfaffianAux_append_add`, `Matrix.pfaffianAux_append_smul`: linearity at any position of a
  skew form.
* `Matrix.pfaffianAux_append_add_smul_of_mem`: adding a multiple of another entry of the list
  leaves the Pfaffian unchanged when `2` is left-regular.
* `Matrix.pfaffianAux_eq_zero_of_zero_mem`: a zero vector in the list gives Pfaffian `0`.
-/

@[expose] public section

namespace Matrix

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

omit [Module R V] in
/-- The Pfaffian is additive in the head vector. -/
theorem pfaffianAux_cons_add (ω : V → V → R) (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z)
    (x y : V) (rest : List V) :
    pfaffianAux ω ((x + y) :: rest) = pfaffianAux ω (x :: rest) + pfaffianAux ω (y :: rest) := by
  rw [pfaffianAux_cons, pfaffianAux_cons, pfaffianAux_cons, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hadd]
  ring

/-- The Pfaffian is homogeneous in the head vector. -/
theorem pfaffianAux_cons_smul (ω : V → V → R) (hsmul : ∀ (c : R) x z, ω (c • x) z = c * ω x z)
    (c : R) (x : V) (rest : List V) :
    pfaffianAux ω ((c • x) :: rest) = c * pfaffianAux ω (x :: rest) := by
  rw [pfaffianAux_cons, pfaffianAux_cons, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hsmul]
  ring

omit [AddCommGroup V] [Module R V] in
private theorem move_head (ω : V → V → R) (hskew : ∀ x y, ω x y = -ω y x) (pre : List V)
    (y : V) (rest : List V) :
    pfaffianAux ω (pre ++ y :: rest) = (-1) ^ pre.length * pfaffianAux ω (y :: (pre ++ rest)) := by
  simpa using pfaffianAux_move_left ω hskew [] pre y rest

omit [Module R V] in
/-- The Pfaffian of a skew form is additive in the entry at any position. -/
theorem pfaffianAux_append_add (ω : V → V → R) (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z)
    (hskew : ∀ x y, ω x y = -ω y x) (pre : List V) (x y : V) (rest : List V) :
    pfaffianAux ω (pre ++ (x + y) :: rest) =
      pfaffianAux ω (pre ++ x :: rest) + pfaffianAux ω (pre ++ y :: rest) := by
  rw [move_head ω hskew, move_head ω hskew, move_head ω hskew, pfaffianAux_cons_add ω hadd]
  ring

/-- The Pfaffian of a skew form is homogeneous in the entry at any position. -/
theorem pfaffianAux_append_smul (ω : V → V → R) (hsmul : ∀ (c : R) x z, ω (c • x) z = c * ω x z)
    (hskew : ∀ x y, ω x y = -ω y x) (pre : List V) (c : R) (x : V) (rest : List V) :
    pfaffianAux ω (pre ++ (c • x) :: rest) = c * pfaffianAux ω (pre ++ x :: rest) := by
  rw [move_head ω hskew, move_head ω hskew, pfaffianAux_cons_smul ω hsmul]
  ring

omit [AddCommGroup V] in
private theorem not_nodup_of_mem (pre rest : List V) (y : V) (h : y ∈ pre ++ rest) :
    ¬ (pre ++ y :: rest).Nodup := by
  intro hn
  rw [List.nodup_append] at hn
  obtain ⟨_, h2, h3⟩ := hn
  rcases List.mem_append.mp h with hp | hr
  · exact h3 y hp y (List.mem_cons_self) rfl
  · exact (List.nodup_cons.mp h2).1 hr

/-- Adding a multiple of another entry of the list to one entry leaves the Pfaffian unchanged. -/
theorem pfaffianAux_append_add_smul_of_mem (ω : V → V → R)
    (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z) (hsmul : ∀ (c : R) x z, ω (c • x) z = c * ω x z)
    (hskew : ∀ x y, ω x y = -ω y x) (hreg : IsLeftRegular (2 : R)) (pre : List V) (x y : V)
    (c : R) (rest : List V) (hy : y ∈ pre ++ rest) :
    pfaffianAux ω (pre ++ (x + c • y) :: rest) = pfaffianAux ω (pre ++ x :: rest) := by
  rw [pfaffianAux_append_add ω hadd hskew, pfaffianAux_append_smul ω hsmul hskew,
    pfaffianAux_eq_zero_of_not_nodup ω hskew hreg _ (not_nodup_of_mem pre rest y hy), mul_zero,
    add_zero]

/-- A zero vector in the list gives Pfaffian `0`. -/
theorem pfaffianAux_eq_zero_of_zero_mem (ω : V → V → R)
    (hsmul : ∀ (c : R) x z, ω (c • x) z = c * ω x z) (hskew : ∀ x y, ω x y = -ω y x)
    (l : List V) (h : (0 : V) ∈ l) : pfaffianAux ω l = 0 := by
  obtain ⟨pre, rest, rfl⟩ := List.append_of_mem h
  have e : (0 : V) = (0 : R) • (0 : V) := (smul_zero _).symm
  rw [e, pfaffianAux_append_smul ω hsmul hskew, zero_mul]

end Matrix
