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
* `Matrix.pfaffianAux_cons_cons_map_transvect`: adding multiples of the first two entries to every
  later entry leaves the Pfaffian unchanged.
* `Matrix.decouple`, `Matrix.decouple_pair_left`, `Matrix.decouple_pair_right`: over a field with
  `2 ≠ 0` and `ω v w ≠ 0`, the tail map that makes every entry pair to zero with `v` and `w`.
* `Matrix.pfaffianAux_cons_cons_eq_mul_map_decouple`: `pfaffianAux ω (v :: w :: rest)` is
  `ω v w` times the Pfaffian of the decoupled tail.
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

private theorem map_transvect_aux (ω : V → V → R) (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z)
    (hsmul : ∀ (c : R) x z, ω (c • x) z = c * ω x z) (hskew : ∀ x y, ω x y = -ω y x)
    (hreg : IsLeftRegular (2 : R)) (v w : V) (α β : V → R) (done todo : List V) :
    pfaffianAux ω (v :: w :: (done.map (fun u => (u + α u • v) + β u • w) ++ todo)) =
      pfaffianAux ω (v :: w :: (done ++ todo)) := by
  induction done using List.reverseRecOn generalizing todo with
  | nil => simp
  | append_singleton done d ih =>
    have hv : v ∈ (v :: w :: done.map (fun u => (u + α u • v) + β u • w)) ++ todo := by simp
    have hw : w ∈ (v :: w :: done.map (fun u => (u + α u • v) + β u • w)) ++ todo := by simp
    have e1 : v :: w :: ((done ++ [d]).map (fun u => (u + α u • v) + β u • w) ++ todo) =
        (v :: w :: done.map (fun u => (u + α u • v) + β u • w)) ++
          ((d + α d • v) + β d • w) :: todo := by simp
    have e3 : v :: w :: (done.map (fun u => (u + α u • v) + β u • w) ++ d :: todo) =
        (v :: w :: done.map (fun u => (u + α u • v) + β u • w)) ++ d :: todo := by simp
    have e4 : v :: w :: (done ++ d :: todo) = v :: w :: ((done ++ [d]) ++ todo) := by simp
    rw [e1, pfaffianAux_append_add_smul_of_mem ω hadd hsmul hskew hreg _ _ w _ _ hw,
      pfaffianAux_append_add_smul_of_mem ω hadd hsmul hskew hreg _ _ v _ _ hv, ← e3, ih, e4]

/-- Replacing every tail entry `u` by `u + α u • v + β u • w` leaves the Pfaffian of
`v :: w :: rest` unchanged. -/
theorem pfaffianAux_cons_cons_map_transvect (ω : V → V → R)
    (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z) (hsmul : ∀ (c : R) x z, ω (c • x) z = c * ω x z)
    (hskew : ∀ x y, ω x y = -ω y x) (hreg : IsLeftRegular (2 : R)) (v w : V) (α β : V → R)
    (rest : List V) :
    pfaffianAux ω (v :: w :: rest.map (fun u => (u + α u • v) + β u • w)) =
      pfaffianAux ω (v :: w :: rest) := by
  simpa using map_transvect_aux ω hadd hsmul hskew hreg v w α β rest []

section Field

variable {K : Type*} [Field K] [Module K V]

omit [Module K V] in
private theorem add_right_of (ω : V → V → K) (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z)
    (hskew : ∀ x y, ω x y = -ω y x) (x y z : V) : ω x (y + z) = ω x y + ω x z := by
  rw [hskew x (y + z), hskew x y, hskew x z, hadd]
  ring

private theorem smul_right_of (ω : V → V → K) (hsmul : ∀ (c : K) x z, ω (c • x) z = c * ω x z)
    (hskew : ∀ x y, ω x y = -ω y x) (c : K) (x y : V) : ω x (c • y) = c * ω x y := by
  rw [hskew x (c • y), hskew x y, hsmul]
  ring

omit [AddCommGroup V] [Module K V] in
private theorem self_eq_zero_of (ω : V → V → K) (hskew : ∀ x y, ω x y = -ω y x)
    (h2 : (2 : K) ≠ 0) (x : V) : ω x x = 0 := by
  have h : (2 : K) * ω x x = 0 := by linear_combination hskew x x
  exact (mul_eq_zero.mp h).resolve_left h2

/-- The tail map that makes both pairings with `v` and `w` vanish. -/
def decouple (ω : V → V → K) (v w u : V) : V :=
  (u + (ω w u / ω v w) • v) + (-(ω v u / ω v w)) • w

/-- The decoupled tail entry pairs to zero with `v`. -/
theorem decouple_pair_left (ω : V → V → K) (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z)
    (hsmul : ∀ (c : K) x z, ω (c • x) z = c * ω x z) (hskew : ∀ x y, ω x y = -ω y x)
    (h2 : (2 : K) ≠ 0) (v w u : V) (ha : ω v w ≠ 0) : ω v (decouple ω v w u) = 0 := by
  unfold decouple
  rw [add_right_of ω hadd hskew, add_right_of ω hadd hskew, smul_right_of ω hsmul hskew,
    smul_right_of ω hsmul hskew, self_eq_zero_of ω hskew h2 v]
  have := div_mul_cancel₀ (ω v u) ha
  linear_combination (-1 : K) * this

/-- The decoupled tail entry pairs to zero with `w`. -/
theorem decouple_pair_right (ω : V → V → K) (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z)
    (hsmul : ∀ (c : K) x z, ω (c • x) z = c * ω x z) (hskew : ∀ x y, ω x y = -ω y x)
    (h2 : (2 : K) ≠ 0) (v w u : V) (ha : ω v w ≠ 0) : ω w (decouple ω v w u) = 0 := by
  unfold decouple
  rw [add_right_of ω hadd hskew, add_right_of ω hadd hskew, smul_right_of ω hsmul hskew,
    smul_right_of ω hsmul hskew, self_eq_zero_of ω hskew h2 w, hskew w v]
  have := div_mul_cancel₀ (ω w u) ha
  linear_combination (-1 : K) * this

/-- Reduction by a nondegenerate pair: `pfaffianAux ω (v :: w :: rest)` is `ω v w` times the
Pfaffian of the decoupled tail. -/
theorem pfaffianAux_cons_cons_eq_mul_map_decouple (ω : V → V → K)
    (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z) (hsmul : ∀ (c : K) x z, ω (c • x) z = c * ω x z)
    (hskew : ∀ x y, ω x y = -ω y x) (h2 : (2 : K) ≠ 0) (v w : V) (rest : List V)
    (ha : ω v w ≠ 0) :
    pfaffianAux ω (v :: w :: rest) = ω v w * pfaffianAux ω (rest.map (decouple ω v w)) := by
  have hreg : IsLeftRegular (2 : K) := mul_right_injective₀ h2
  rw [← pfaffianAux_cons_cons_map_transvect ω hadd hsmul hskew hreg v w (fun u => ω w u / ω v w)
    (fun u => -(ω v u / ω v w)) rest]
  exact pfaffianAux_pair_cons_of_zero ω v _ _ (fun x hx => by
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
    exact decouple_pair_left ω hadd hsmul hskew h2 v w u ha)

end Field

end Matrix
