/- SPDX-License-Identifier: Apache-2.0 -/
module

public import GororobaMath.LinearAlgebra.Pfaffian
public import Mathlib.Algebra.Module.Defs
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Tactic.Module
public import Mathlib.LinearAlgebra.StdBasis

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
* `Matrix.decoupleₗ`, `Matrix.ker_decoupleₗ`: the decoupling map is linear with kernel the plane of
  `v` and `w`.
* `Matrix.indep_map_decouple`: the decoupled tail of an independent list is independent and
  repetition free.
* `Matrix.orth_of_mem_span_map_decouple`: a combination of decoupled entries pairs to zero with
  `v` and `w`.
* `Matrix.exists_orth_of_pfaffianAux_eq_zero`: an independent list with zero Pfaffian has a nonzero
  vector in its span that pairs to zero with every entry. Independence is stated as
  `l.Nodup` with `LinearIndepOn K id {x | x ∈ l}`.
* `Matrix.pfaffianAux_reindex`: the Pfaffian of pulled-back entries is the Pfaffian on the image
  list.
* `Matrix.pfaffianAux_congr`: the Pfaffian on a list depends only on the entries at pairs of its
  members.
* `Matrix.exists_vecMul_eq_zero_of_pfaffian_eq_zero`,
  `Matrix.exists_mulVec_eq_zero_of_pfaffian_eq_zero`: a skew matrix over a field with `2 ≠ 0`
  and zero Pfaffian has a nonzero kernel vector.
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

omit [AddCommGroup V] [Module R V] in
/-- Reindexing: the Pfaffian of the pulled-back entries `A (g a) (g b)` on a list is the Pfaffian
of `A` on the image list. -/
theorem pfaffianAux_reindex {ι κ : Type*} (A : ι → ι → R) (g : κ → ι) :
    ∀ (n : ℕ) (l : List κ), l.length = n →
      pfaffianAux (fun a b => A (g a) (g b)) l = pfaffianAux A (l.map g) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hn
  cases l with
  | nil => simp only [List.map_nil, pfaffianAux_nil]
  | cons i rest =>
    rw [pfaffianAux_cons, List.map_cons, pfaffianAux_cons]
    refine Fintype.sum_equiv (finCongr (by simp)) _ _ (fun k => ?_)
    have hlt : (rest.eraseIdx k).length < n := by
      have := List.length_eraseIdx_of_lt k.isLt
      simp only [List.length_cons] at hn
      omega
    simp only [finCongr_apply, Fin.val_cast]
    rw [List.eraseIdx_map, ← ih _ hlt (rest.eraseIdx k) rfl]
    simp [List.getElem_map]

omit [AddCommGroup V] [Module R V] in
/-- The Pfaffian on a list reads the matrix only at pairs of entries of the list. -/
theorem pfaffianAux_congr {ι : Type*} (A B : ι → ι → R) :
    ∀ (n : ℕ) (l : List ι), l.length = n → (∀ a ∈ l, ∀ b ∈ l, A a b = B a b) →
      pfaffianAux A l = pfaffianAux B l := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hn h
  cases l with
  | nil => simp only [pfaffianAux_nil]
  | cons i rest =>
    rw [pfaffianAux_cons, pfaffianAux_cons]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hlt : (rest.eraseIdx k).length < n := by
      have := List.length_eraseIdx_of_lt k.isLt
      simp only [List.length_cons] at hn
      omega
    have hsub : ∀ a ∈ rest.eraseIdx k, a ∈ i :: rest := fun a ha =>
      List.mem_cons_of_mem _ ((List.eraseIdx_sublist _ _).subset ha)
    rw [h i List.mem_cons_self rest[k] (by simp),
      ih _ hlt (rest.eraseIdx k) rfl fun a ha b hb => h a (hsub a ha) b (hsub b hb)]

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

/-- The decoupling map sends `v` to `0`. -/
theorem decouple_left (ω : V → V → K) (hskew : ∀ x y, ω x y = -ω y x) (h2 : (2 : K) ≠ 0)
    (v w : V) (ha : ω v w ≠ 0) : decouple ω v w v = 0 := by
  unfold decouple
  have h1 : (-ω v w) / ω v w = -1 := by rw [neg_div, div_self ha]
  rw [hskew w v, self_eq_zero_of ω hskew h2 v, h1, zero_div, neg_zero]
  module

/-- The decoupling map sends `w` to `0`. -/
theorem decouple_right (ω : V → V → K) (hskew : ∀ x y, ω x y = -ω y x) (h2 : (2 : K) ≠ 0)
    (v w : V) (ha : ω v w ≠ 0) : decouple ω v w w = 0 := by
  unfold decouple
  rw [self_eq_zero_of ω hskew h2 w, zero_div, div_self ha]
  module

/-- The decoupling map as a linear map. -/
def decoupleₗ (ω : V → V → K) (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z)
    (hsmul : ∀ (c : K) x z, ω (c • x) z = c * ω x z) (hskew : ∀ x y, ω x y = -ω y x)
    (v w : V) : V →ₗ[K] V where
  toFun := decouple ω v w
  map_add' x y := by
    unfold decouple
    rw [add_right_of ω hadd hskew, add_right_of ω hadd hskew]
    module
  map_smul' c x := by
    simp only [RingHom.id_apply]
    unfold decouple
    rw [smul_right_of ω hsmul hskew, smul_right_of ω hsmul hskew]
    module

/-- The entry `u` differs from its decoupled image by a combination of `v` and `w`. -/
theorem decouple_decomp (ω : V → V → K) (v w u : V) :
    u = (decouple ω v w u + (-(ω w u / ω v w)) • v) + (ω v u / ω v w) • w := by
  unfold decouple
  module

/-- The kernel of the decoupling map is the plane spanned by `v` and `w`. -/
theorem ker_decoupleₗ (ω : V → V → K) (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z)
    (hsmul : ∀ (c : K) x z, ω (c • x) z = c * ω x z) (hskew : ∀ x y, ω x y = -ω y x)
    (h2 : (2 : K) ≠ 0) (v w : V) (ha : ω v w ≠ 0) :
    LinearMap.ker (decoupleₗ ω hadd hsmul hskew v w) = Submodule.span K {v, w} := by
  apply le_antisymm
  · intro u hu
    have h0 : decouple ω v w u = 0 := hu
    have e := decouple_decomp ω v w u
    rw [h0, zero_add] at e
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · refine Submodule.span_le.mpr ?_
    rintro x (rfl | rfl)
    · exact decouple_left ω hskew h2 x w ha
    · exact decouple_right ω hskew h2 v x ha

/-- A decoupled list of an independent list is independent and repetition free. -/
theorem indep_map_decouple (ω : V → V → K) (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z)
    (hsmul : ∀ (c : K) x z, ω (c • x) z = c * ω x z) (hskew : ∀ x y, ω x y = -ω y x)
    (h2 : (2 : K) ≠ 0) (v w : V) (rest : List V) (ha : ω v w ≠ 0)
    (hnd : (v :: w :: rest).Nodup) (hli : LinearIndepOn K id {x | x ∈ v :: w :: rest}) :
    (rest.map (decouple ω v w)).Nodup ∧
      LinearIndepOn K id {x | x ∈ rest.map (decouple ω v w)} := by
  have hU : {x | x ∈ v :: w :: rest} = {x | x ∈ rest} ∪ ({v, w} : Set V) := by
    ext x
    simp only [List.mem_cons, Set.mem_ofPred_eq, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    tauto
  have hn1 := List.nodup_cons.mp hnd
  have hn2 := List.nodup_cons.mp hn1.2
  have hdisj : Disjoint {x | x ∈ rest} ({v, w} : Set V) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rcases hx' with rfl | hx'
    · exact hn1.1 (List.mem_cons_of_mem _ hx)
    · rw [Set.mem_singleton_iff] at hx'
      subst hx'
      exact hn2.1 hx
  rw [hU] at hli
  obtain ⟨hT, _, hD⟩ := (linearIndepOn_union_iff (v := id) hdisj).mp hli
  simp only [Set.image_id] at hD
  have hker : Disjoint (Submodule.span K {x | x ∈ rest})
      (LinearMap.ker (decoupleₗ ω hadd hsmul hskew v w)) := by
    rw [ker_decoupleₗ ω hadd hsmul hskew h2 v w ha]
    exact hD
  refine ⟨?_, ?_⟩
  · refine List.Nodup.map_on (fun x hx y hy hxy => ?_) hn2.2
    have h1 : x - y ∈ Submodule.span K {x | x ∈ rest} :=
      Submodule.sub_mem _ (Submodule.subset_span hx) (Submodule.subset_span hy)
    have h2' : x - y ∈ LinearMap.ker (decoupleₗ ω hadd hsmul hskew v w) := by
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.mpr hxy
    exact sub_eq_zero.mp ((Submodule.disjoint_def.mp hker) _ h1 h2')
  · have himg := hT.image (f := decoupleₗ ω hadd hsmul hskew v w) hker
    convert himg using 1
    ext y
    simp only [Set.mem_ofPred_eq, List.mem_map, Set.mem_image]
    exact Iff.rfl

/-- A combination of decoupled entries pairs to zero with `v` and `w`. -/
theorem orth_of_mem_span_map_decouple (ω : V → V → K)
    (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z) (hsmul : ∀ (c : K) x z, ω (c • x) z = c * ω x z)
    (hskew : ∀ x y, ω x y = -ω y x) (h2 : (2 : K) ≠ 0) (v w : V) (rest : List V)
    (ha : ω v w ≠ 0) (u : V) (hu : u ∈ Submodule.span K {x | x ∈ rest.map (decouple ω v w)}) :
    ω u v = 0 ∧ ω u w = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    rw [hskew _ v, hskew _ w, decouple_pair_left ω hadd hsmul hskew h2 v w y ha,
      decouple_pair_right ω hadd hsmul hskew h2 v w y ha]
    simp
  | zero =>
    have h := hsmul 0 0
    simp only [zero_smul, zero_mul] at h
    exact ⟨h v, h w⟩
  | add x y _ _ hx hy =>
    rw [hadd, hadd, hx.1, hx.2, hy.1, hy.2]
    simp
  | smul a x _ hx =>
    rw [hsmul, hsmul, hx.1, hx.2]
    simp

private theorem exists_orth_aux (ω : V → V → K)
    (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z) (hsmul : ∀ (c : K) x z, ω (c • x) z = c * ω x z)
    (hskew : ∀ x y, ω x y = -ω y x) (h2 : (2 : K) ≠ 0) :
    ∀ (n : ℕ) (l : List V), l.length = n → l.Nodup → LinearIndepOn K id {x | x ∈ l} →
      pfaffianAux ω l = 0 →
        ∃ u ∈ Submodule.span K {x | x ∈ l}, u ≠ 0 ∧ ∀ x ∈ l, ω u x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro l hn hnd hli hp
  cases l with
  | nil =>
    rw [pfaffianAux_nil] at hp
    exact absurd hp one_ne_zero
  | cons v rest =>
    by_cases h : ∀ x ∈ rest, ω v x = 0
    · refine ⟨v, Submodule.subset_span (by simp), ?_, ?_⟩
      · exact hli.ne_zero (i := v) (by simp)
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact self_eq_zero_of ω hskew h2 x
        · exact h x hx
    · push Not at h
      obtain ⟨w, hw, hvw⟩ := h
      obtain ⟨r1, r2, rfl⟩ := List.append_of_mem hw
      have hperm : (v :: (r1 ++ w :: r2)).Perm (v :: w :: (r1 ++ r2)) :=
        List.Perm.cons v List.perm_middle
      have hnd' := hperm.nodup_iff.mp hnd
      have hli' : LinearIndepOn K id {x | x ∈ v :: w :: (r1 ++ r2)} := by
        have e : {x | x ∈ v :: w :: (r1 ++ r2)} = {x | x ∈ v :: (r1 ++ w :: r2)} := by
          ext x
          exact hperm.mem_iff.symm
        rw [e]
        exact hli
      have hreg : IsLeftRegular (2 : K) := mul_right_injective₀ h2
      have hmv := pfaffianAux_move_left ω hskew [v] r1 w r2
      have e1 : [v] ++ r1 ++ w :: r2 = v :: (r1 ++ w :: r2) := by simp
      have e2 : [v] ++ w :: (r1 ++ r2) = v :: w :: (r1 ++ r2) := by simp
      rw [e1, e2, hp] at hmv
      have hX : pfaffianAux ω (v :: w :: (r1 ++ r2)) = 0 := by
        rcases mul_eq_zero.mp hmv.symm with h | h
        · exact absurd h (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        · exact h
      have hL3 := pfaffianAux_cons_cons_eq_mul_map_decouple ω hadd hsmul hskew h2 v w (r1 ++ r2) hvw
      rw [hX] at hL3
      have hpf : pfaffianAux ω ((r1 ++ r2).map (decouple ω v w)) = 0 :=
        (mul_eq_zero.mp hL3.symm).resolve_left hvw
      obtain ⟨hnd2, hli2⟩ := indep_map_decouple ω hadd hsmul hskew h2 v w (r1 ++ r2) hvw hnd' hli'
      have hlen : ((r1 ++ r2).map (decouple ω v w)).length < n := by
        simp only [List.length_cons, List.length_append, List.length_map] at hn ⊢
        omega
      obtain ⟨u, hu, hu0, hu1⟩ := ih _ hlen _ rfl hnd2 hli2 hpf
      obtain ⟨huv, huw⟩ := orth_of_mem_span_map_decouple ω hadd hsmul hskew h2 v w (r1 ++ r2) hvw
        u hu
      refine ⟨u, ?_, hu0, ?_⟩
      · refine (Submodule.span_le.mpr ?_) hu
        intro y hy
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
        have hxl : x ∈ v :: (r1 ++ w :: r2) := by
          simp only [List.mem_cons, List.mem_append] at hx ⊢
          tauto
        have hvl : v ∈ v :: (r1 ++ w :: r2) := by simp
        have hwl : w ∈ v :: (r1 ++ w :: r2) := by simp
        exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.subset_span hxl)
          (Submodule.smul_mem _ _ (Submodule.subset_span hvl)))
          (Submodule.smul_mem _ _ (Submodule.subset_span hwl))
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact huv
        · rcases List.mem_append.mp hx with hx | hx
          · have hxr : x ∈ r1 ++ r2 := List.mem_append_left _ hx
            have hd := congrArg (ω u) (decouple_decomp ω v w x)
            rw [hd, add_right_of ω hadd hskew, add_right_of ω hadd hskew,
              smul_right_of ω hsmul hskew, smul_right_of ω hsmul hskew, huv, huw,
              hu1 _ (List.mem_map_of_mem hxr)]
            simp
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact huw
            · have hxr : x ∈ r1 ++ r2 := List.mem_append_right _ hx
              have hd := congrArg (ω u) (decouple_decomp ω v w x)
              rw [hd, add_right_of ω hadd hskew, add_right_of ω hadd hskew,
                smul_right_of ω hsmul hskew, smul_right_of ω hsmul hskew, huv, huw,
                hu1 _ (List.mem_map_of_mem hxr)]
              simp

/-- A repetition-free list of linearly independent vectors with zero Pfaffian has a nonzero vector
in its span that pairs to zero under `ω` with every entry. -/
theorem exists_orth_of_pfaffianAux_eq_zero (ω : V → V → K)
    (hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z) (hsmul : ∀ (c : K) x z, ω (c • x) z = c * ω x z)
    (hskew : ∀ x y, ω x y = -ω y x) (h2 : (2 : K) ≠ 0) (l : List V) (hnd : l.Nodup)
    (hli : LinearIndepOn K id {x | x ∈ l}) (hp : pfaffianAux ω l = 0) :
    ∃ u ∈ Submodule.span K {x | x ∈ l}, u ≠ 0 ∧ ∀ x ∈ l, ω u x = 0 :=
  exists_orth_aux ω hadd hsmul hskew h2 l.length l rfl hnd hli hp

omit [Module K V] in
private theorem gram_skew {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, A i j = -A j i)
    (x y : Fin n → K) :
    dotProduct x (A.mulVec y) = -dotProduct y (A.mulVec x) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hA i j]
  ring

/-- A skew matrix over a field with `2 ≠ 0` and zero Pfaffian has a nonzero kernel vector. -/
theorem exists_vecMul_eq_zero_of_pfaffian_eq_zero (h2 : (2 : K) ≠ 0) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, A i j = -A j i) (h : pfaffian A = 0) :
    ∃ v : Fin n → K, v ≠ 0 ∧ Matrix.vecMul v A = 0 := by
  let b := Pi.basisFun K (Fin n)
  let ω : (Fin n → K) → (Fin n → K) → K := fun x y => dotProduct x (A.mulVec y)
  have hmb : ∀ j, A.mulVec (b j) = fun i => A i j := by
    intro j
    ext i
    simp [b, Pi.basisFun_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  have gram : ∀ i j, ω (b i) (b j) = A i j := by
    intro i j
    simp only [ω, hmb]
    simp [b, Pi.basisFun_apply, dotProduct, Pi.single_apply]
  have hadd : ∀ x y z, ω (x + y) z = ω x z + ω y z := fun x y z => add_dotProduct _ _ _
  have hsmul : ∀ (c : K) x z, ω (c • x) z = c * ω x z := fun c x z => by
    simp only [ω, smul_dotProduct, smul_eq_mul]
  have hskew : ∀ x y, ω x y = -ω y x := gram_skew A hA
  have hpf : pfaffianAux ω ((List.finRange n).map b) = 0 := by
    rw [← pfaffianAux_reindex ω b n _ (List.length_finRange), ← h]
    have e : (fun a c => ω (b a) (b c)) = A := funext fun a => funext fun c => gram a c
    rw [e]
    rfl
  have hnd : ((List.finRange n).map b).Nodup := (List.nodup_finRange n).map b.injective
  have hli : LinearIndepOn K id {x | x ∈ (List.finRange n).map b} := by
    have e : {x | x ∈ (List.finRange n).map b} = Set.range b := by
      ext x
      simp [List.mem_map, Set.mem_range]
    rw [e]
    exact b.linearIndependent.linearIndepOn_id
  obtain ⟨u, _, hu0, hu⟩ := exists_orth_of_pfaffianAux_eq_zero ω hadd hsmul hskew h2 _ hnd hli hpf
  refine ⟨u, hu0, ?_⟩
  funext j
  have := hu (b j) (List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩)
  simp only [ω, hmb] at this
  exact this

/-- The same kernel vector annihilates the matrix from the other side. -/
theorem exists_mulVec_eq_zero_of_pfaffian_eq_zero (h2 : (2 : K) ≠ 0) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, A i j = -A j i) (h : pfaffian A = 0) :
    ∃ v : Fin n → K, v ≠ 0 ∧ A.mulVec v = 0 := by
  obtain ⟨v, hv0, hv⟩ := exists_vecMul_eq_zero_of_pfaffian_eq_zero h2 A hA h
  refine ⟨v, hv0, ?_⟩
  funext i
  have hi := congrFun hv i
  simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at hi
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
  calc ∑ j, A i j * v j = -∑ j, v j * A j i := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hA i j]
        ring
    _ = 0 := by rw [hi, neg_zero]

end Field

end Matrix
