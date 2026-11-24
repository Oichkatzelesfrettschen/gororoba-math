(** * Two-blade products of the sedenion algebra: the norm census of
    the 210 two-blades.

    Convention.  A vector is a list of terms (index, integer coefficient),
    not necessarily merged by index; the basis product is
    e_p * e_q = sed_sign p q * e_{p XOR q} with the table [sed_sign] of
    [C1467_XORSignCocycle] (bound to the bounded recurrence by
    [sed_sign_table_correct], which reads as [cd_sign] of
    gororoba_quantum/cd_core.py at dimension 16; no comparison under ci/
    runs this table against cd_core.py).  [smul] multiplies two term lists by
    bilinearity, [scoef v n] is the coefficient of e_n in the sum of the
    terms of v, and [snorm2] is the sum over n < 16 of the squares of those
    coefficients.  A two-blade is e_i + t e_j with 1 <= i < j <= 15 and
    t = +1 or -1 (105 x 2 = 210 two-blades); [bnorm a b] is the squared
    norm N of the product a * b.

    Row answered: gororoba-quantum docs/evidence/box_kite_census/README.md
    line 46 (two-blade products).
    - [bnorm_hist]: over the 210 x 210 = 44100 ordered products the
      squared norm N is 0 for 336, 4 for 43428 and 8 for 336, and for none
      else.
    - [zero_products_commute_zero]: a product is zero in one order exactly
      when it is zero in the other (the zero products hold in both orders).
    - [zd_planes_are_assessors]: the planes (i, j) carrying a zero product
      are the 42 planes with i < 8 < j and i XOR j <> 8; the 7 planes
      (l, l XOR 8) carry none.
    - [zd_blade_count]: 84 two-blades take part in a zero product.
    The 336 zero products agree with the corpus
    [sedenion_zero_divisor_corpus] of cd_core.py only through the check of
    scripts/box_kite_census.py; no Rocq statement names that corpus. *)

From Stdlib Require Import Arith PeanoNat Bool List ZArith.
From OpenGororobaVerified Require Import C1467_XORSignCocycle.
Import ListNotations.

Open Scope Z_scope.

Definition svec : Type := list (nat * Z).

Definition smul (x y : svec) : svec :=
  flat_map (fun xa => map (fun yb =>
      (Nat.lxor (fst xa) (fst yb),
       snd xa * snd yb * sed_sign (fst xa) (fst yb))) y) x.

Definition scoef (v : svec) (n : nat) : Z :=
  fold_left Z.add (map snd (filter (fun t => Nat.eqb (fst t) n) v)) 0.

Definition idx16 : list nat := seq 0 16.

Definition snorm2 (v : svec) : Z :=
  fold_left Z.add (map (fun n => scoef v n * scoef v n) idx16) 0.

Definition blade : Type := (nat * nat * Z)%type.

Definition bvec (b : blade) : svec :=
  let '(i, j, t) := b in [(i, 1); (j, t)].

Definition blades : list blade :=
  flat_map (fun i => flat_map (fun j => [(i, j, 1); (i, j, -1)])
                              (seq (S i) (15 - i))) (seq 1 15).

Definition bnorm (a b : blade) : Z := snorm2 (smul (bvec a) (bvec b)).

Definition cnt {A : Type} (f : A -> bool) (l : list A) : N :=
  fold_left (fun a x => if f x then N.succ a else a) l 0%N.

Definition blade_pairs : list (blade * blade) := list_prod blades blades.

Theorem blades_count : length blades = 210%nat.
Proof. vm_compute. reflexivity. Qed.

Definition norm_hist : N * N * N * N :=
  fold_left (fun h p =>
    let '(n0, n4, n8, no) := h in
    let n := bnorm (fst p) (snd p) in
    if Z.eqb n 0 then (N.succ n0, n4, n8, no)
    else if Z.eqb n 4 then (n0, N.succ n4, n8, no)
    else if Z.eqb n 8 then (n0, n4, N.succ n8, no)
    else (n0, n4, n8, N.succ no)) blade_pairs (0, 0, 0, 0)%N.

(** (N = 0, N = 4, N = 8, any other N) over the 44100 ordered products. *)
Theorem bnorm_hist : norm_hist = (336%N, 43428%N, 336%N, 0%N).
Proof. vm_compute. reflexivity. Qed.

Theorem zero_products_commute_zero :
  forallb (fun p => implb (Z.eqb (bnorm (fst p) (snd p)) 0)
                          (Z.eqb (bnorm (snd p) (fst p)) 0)) blade_pairs
  = true.
Proof. vm_compute. reflexivity. Qed.

Definition planes : list (nat * nat) :=
  flat_map (fun i => map (fun j => (i, j)) (seq (S i) (15 - i))) (seq 1 15).

Definition zero_bearing (i j : nat) : bool :=
  existsb (fun s => existsb (fun b => Z.eqb (bnorm (i, j, s) b) 0) blades)
          [1; -1].

Definition zd_planes : list (nat * nat) :=
  filter (fun p => zero_bearing (fst p) (snd p)) planes.

Definition mem_plane (p : nat * nat) (l : list (nat * nat)) : bool :=
  existsb (fun q => Nat.eqb (fst p) (fst q) && Nat.eqb (snd p) (snd q)) l.

Definition assessor_plane (p : nat * nat) : bool :=
  Nat.ltb (fst p) 8 && Nat.ltb 8 (snd p)
  && negb (Nat.eqb (Nat.lxor (fst p) (snd p)) 8).

Theorem zd_planes_are_assessors :
  zd_planes = filter assessor_plane planes /\ length zd_planes = 42%nat.
Proof. split; vm_compute; reflexivity. Qed.

Theorem nonkite_planes_carry_none :
  forallb (fun l => negb (zero_bearing l (Nat.lxor l 8))) (seq 1 7) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zd_blade_count :
  cnt (fun a => existsb (fun b => Z.eqb (bnorm a b) 0) blades) blades
  = 84%N.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions blades_count.
Print Assumptions bnorm_hist.
Print Assumptions zero_products_commute_zero.
Print Assumptions zd_planes_are_assessors.
Print Assumptions nonkite_planes_carry_none.
Print Assumptions zd_blade_count.
