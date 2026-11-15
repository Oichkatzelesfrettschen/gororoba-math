(** The kernel of left multiplication by e_1 + e_18 on A_5, as a certificate over the integers.

    The lemmas of CdTowerKernelCertificate.v take an element y of level 5, n vectors, n functionals, a table
    back of 32 images and a scalar d, with three finite checks over Z. Here y = e_1 + e_18 (coordinate
    indices 1 and 18, first half first, as in CdTowerCanonicalKernels.v), n = 12 and d = 2, so over every
    commutative ring where the image of 2 is invertible the kernel is free of rank 12, the rank that
    CayleyDickson.Tower.finrank_ker_pathion_1_18 of the Lean library states over the rationals and
    finrank_ker_pathion_1_18_int over the integers.

    The tables follow the block structure of left multiplication by y. The involution x -> x xor 19 pairs the
    32 basis indices into 16 blocks {x, x xor 19}, and y maps the block of x onto the block {x xor 1, x xor 18}
    by a 2 x 2 matrix A of entries +1 and -1, whose determinant is 0 or +-2. Twelve blocks have determinant 0:
    for each, the vector is e_x + s e_(x xor 19) with the sign s that y annihilates, the functional is 2 e_x*
    (the coordinate at x, doubled), and back sends e_(x xor 1) to -2 s A_00 e_(x xor 19) and e_(x xor 18)
    to 0. Four blocks have determinant +-2: back is 2 A^(-1), an integer matrix, on the images of that block.
    Vectors are ordered by the smallest index of their block. *)

From Stdlib Require Import ZArith List Lia PeanoNat Ring Zmod.
Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange CdTowerKernelCertificate.
Require CdTowerCanonicalKernels.
Import ListNotations.

Module E1E18Kernel (D : CommutativeRing).
Module H := IntegerHom D.
Module KC := KernelCertificate IntegerRing D H.
Import KC KC.BC.
Local Open Scope Z_scope.

(** The element of level k with the coordinates of a list, first half first. *)
Fixpoint of_list (k : nat) (l : list Z) : TA.cd k :=
  match k with
  | O => hd 0 l
  | S j => (of_list j (firstn (Nat.pow 2 j) l), of_list j (skipn (Nat.pow 2 j) l))
  end.

Definition row (table : list (list Z)) (j : nat) : TA.cd 5 := of_list 5 (nth j table []).

Tactic Notation "below" integer(bound) tactic3(run) :=
  let j := fresh "j" in let Hj := fresh "Hj" in
  intros j Hj; do bound (destruct j as [|j]; [run |]); exfalso; lia.

(** y = e_1 + e_18, nullity 12, d = 2. *)
Definition point : TA.cd 5 := of_list 5 [0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0].
Definition vectors : nat -> TA.cd 5 := row
    [[0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; (-1); 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; (-1); 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; (-1); 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; (-1); 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; (-1)];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; (-1); 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0]].
Definition functionals : nat -> TA.cd 5 := row
    [[0; 0; 0; 0; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]].
Definition back : nat -> TA.cd 5 := row
    [[0; (-1); 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; (-1); 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; (-1); 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; (-1); 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; (-1); 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; (-2); 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; (-2); 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; (-2); 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; (-2); 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; (-2); 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; (-2)];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 2; 0; 0];
     [0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; (-1); 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; (-1); 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 1; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; (-1); 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0];
     [0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0; 0]].

Lemma vectors_annihilated : forall j, (j < 12)%nat ->
  TA.mul 5 point (vectors j) = TA.zero 5.
Proof. below 12 (vm_compute; reflexivity). Qed.

Lemma splitting_on_basis : forall i, (i < Nat.pow 2 5)%nat ->
  TA.scale 5 2 (SA.basis 5 i) =
  TA.add 5 (source_map 5 back (TA.mul 5 point (SA.basis 5 i)))
           (source_comb 5 12 functionals vectors (SA.basis 5 i)).
Proof. change (Nat.pow 2 5) with 32%nat. below 32 (vm_compute; reflexivity). Qed.

Lemma functionals_dual : forall j l, (j < 12)%nat -> (l < 12)%nat ->
  source_pair 5 (functionals j) (vectors l) = if Nat.eqb j l then 2 else 0.
Proof.
  intros j l Hj Hl. revert l Hl. do 12 (destruct j as [|j]; [below 12 (vm_compute; reflexivity) |]).
  exfalso; lia.
Qed.

Theorem kernel_vectors : forall j, (j < 12)%nat ->
  TB.mul 5 (tmap 5 point) (tmap 5 (vectors j)) = TB.zero 5.
Proof. exact (KC.kernel_vectors 5 12 point vectors vectors_annihilated). Qed.

Theorem kernel_spanned : forall z, TB.mul 5 (tmap 5 point) z = TB.zero 5 ->
  TB.scale 5 (H.h 2) z = target_comb 5 12 functionals vectors z.
Proof.
  exact (KC.kernel_spanned 5 12 point 2 back functionals vectors splitting_on_basis).
Qed.

Theorem coefficients_recovered (a : nat -> D.t) : forall l, (l < 12)%nat ->
  target_pair 5 (tmap 5 (functionals l))
    (SB.tsum 5 12 (fun j => TB.scale 5 (a j) (tmap 5 (vectors j)))) = D.mul (H.h 2) (a l).
Proof.
  exact (KC.coefficients_recovered 5 12 2 functionals vectors functionals_dual a).
Qed.

Theorem combination_zero_coefficients (a : nat -> D.t) :
  SB.tsum 5 12 (fun j => TB.scale 5 (a j) (tmap 5 (vectors j))) = TB.zero 5 ->
  forall l, (l < 12)%nat -> D.mul (H.h 2) (a l) = D.zero.
Proof.
  exact (KC.combination_zero_coefficients 5 12 2 functionals vectors functionals_dual a).
Qed.

Theorem kernel_free_basis (inverse : D.t) : D.mul (H.h 2) inverse = D.one -> forall z,
  TB.mul 5 (tmap 5 point) z = TB.zero 5 <->
  z = SB.tsum 5 12 (fun j => TB.scale 5 (D.mul inverse (target_pair 5 (tmap 5 (functionals j)) z))
                                  (tmap 5 (vectors j))).
Proof.
  exact (KC.kernel_free_basis 5 12 point 2 back functionals vectors
           vectors_annihilated splitting_on_basis inverse).
Qed.

End E1E18Kernel.

(** The statement has a model in which 2 is invertible: Zmod 7, where 2 4 = 1. *)
Module Mod7 := E1E18Kernel CdTowerCanonicalKernels.Zmod7.

Definition kernel_mod7 :=
  Mod7.kernel_free_basis (Zmod.of_Z 7 4) ltac:(vm_compute; reflexivity).
