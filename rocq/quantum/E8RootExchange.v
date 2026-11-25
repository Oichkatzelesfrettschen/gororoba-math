(** * Root exchange: the diagonal sign symmetries of the E8-bar Rees data.

    Convention. The variables, the polynomial type SPoly, the matrices Cm and Cp (C of the N- and N+ scripts),
    the evaluation evSP and the reflection checkEq are those of E8ConjugationMap.v: variable index 1 is i and
    the indices 2 .. 10 are s1 .. s9. For a list T of variable indices, the flip of T substitutes x -> -x for
    every variable in T (flipSP on polynomials, flipx on points); the flip of T with congruence D = diag(d)
    is a symmetry of a matrix C when C at the flipped point is D C D, that is entry (a, b) is multiplied by
    d a * d b. The generator lists jm and jp are those of E8ConjugationIdeal.v, and signed e g multiplies the
    k-th element of g by plus or minus one according to e.

    Main results.
    - symm_Cm_T1, symm_Cm_T2, symm_Cm_T3: the flips of {s1, s3, s6, s9}, of {i, s2, s3, s4, s6, s7, s8} and
      of their symmetric difference are symmetries of C of the N- script, with the diagonals D1, D2 and
      D1 D2; symm_Cp_T1, symm_Cp_T2, symm_Cp_T3 are the same for the N+ script with the roles of s4 and s5
      exchanged. Each is an entrywise identity of integer polynomials with i free, decided by vm_compute as an equality of coefficient lists.
    - jm_flip_s4, jm_flip_s3s5s6, jm_flip_s1s5s9, jm_flip_i_s2_s5_s7_s8, jm_flip_T2: every generator of
      J_N- is multiplied by plus or minus one under each of the flips of {s4}, {s3, s5, s6}, {s1, s5, s9},
      {i, s2, s5, s7, s8} and of the flip of T2, in every commutative ring.
    - RootExchange.root_exchange_C, root_exchange_detB, root_exchange_ideal: in a ring with i^2 = -1, the
      flip of T2 changes the root i = r of -1 to -r, and carries the N- matrix C, the determinant of its
      pivot block and the ideal J_N- at root r onto the same data at root -r.

    Scope. The flips act on the N- data of one cell at a time over a ring with i a free variable. Over a
    prime field the flip of T2 sends the data at the root r to the data at -r with the same sign, so it is no
    symmetry of one cell. *)

From Stdlib Require Import ZArith List Ring Ring_theory InitialRing PeanoNat Lia Bool.
Require Import CdTowerRing StiefelA5Certificate StiefelA5Pfaffian E8ConjugationMap E8ConjugationIdeal.
Import ListNotations.

Definition inT (T : list nat) (v : nat) : bool := existsb (Nat.eqb v) T.

Fixpoint flipSign (T : list nat) (vs : list nat) : Z :=
  match vs with [] => 1%Z | v :: r => Z.mul (if inT T v then (-1)%Z else 1%Z) (flipSign T r) end.

Fixpoint flipSP (T : list nat) (s : SPoly) : SPoly :=
  match s with
  | [] => []
  | (c, vs) :: r => (Z.mul c (flipSign T vs), vs) :: flipSP T r
  end.

Definition T1 : list nat := [2; 4; 7; 10].
Definition T2 : list nat := [1; 3; 4; 5; 7; 8; 9].
Definition T3 : list nat := [1; 2; 3; 5; 8; 9; 10].
Definition T2p : list nat := [1; 3; 4; 6; 7; 8; 9].
Definition T3p : list nat := [1; 2; 3; 6; 8; 9; 10].

Definition d1L : list Z := [1%Z; 1%Z; 1%Z; (-1)%Z; (-1)%Z; (-1)%Z; (-1)%Z; 1%Z; 1%Z; 1%Z; 1%Z; (-1)%Z; (-1)%Z; (-1)%Z; (-1)%Z].
Definition d2L : list Z := [1%Z; 1%Z; (-1)%Z; (-1)%Z; 1%Z; 1%Z; (-1)%Z; 1%Z; (-1)%Z; (-1)%Z; 1%Z; 1%Z; (-1)%Z; (-1)%Z; 1%Z].
Definition d3L : list Z := [1%Z; 1%Z; (-1)%Z; 1%Z; (-1)%Z; (-1)%Z; 1%Z; 1%Z; (-1)%Z; (-1)%Z; 1%Z; (-1)%Z; 1%Z; 1%Z; (-1)%Z].
Definition dsel (L : list Z) (a : nat) : Z := nth a L 1%Z.

Definition spoly_eq_dec (x y : SPoly) : {x = y} + {x <> y}.
Proof.
  apply list_eq_dec. intros [c u] [d v].
  destruct (Z.eq_dec c d) as [-> | Hc]; [| right; congruence].
  destruct (list_eq_dec Nat.eq_dec u v) as [-> | Hu]; [left; reflexivity | right; congruence].
Defined.

(** The congruence is checked as an equality of coefficient lists: the flip changes signs only, so the
    entry at the flipped point is the entry scaled by d a * d b as a polynomial, before any evaluation. *)
Definition symCheck (T : list nat) (L : list Z) (C : nat -> nat -> SPoly) : bool :=
  allpairs (fun a b =>
    if spoly_eq_dec (flipSP T (C a b)) (scaleSP (Z.mul (dsel L a) (dsel L b)) (C a b)) then true else false).

Lemma symm_Cm_T1_ok : symCheck T1 d1L Cm = true. Proof. vm_compute. reflexivity. Qed.
Lemma symm_Cm_T2_ok : symCheck T2 d2L Cm = true. Proof. vm_compute. reflexivity. Qed.
Lemma symm_Cm_T3_ok : symCheck T3 d3L Cm = true. Proof. vm_compute. reflexivity. Qed.
Lemma symm_Cp_T1_ok : symCheck T1 d1L Cp = true. Proof. vm_compute. reflexivity. Qed.
Lemma symm_Cp_T2_ok : symCheck T2p d2L Cp = true. Proof. vm_compute. reflexivity. Qed.
Lemma symm_Cp_T3_ok : symCheck T3p d3L Cp = true. Proof. vm_compute. reflexivity. Qed.

(** Homogeneity of the generators of J_N- under the flips, in every commutative ring. *)
Section JHomogeneity.
Variable R : Type.
Variables (rO rI : R) (radd rmul rsub : R -> R -> R) (ropp : R -> R).
Hypothesis Rth : ring_theory rO rI radd rmul rsub ropp (@eq R).
Add Ring jhom_ring : Rth.

(** The flip of s4 multiplies every generator of J_N- by +1. *)
Theorem jm_flip_s4 : forall i s1 s2 s3 s4 s5 s6 s7 s8 s9,
  jm R rO rI radd rmul ropp i s1 s2 s3 (ropp s4) s5 s6 s7 s8 s9
  = signed R ropp [ true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true; true ] (jm R rO rI radd rmul ropp i s1 s2 s3 s4 s5 s6 s7 s8 s9).
Proof.
  intros. unfold jm. cbn [signed sgn].
  repeat (apply (cons_eq R); [ring |]). reflexivity.
Qed.

(** The flip of s3, s5, s6 multiplies the generators of J_N- by the signs of its character. *)
Theorem jm_flip_s3s5s6 : forall i s1 s2 s3 s4 s5 s6 s7 s8 s9,
  jm R rO rI radd rmul ropp i s1 s2 (ropp s3) s4 (ropp s5) (ropp s6) s7 s8 s9
  = signed R ropp [ true; true; true; true; false; true; false; false; true; false; true; true; false; true; true; false; true; true; false; true; false; true; false; true; true; false; true ] (jm R rO rI radd rmul ropp i s1 s2 s3 s4 s5 s6 s7 s8 s9).
Proof.
  intros. unfold jm. cbn [signed sgn].
  repeat (apply (cons_eq R); [ring |]). reflexivity.
Qed.

(** The flip of s1, s5, s9 multiplies the generators of J_N- by the signs of its character. *)
Theorem jm_flip_s1s5s9 : forall i s1 s2 s3 s4 s5 s6 s7 s8 s9,
  jm R rO rI radd rmul ropp i (ropp s1) s2 s3 s4 (ropp s5) s6 s7 s8 (ropp s9)
  = signed R ropp [ true; true; true; false; true; false; true; true; false; true; false; true; false; true; true; false; true; false; true; false; true; true; false; true; true; false; true ] (jm R rO rI radd rmul ropp i s1 s2 s3 s4 s5 s6 s7 s8 s9).
Proof.
  intros. unfold jm. cbn [signed sgn].
  repeat (apply (cons_eq R); [ring |]). reflexivity.
Qed.

(** The flip of i, s2, s5, s7, s8 multiplies the generators of J_N- by the signs of its character. *)
Theorem jm_flip_i_s2_s5_s7_s8 : forall i s1 s2 s3 s4 s5 s6 s7 s8 s9,
  jm R rO rI radd rmul ropp (ropp i) s1 (ropp s2) s3 s4 (ropp s5) s6 (ropp s7) (ropp s8) s9
  = signed R ropp [ true; true; true; false; true; false; true; true; false; true; false; true; false; true; true; false; true; false; true; false; true; true; false; true; true; false; true ] (jm R rO rI radd rmul ropp i s1 s2 s3 s4 s5 s6 s7 s8 s9).
Proof.
  intros. unfold jm. cbn [signed sgn].
  repeat (apply (cons_eq R); [ring |]). reflexivity.
Qed.

(** The flip of T2 = {i, s2, s3, s4, s6, s7, s8} multiplies the generators of J_N- by the signs of its character. *)
Theorem jm_flip_T2 : forall i s1 s2 s3 s4 s5 s6 s7 s8 s9,
  jm R rO rI radd rmul ropp (ropp i) s1 (ropp s2) (ropp s3) (ropp s4) s5 (ropp s6) (ropp s7) (ropp s8) s9
  = signed R ropp [ true; true; true; false; false; false; false; false; false; false; false; true; true; true; true; true; true; false; false; false; false; true; true; true; true; true; true ] (jm R rO rI radd rmul ropp i s1 s2 s3 s4 s5 s6 s7 s8 s9).
Proof.
  intros. unfold jm. cbn [signed sgn].
  repeat (apply (cons_eq R); [ring |]). reflexivity.
Qed.

End JHomogeneity.

Module RootExchange (D : CommutativeRingWithI).
Module CM := ConjugationMap D.
Add Ring rx_ring : D.ring_th.

Definition flipx (T : list nat) (xv : nat -> D.t) (j : nat) : D.t :=
  if inT T j then D.opp (xv j) else xv j.

Lemma evMono_flip T xv vs :
  CM.evMono (flipx T xv) vs = D.mul (CM.SPf.phiZ (flipSign T vs)) (CM.evMono xv vs).
Proof.
  induction vs as [|v r IH]; cbn [CM.evMono flipSign].
  - rewrite CM.SPf.phiZ_one. ring.
  - rewrite IH. unfold flipx. destruct (inT T v); rewrite CM.phiZ_mul;
      [rewrite CM.SPf.phiZ_mone | rewrite CM.SPf.phiZ_one]; ring.
Qed.

Theorem evSP_flip T xv s : CM.evSP xv (flipSP T s) = CM.evSP (flipx T xv) s.
Proof.
  induction s as [|[c vs] r IH]; cbn [flipSP CM.evSP]; [reflexivity|].
  rewrite IH, evMono_flip, CM.phiZ_mul. ring.
Qed.

Lemma symm_of_check T L C : symCheck T L C = true ->
  forall xv a b, (a < 15)%nat -> (b < 15)%nat ->
  CM.evSP (flipx T xv) (C a b)
  = D.mul (CM.SPf.phiZ (Z.mul (dsel L a) (dsel L b))) (CM.evSP xv (C a b)).
Proof.
  intros H xv a b Ha Hb.
  pose proof (allpairs_sound _ H a b Ha Hb) as E0. cbv beta in E0.
  destruct (spoly_eq_dec (flipSP T (C a b)) (scaleSP (Z.mul (dsel L a) (dsel L b)) (C a b))) as [E | N];
    [| discriminate E0].
  rewrite <- evSP_flip, E, CM.evSP_scale. reflexivity.
Qed.

Definition symm_Cm_T1 := symm_of_check T1 d1L Cm symm_Cm_T1_ok.
Definition symm_Cm_T2 := symm_of_check T2 d2L Cm symm_Cm_T2_ok.
Definition symm_Cm_T3 := symm_of_check T3 d3L Cm symm_Cm_T3_ok.
Definition symm_Cp_T1 := symm_of_check T1 d1L Cp symm_Cp_T1_ok.
Definition symm_Cp_T2 := symm_of_check T2p d2L Cp symm_Cp_T2_ok.
Definition symm_Cp_T3 := symm_of_check T3p d3L Cp symm_Cp_T3_ok.

(** The flip of T2 changes i to -i, so it exchanges the root r of -1 with -r. *)
Theorem root_exchange_root xv : flipx T2 xv 1 = D.opp (xv 1).
Proof. reflexivity. Qed.

Theorem root_exchange_root_sq xv :
  D.mul (xv 1) (xv 1) = D.opp D.one -> D.mul (flipx T2 xv 1) (flipx T2 xv 1) = D.opp D.one.
Proof. intros H. rewrite root_exchange_root. rewrite <- H. ring. Qed.

(** The matrix C of the N- script at root -r is D2 C D2 of the one at root r. *)
Theorem root_exchange_C xv a b : (a < 15)%nat -> (b < 15)%nat ->
  CM.evSP (flipx T2 xv) (Cm a b)
  = D.mul (CM.SPf.phiZ (Z.mul (dsel d2L a) (dsel d2L b))) (CM.evSP xv (Cm a b)).
Proof. exact (symm_Cm_T2 xv a b). Qed.

(** The determinant of the pivot block of the N- script is the same at root r and at root -r. *)
Theorem root_exchange_detB xv : D.mul (xv 1) (xv 1) = D.opp D.one ->
  CM.detBD Cm Fm (flipx T2 xv) = CM.detBD Cm Fm xv.
Proof.
  intros Hi. rewrite (CM.detB_Nm xv Hi), (CM.detB_Nm (flipx T2 xv) (root_exchange_root_sq xv Hi)).
  unfold CM.closedForm, CM.sqm1. cbv [flipx T2 inT existsb Nat.eqb orb].
  ring.
Qed.

(** The ideal J_N- generated at root -r equals the one generated at root r. *)
Theorem root_exchange_ideal xv x :
  gen_ideal D.t D.zero D.add D.mul
    (jm D.t D.zero D.one D.add D.mul D.opp (flipx T2 xv 1) (flipx T2 xv 2) (flipx T2 xv 3) (flipx T2 xv 4)
       (flipx T2 xv 5) (flipx T2 xv 6) (flipx T2 xv 7) (flipx T2 xv 8) (flipx T2 xv 9) (flipx T2 xv 10)) x
  <-> gen_ideal D.t D.zero D.add D.mul
    (jm D.t D.zero D.one D.add D.mul D.opp (xv 1) (xv 2) (xv 3) (xv 4) (xv 5) (xv 6) (xv 7) (xv 8) (xv 9)
       (xv 10)) x.
Proof.
  cbv [flipx T2 inT existsb Nat.eqb orb].
  rewrite (jm_flip_T2 D.t D.zero D.one D.add D.mul D.sub D.opp D.ring_th).
  exact (gen_ideal_signed D.t D.zero D.one D.add D.mul D.sub D.opp D.ring_th _ _ x).
Qed.

End RootExchange.

Module GaussianRootExchange := RootExchange GaussianIntegers.

Print Assumptions jm_flip_T2.
Print Assumptions symm_Cm_T2_ok.
Print Assumptions symm_Cp_T3_ok.
Print Assumptions GaussianRootExchange.root_exchange_detB.
Print Assumptions GaussianRootExchange.root_exchange_ideal.
