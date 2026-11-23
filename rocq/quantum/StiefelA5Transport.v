(** The transport of left multiplication by a doubly pure A_5 element onto the bordered matrices A(z, w).

    Convention: the tower of CdTowerRing.v, (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)), over a
    commutative ring with an element i, i i = -1. For x = (r, s) in A_5 put
    phi(x)_c = r_c + i conj(s)_c and psi(x)_c = r_c - i conj(s)_c (c < 16). For y = (p, q) with p, q pure in
    A_4 (coordinates a_k, b_k for k = 1..15) put z_k = a_k + i b_k and w_k = a_k - i b_k. Then
    phi(y x) = A(z, w) psi(x) and psi(y x) = A(w, z) phi(x), with A the matrix of StiefelA5Certificate.v
    evaluated at z and t = w (resp. w and t = z). This is the transport of
    docs/evidence/a5-stiefel-pfaffian-germs/README.md (item 2) of gororoba-quantum in a form linear over
    the coefficient ring. *)

From Stdlib Require Import ZArith List Ring Ring_polynom Ring_theory InitialRing PeanoNat Lia.
Require Import CdTowerRing Pfaffian StiefelA5Certificate StiefelA5Pfaffian.
Import ListNotations.

Module StiefelTransport (D : CommutativeRingWithI).
Module T := RingTower D.
Module SP := StiefelPfaffian D.
Add Ring st_ring : D.ring_th.

Fixpoint mk (k : nat) (f : nat -> D.t) : T.cd k :=
  match k as d return T.cd d with
  | O => f O
  | S j => (mk j f, mk j (fun i => f (i + Nat.pow 2 j)%nat))
  end.

Lemma coord_mk k : forall f i, i < Nat.pow 2 k -> T.coord k (mk k f) i = f i.
Proof.
  induction k as [|k IH]; intros f i Hi; simpl in *.
  - f_equal. lia.
  - destruct (Nat.ltb i (Nat.pow 2 k)) eqn:E.
    + apply Nat.ltb_lt in E. apply IH. exact E.
    + apply Nat.ltb_ge in E. rewrite IH by lia. f_equal. lia.
Qed.

Section Transport.
Variables a b R S : nat -> D.t.

Definition pureA (f : nat -> D.t) : nat -> D.t := fun j => if Nat.eqb j 0 then D.zero else f j.
Definition y5 : T.cd 5 := (mk 4 (pureA a), mk 4 (pureA b)).
Definition x5 : T.cd 5 := (mk 4 R, mk 4 S).

Definition zc (k : nat) : D.t := D.add (a k) (D.mul D.i (b k)).
Definition wc (k : nat) : D.t := D.sub (a k) (D.mul D.i (b k)).
Definition envzw : list D.t := map zc (seq 1 15) ++ map wc (seq 1 15).
Definition envwz : list D.t := map wc (seq 1 15) ++ map zc (seq 1 15).

Definition phi (u : T.cd 5) (c : nat) : D.t :=
  D.add (T.coord 4 (fst u) c) (D.mul D.i (T.coord 4 (T.conjugate 4 (snd u)) c)).
Definition psi (u : T.cd 5) (c : nat) : D.t :=
  D.sub (T.coord 4 (fst u) c) (D.mul D.i (T.coord 4 (T.conjugate 4 (snd u)) c)).

(** sgn_tab c e is sgn16 c e (sgn_tab_ok); the literal table keeps the reductions below small. *)
Definition sgn_tab : list (list Z) :=
  [[1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1; -1];
   [1; 1; -1; 1; -1; 1; 1; -1; -1; 1; 1; -1; 1; -1; -1; 1];
   [1; 1; 1; -1; -1; -1; 1; 1; -1; -1; 1; 1; 1; 1; -1; -1];
   [1; -1; 1; 1; -1; 1; -1; 1; -1; 1; -1; 1; 1; -1; 1; -1];
   [1; 1; 1; 1; 1; -1; -1; -1; -1; -1; -1; -1; 1; 1; 1; 1];
   [1; -1; 1; -1; 1; 1; 1; -1; -1; 1; -1; 1; -1; 1; -1; 1];
   [1; -1; -1; 1; 1; -1; 1; 1; -1; 1; 1; -1; -1; 1; 1; -1];
   [1; 1; -1; -1; 1; 1; -1; 1; -1; -1; 1; 1; -1; -1; 1; 1];
   [1; 1; 1; 1; 1; 1; 1; 1; 1; -1; -1; -1; -1; -1; -1; -1];
   [1; -1; 1; -1; 1; -1; -1; 1; 1; 1; 1; -1; 1; -1; -1; 1];
   [1; -1; -1; 1; 1; 1; -1; -1; 1; -1; 1; 1; 1; 1; -1; -1];
   [1; 1; -1; -1; 1; -1; 1; -1; 1; 1; -1; 1; 1; -1; 1; -1];
   [1; -1; -1; -1; -1; 1; 1; 1; 1; -1; -1; -1; 1; 1; 1; 1];
   [1; 1; -1; 1; -1; -1; -1; 1; 1; 1; -1; 1; -1; 1; -1; 1];
   [1; 1; 1; -1; -1; 1; -1; -1; 1; 1; 1; -1; -1; 1; 1; -1];
   [1; -1; 1; 1; -1; -1; 1; -1; 1; -1; 1; 1; -1; -1; 1; 1]]%Z.

Lemma sgn_tab_ok :
  forallb (fun c => forallb (fun e => Z.eqb (nth e (nth c sgn_tab []) 0%Z) (sgn16 c e)) (seq 0 16)) (seq 0 16) = true.
Proof. vm_compute. reflexivity. Qed.

Definition zsign (c e : nat) : D.t := SP.phiZ (nth e (nth c sgn_tab []) 0%Z).

(** The entries of A(zf, tf), as StiefelA5Certificate.Amat states them. *)
Definition Aent (zf tf : nat -> D.t) (c e : nat) : D.t :=
  if Nat.eqb c e then D.zero
  else if Nat.eqb c 0 then D.opp (tf e)
  else if Nat.eqb e 0 then tf c
  else D.mul (zsign c e) (zf (Nat.lxor c e)).

Ltac transport_close :=
  cbv [phi psi y5 x5 mk pureA T.mul T.add T.scale T.conjugate T.coord T.neg_one fst snd Nat.pow Nat.mul Nat.add
       Nat.ltb Nat.leb Nat.sub Nat.eqb SP.P.sumk];
  cbv [Aent zsign sgn_tab nth Nat.eqb Nat.lxor Nat.bitwise Nat.max Nat.div2 Nat.odd Nat.even xorb negb Nat.mul Nat.add
       SP.phiZ gen_phiZ gen_phiPOS gen_phiPOS1 zc wc];
  ring [D.i_squared].

Lemma transport_phi c : c < 16 ->
  phi (T.mul 5 y5 x5) c = SP.P.sumk 16 (fun e => D.mul (Aent zc wc c e) (psi x5 e)).
Proof.
  intros Hc.
  do 16 (destruct c as [|c]; [transport_close|]). lia.
Qed.

Lemma transport_psi c : c < 16 ->
  psi (T.mul 5 y5 x5) c = SP.P.sumk 16 (fun e => D.mul (Aent wc zc c e) (phi x5 e)).
Proof.
  intros Hc.
  do 16 (destruct c as [|c]; [transport_close|]). lia.
Qed.

End Transport.
End StiefelTransport.
