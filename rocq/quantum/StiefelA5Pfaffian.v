(** Evaluation of the Pfaffian certificate in any commutative ring.

    ev env p evaluates a polynomial of StiefelA5Certificate.v at the variable values env (variable j is the
    j-th entry of env, counted from 1), through the Z-morphism gen_phiZ. pf_A_eval states that the Pfaffian of
    PfaffianTheory, applied to the evaluated matrix Amat over the indices 0..15, equals the evaluated
    -(z.t) Q G: the memo table's local checks lift to every stored entry by induction on length. *)

From Stdlib Require Import ZArith List Ring Ring_polynom Ring_theory InitialRing PeanoNat Lia FMapPositive Wf_nat.
Require Import CdTowerRing Pfaffian StiefelA5Certificate.
Import ListNotations.

Module StiefelPfaffian (D : CommutativeRing).
Module P := PfaffianTheory D.
Add Ring sp_ring : D.ring_th.

Definition phiZ : Z -> D.t := gen_phiZ D.zero D.one D.add D.mul D.opp.
Definition Rsth := Eqsth D.t.
Definition Reqe := Eq_ext D.add D.mul D.opp.
Definition ARth := Rth_ARth Rsth Reqe D.ring_th.
Definition morph := gen_phiZ_morph Rsth Reqe D.ring_th.

Definition ev (env : list D.t) (p : ZP) : D.t := Pphi D.zero D.add D.mul phiZ env p.

Lemma ev_add env p q : ev env (padd p q) = D.add (ev env p) (ev env q).
Proof. exact (Padd_ok Rsth Reqe ARth morph q p env). Qed.

Lemma ev_mul env p q : ev env (pmul p q) = D.mul (ev env p) (ev env q).
Proof. exact (Pmul_ok Rsth Reqe ARth morph p q env). Qed.

Lemma ev_opp env p : ev env (popp p) = D.opp (ev env p).
Proof. exact (Popp_ok Rsth Reqe ARth morph p env). Qed.

Lemma ev_pc env c : ev env (pc c) = phiZ c.
Proof. reflexivity. Qed.

Lemma ev_peq env p q : peq p q = true -> ev env p = ev env q.
Proof. intros H. exact (Peq_ok Rsth Reqe morph p q H env). Qed.

Lemma phiZ_one : phiZ 1%Z = D.one.
Proof. reflexivity. Qed.

Lemma phiZ_mone : phiZ (-1)%Z = D.opp D.one.
Proof. reflexivity. Qed.

Lemma ev_sgnP env k : ev env (sgnP k) = P.sgn k.
Proof. unfold sgnP, P.sgn. destruct (Nat.even k); reflexivity. Qed.

Lemma ev_sumP env n f : ev env (sumP n f) = P.sumk n (fun k => ev env (f k)).
Proof.
  induction n as [|n IH]; simpl; [reflexivity|].
  rewrite ev_add, IH. reflexivity.
Qed.

Section Table.
Variable tbl : PM.t (list nat * ZP).
Hypothesis Htbl : check_table tbl = true.
Variable env : list D.t.

Definition evM (a b : nat) : D.t := ev env (Amat a b).

Lemma entries_ok l p : lookup tbl l = Some p -> entry_ok tbl l p = true.
Proof.
  unfold lookup. destruct (PM.find (keyl l) tbl) as [[l' p']|] eqn:E; [|discriminate].
  destruct (list_eq_dec Nat.eq_dec l l') as [<-|]; [|discriminate]. intros Hp. injection Hp as <-.
  assert (H2 := Htbl). unfold check_table in H2. apply andb_prop in H2. destruct H2 as [Hall _].
  rewrite forallb_forall in Hall.
  exact (Hall (keyl l, (l, p')) (PM.elements_correct tbl (keyl l) E)).
Qed.

Lemma children_ev x r k s (F : nat -> D.t) :
  children tbl x r k = Some s ->
  (forall j q, j < k -> lookup tbl (rem_at j r) = Some q -> ev env q = F j) ->
  ev env s = P.sumk k (fun j => D.mul (D.mul (P.sgn j) (evM x (nth j r O))) (F j)).
Proof.
  revert s. induction k as [|k IH]; intros s Hc HF.
  - simpl in Hc. injection Hc as <-. reflexivity.
  - simpl in Hc. destruct (children tbl x r k) as [acc|] eqn:Ea; [|discriminate].
    destruct (lookup tbl (rem_at k r)) as [q|] eqn:Eq; [|discriminate].
    injection Hc as <-. simpl. rewrite ev_add, !ev_mul, ev_sgnP.
    rewrite (IH acc eq_refl) by (intros; apply HF; [lia|assumption]).
    rewrite (HF k q) by (try lia; exact Eq). unfold evM. reflexivity.
Qed.

Lemma stored_ok : forall n l p, length l = n -> lookup tbl l = Some p -> ev env p = P.pf evM l.
Proof.
  intros n. induction n as [n IH] using (well_founded_induction lt_wf).
  intros l p Hlen Hl. assert (Ho := entries_ok l p Hl).
  destruct l as [|x r].
  - simpl in Ho. rewrite (ev_peq env p (pc 1) Ho). reflexivity.
  - simpl in Ho. destruct (children tbl x r (length r)) as [s|] eqn:Ec; [|discriminate].
    rewrite (ev_peq env p s Ho). rewrite P.pf_cons.
    apply (children_ev x r (length r) s (fun j => P.pf evM (rem_at j r)) Ec).
    intros j q Hj Hq. apply (IH (length (rem_at j r))); [|reflexivity|exact Hq].
    simpl in Hlen. rewrite P.length_rem_at by exact Hj. lia.
Qed.

Theorem pf_A_eval : P.pf evM idx = ev env rhs.
Proof.
  assert (H2 := Htbl). unfold check_table in H2. apply andb_prop in H2. destruct H2 as [_ Hroot].
  destruct (lookup tbl idx) as [p|] eqn:E; [|discriminate].
  rewrite <- (stored_ok (length idx) idx p eq_refl E). apply ev_peq. exact Hroot.
Qed.

End Table.

Lemma ev_rhs env : ev env rhs = D.opp (D.mul (ev env ztP) (D.mul (ev env QP) (ev env GP))).
Proof. unfold rhs. rewrite ev_opp, !ev_mul. reflexivity. Qed.

Lemma ev_QP env : ev env QP = P.sumk 15 (fun m => D.mul (ev env (zv (1 + m))) (ev env (zv (1 + m)))).
Proof. unfold QP, dotP. rewrite ev_sumP. apply P.sumk_ext. intros m Hm. rewrite ev_mul. reflexivity. Qed.

End StiefelPfaffian.
