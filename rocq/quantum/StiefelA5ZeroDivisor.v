(** Every A_5 Stiefel element is a zero divisor (Moreno, math/0512517, Section 5, Question 1, at n + 1 = 5).

    Statement: over a field K of characteristic other than 2 that contains i with i i = -1, let
    y = (p, q) in A_5 (the tower of CdTowerRing.v) with p, q pure in A_4, coordinates a_k and b_k
    (k = 1..15), and a.a = b.b, a.b = 0 (bilinear sums). Then some nonzero x has y x = 0.

    Proof: z = a + i b satisfies Q(z) = z.z = a.a - b.b + 2 i a.b = 0, so the certified identity
    Pf A(z, w) = -(z.w) Q(z) G(z) (StiefelA5Certificate.v, StiefelA5Pfaffian.v) gives Pf A(z, w) = 0, and
    PfaffianKernel gives a nonzero v with A(z, w) v = 0. x = (v / 2, conj(i v / 2)) has psi(x) = v and
    phi(x) = 0, so the transport (StiefelA5Transport.v) gives phi(y x) = A(z, w) v = 0 and
    psi(y x) = A(w, z) phi(x) = 0, hence y x = 0. The real case is the instance K = C. *)

From Stdlib Require Import ZArith List Ring Field Ring_polynom Ring_theory InitialRing PeanoNat Lia.
Require Import CdTowerRing Pfaffian StiefelA5Certificate StiefelA5Pfaffian StiefelA5Transport.
Import ListNotations.

Module Type PfFieldI.
  Include PfField.
  Parameter i : t.
  Axiom i_squared : mul i i = opp one.
End PfFieldI.

Module StiefelZeroDivisor (K : PfFieldI).
Module ST := StiefelTransport K.
Module PK := PfaffianKernel K.
Module T := ST.T.
Add Field szd_field : K.field_th.

Lemma Amat_skew_check :
  forallb (fun c => forallb (fun e => peq (Amat c e) (popp (Amat e c))) (seq 0 16)) (seq 0 16) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma evM_skew env c e : c < 16 -> e < 16 -> ST.SP.evM env c e = K.opp (ST.SP.evM env e c).
Proof.
  intros Hc He. unfold ST.SP.evM. rewrite <- ST.SP.ev_opp. apply ST.SP.ev_peq.
  assert (H := Amat_skew_check). rewrite forallb_forall in H.
  specialize (H c ltac:(apply in_seq; lia)). rewrite forallb_forall in H.
  apply H. apply in_seq. lia.
Qed.

Lemma pf_same M l : PK.P.pf M l = ST.SP.P.pf M l.
Proof. reflexivity. Qed.

Lemma sumk_same n f : PK.P.sumk n f = ST.SP.P.sumk n f.
Proof. reflexivity. Qed.

Definition Mr (env : list K.t) (c e : nat) : K.t :=
  if andb (Nat.ltb c 16) (Nat.ltb e 16) then ST.SP.evM env c e else K.zero.

Lemma Mr_skew env : PK.P.skew (Mr env).
Proof.
  intros c e. unfold Mr. destruct (Nat.ltb c 16) eqn:Ec; destruct (Nat.ltb e 16) eqn:Ee; simpl;
    try (field_simplify; reflexivity).
  apply Nat.ltb_lt in Ec, Ee. apply evM_skew; assumption.
Qed.

Lemma lsum_seq_from s n f : PK.lsum (seq s n) f = PK.P.sumk n (fun k => f (s + k)%nat).
Proof.
  revert s. induction n as [|n IH]; intros s; [reflexivity|].
  cbn [seq]. unfold PK.lsum. cbn [fold_right]. fold (PK.lsum (seq (S s) n) f).
  rewrite IH, PK.P.sumk_first. rewrite Nat.add_0_r.
  rewrite (PK.P.sumk_ext n (fun k => f (S s + k)%nat) (fun k => f (s + S k)%nat)) by (intros; f_equal; lia).
  reflexivity.
Qed.

Lemma lsum_seq n f : PK.lsum (seq 0 n) f = PK.P.sumk n f.
Proof. rewrite lsum_seq_from. reflexivity. Qed.

Lemma coord_scale k : forall r (u : T.cd k) c, T.coord k (T.scale k r u) c = K.mul r (T.coord k u c).
Proof.
  induction k as [|k IH]; intros r u c; simpl; [reflexivity|].
  destruct (Nat.ltb c (Nat.pow 2 k)); apply IH.
Qed.

Lemma coord_conj k : forall (u : T.cd k) c, c < Nat.pow 2 k ->
  T.coord k (T.conjugate k u) c = if Nat.eqb c 0 then T.coord k u c else K.opp (T.coord k u c).
Proof.
  induction k as [|k IH]; intros u c Hc; simpl in *.
  - assert (c = 0) by lia. subst. reflexivity.
  - destruct (Nat.ltb c (Nat.pow 2 k)) eqn:E.
    + apply Nat.ltb_lt in E. apply IH. exact E.
    + apply Nat.ltb_ge in E. rewrite coord_scale. unfold T.neg_one.
      assert (Hc0 : Nat.eqb c 0 = false) by (apply Nat.eqb_neq; pose proof (Nat.pow_nonzero 2 k); lia).
      rewrite Hc0. ring.
Qed.

Lemma coord_zero k : forall c, T.coord k (T.zero k) c = K.zero.
Proof. induction k as [|k IH]; intros c; simpl; [reflexivity|]. destruct (Nat.ltb c (Nat.pow 2 k)); apply IH. Qed.

Lemma eq_zero_of_coords k : forall (u : T.cd k), (forall c, c < Nat.pow 2 k -> T.coord k u c = K.zero) -> u = T.zero k.
Proof.
  induction k as [|k IH]; intros u H; simpl in *.
  - exact (H 0 ltac:(lia)).
  - destruct u as [u1 u2]. f_equal.
    + apply IH. intros c Hc. specialize (H c ltac:(lia)). simpl in H.
      replace (Nat.ltb c (Nat.pow 2 k)) with true in H by (symmetry; apply Nat.ltb_lt; exact Hc). exact H.
    + apply IH. intros c Hc. specialize (H (c + Nat.pow 2 k) ltac:(lia)). simpl in H.
      replace (Nat.ltb (c + Nat.pow 2 k) (Nat.pow 2 k)) with false in H by (symmetry; apply Nat.ltb_ge; lia).
      replace (c + Nat.pow 2 k - Nat.pow 2 k) with c in H by lia. exact H.
Qed.

Lemma two_ne : K.add K.one K.one <> K.zero.
Proof. exact K.two_nonzero. Qed.

Lemma i_ne : K.i <> K.zero.
Proof.
  intros H. apply PK.one_nonzero. replace K.one with (K.opp (K.mul K.i K.i)) by (rewrite K.i_squared; ring).
  rewrite H. ring.
Qed.

Lemma lxor_check :
  forallb (fun c => forallb (fun e => orb (Nat.eqb c e) (andb (Nat.leb 1 (Nat.lxor c e)) (Nat.leb (Nat.lxor c e) 15)))
    (seq 0 16)) (seq 0 16) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lxor_range c e : c < 16 -> e < 16 -> c <> e -> 1 <= Nat.lxor c e <= 15.
Proof.
  intros Hc He Hne. assert (H := lxor_check). rewrite forallb_forall in H.
  specialize (H c ltac:(apply in_seq; lia)). rewrite forallb_forall in H.
  specialize (H e ltac:(apply in_seq; lia)).
  replace (Nat.eqb c e) with false in H by (symmetry; apply Nat.eqb_neq; exact Hne).
  cbn [orb] in H. apply andb_prop in H. destruct H as [H1 H2]. apply Nat.leb_le in H1, H2. lia.
Qed.

Lemma zsign_eq c e : c < 16 -> e < 16 -> ST.zsign c e = ST.SP.phiZ (sgn16 c e).
Proof.
  intros Hc He. unfold ST.zsign. f_equal. apply Z.eqb_eq.
  assert (H := ST.sgn_tab_ok). rewrite forallb_forall in H.
  specialize (H c ltac:(apply in_seq; lia)). rewrite forallb_forall in H.
  apply H. apply in_seq. lia.
Qed.

Section Link.
Variables zf tf : nat -> K.t.
Definition envft : list K.t := map zf (seq 1 15) ++ map tf (seq 1 15).

Lemma ev_pX j : ST.SP.ev envft (pX j) = BinList.nth K.zero j envft.
Proof. unfold pX, ST.SP.ev. symmetry. exact (mkX_ok ST.SP.Rsth ST.SP.Reqe ST.SP.ARth ST.SP.morph j envft). Qed.

Lemma nth_env_z j : 1 <= j <= 15 -> BinList.nth K.zero (Pos.of_nat j) envft = zf j.
Proof. intros H. do 16 (destruct j as [|j]; [try lia; reflexivity|]). lia. Qed.

Lemma nth_env_t j : 1 <= j <= 15 -> BinList.nth K.zero (Pos.of_nat (15 + j)) envft = tf j.
Proof. intros H. do 16 (destruct j as [|j]; [try lia; reflexivity|]). lia. Qed.

Lemma evM_Aent c e : c < 16 -> e < 16 -> ST.SP.evM envft c e = ST.Aent zf tf c e.
Proof.
  intros Hc He. unfold ST.SP.evM, Amat, ST.Aent.
  destruct (Nat.eqb c e) eqn:Ece; [reflexivity|]. apply Nat.eqb_neq in Ece.
  destruct (Nat.eqb c 0) eqn:Ec0.
  - apply Nat.eqb_eq in Ec0. subst c. rewrite ST.SP.ev_opp, ev_pX, nth_env_t by lia. reflexivity.
  - destruct (Nat.eqb e 0) eqn:Ee0.
    + apply Nat.eqb_eq in Ee0. subst e. rewrite ev_pX, nth_env_t by (apply Nat.eqb_neq in Ec0; lia). reflexivity.
    + rewrite ST.SP.ev_mul, ST.SP.ev_pc, ev_pX, nth_env_z by (apply lxor_range; assumption).
      rewrite zsign_eq by assumption. reflexivity.
Qed.
End Link.

Section Stiefel.
Variables a b : nat -> K.t.
Hypothesis Hnorm : PK.P.sumk 15 (fun m => K.mul (a (S m)) (a (S m))) = PK.P.sumk 15 (fun m => K.mul (b (S m)) (b (S m))).
Hypothesis Horth : PK.P.sumk 15 (fun m => K.mul (a (S m)) (b (S m))) = K.zero.

Definition env := ST.envzw a b.

Lemma ev_zv m : m < 15 -> ST.SP.ev env (zv (S m)) = ST.zc a b (S m).
Proof.
  intros Hm. unfold zv, env, ST.envzw.
  change (map (ST.zc a b) (seq 1 15) ++ map (ST.wc a b) (seq 1 15)) with (envft (ST.zc a b) (ST.wc a b)).
  rewrite ev_pX, nth_env_z by lia. reflexivity.
Qed.

Lemma Q_zero : ST.SP.ev env QP = K.zero.
Proof.
  rewrite ST.SP.ev_QP.
  rewrite (ST.SP.P.sumk_ext 15 _ (fun m => K.add (K.mul (a (S m)) (a (S m)))
              (K.add (K.opp (K.mul (b (S m)) (b (S m)))) (K.mul (K.add K.i K.i) (K.mul (a (S m)) (b (S m))))))).
  - rewrite !ST.SP.P.sumk_add, ST.SP.P.sumk_opp, ST.SP.P.sumk_scale.
    rewrite <- (sumk_same 15 (fun k => K.mul (b (S k)) (b (S k)))).
    rewrite <- (sumk_same 15 (fun k => K.mul (a (S k)) (b (S k)))).
    rewrite <- (sumk_same 15 (fun k => K.mul (a (S k)) (a (S k)))).
    rewrite Hnorm, Horth. ring.
  - intros m Hm. change (1 + m)%nat with (S m). rewrite (ev_zv m Hm). unfold ST.zc.
    ring [K.i_squared].
Qed.

Lemma pf_zero : PK.P.pf (Mr env) idx = K.zero.
Proof.
  rewrite (PK.P.pf_ext (Mr env) (ST.SP.evM env) idx).
  - rewrite pf_same, (ST.SP.pf_A_eval table certificate_ok env). rewrite ST.SP.ev_rhs, Q_zero. ring.
  - intros c e Hc He. unfold Mr. apply in_seq in Hc, He.
    replace (Nat.ltb c 16) with true by (symmetry; apply Nat.ltb_lt; lia).
    replace (Nat.ltb e 16) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity.
Qed.

Theorem stiefel_zero_divisor : exists x : T.cd 5, x <> T.zero 5 /\ T.mul 5 (ST.y5 a b) x = T.zero 5.
Proof.
  destruct (PK.pf_zero_kernel 16 idx (Mr env) eq_refl eq_refl (Mr_skew env) (seq_NoDup 16 0) pf_zero)
    as [v [[c0 [Hc0 Hv0]] Hker]].
  set (h := K.inv (K.add K.one K.one)).
  assert (Hh : K.mul (K.add K.one K.one) h = K.one) by (unfold h; field; exact two_ne).
  set (R := fun c => K.mul (v c) h).
  set (S := fun c => if Nat.eqb c 0 then K.mul K.i (K.mul (v c) h) else K.opp (K.mul K.i (K.mul (v c) h))).
  exists (ST.x5 R S).
  assert (Hpsi : forall e, e < 16 -> ST.psi (ST.x5 R S) e = v e).
  { intros e He. unfold ST.psi, ST.x5. cbn [fst snd].
    rewrite ST.coord_mk by (simpl; lia). rewrite coord_conj by (simpl; lia). rewrite ST.coord_mk by (simpl; lia).
    unfold R, S. destruct (Nat.eqb e 0);
      transitivity (K.mul (v e) (K.mul (K.add K.one K.one) h)); try (rewrite Hh; ring);
      ring [K.i_squared]. }
  assert (Hphi : forall e, e < 16 -> ST.phi (ST.x5 R S) e = K.zero).
  { intros e He. unfold ST.phi, ST.x5. cbn [fst snd].
    rewrite ST.coord_mk by (simpl; lia). rewrite coord_conj by (simpl; lia). rewrite ST.coord_mk by (simpl; lia).
    unfold R, S. destruct (Nat.eqb e 0); ring [K.i_squared]. }
  assert (H1 : forall c, c < 16 -> ST.phi (T.mul 5 (ST.y5 a b) (ST.x5 R S)) c = K.zero).
  { intros c Hc. rewrite ST.transport_phi by exact Hc.
    rewrite (ST.SP.P.sumk_ext 16 _ (fun e => K.mul (Mr env c e) (v e))).
    - rewrite <- !sumk_same. rewrite <- lsum_seq. apply Hker. apply in_seq. lia.
    - intros e He. rewrite Hpsi by exact He. unfold Mr. unfold env, ST.envzw.
      change (map (ST.zc a b) (seq 1 15) ++ map (ST.wc a b) (seq 1 15)) with (envft (ST.zc a b) (ST.wc a b)).
      rewrite evM_Aent by assumption.
      replace (Nat.ltb c 16) with true by (symmetry; apply Nat.ltb_lt; lia).
      replace (Nat.ltb e 16) with true by (symmetry; apply Nat.ltb_lt; lia). reflexivity. }
  assert (H2 : forall c, c < 16 -> ST.psi (T.mul 5 (ST.y5 a b) (ST.x5 R S)) c = K.zero).
  { intros c Hc. rewrite ST.transport_psi by exact Hc.
    apply ST.SP.P.sumk_zero. intros e He. rewrite Hphi by exact He. ring. }
  split.
  - intros Hx. assert (E := f_equal (fun u => T.coord 4 (fst u) c0) Hx). cbv beta in E.
    change (fst (T.zero 5)) with (T.zero 4) in E. change (fst (ST.x5 R S)) with (ST.mk 4 R) in E.
    rewrite coord_zero, ST.coord_mk in E by (apply in_seq in Hc0; simpl; lia).
    unfold R in E. apply Hv0. apply (PK.mul_zero_l h (v c0)).
    + rewrite <- E. ring.
    + intros Hz. apply PK.one_nonzero. rewrite <- Hh, Hz. ring.
  - destruct (T.mul 5 (ST.y5 a b) (ST.x5 R S)) as [u1 u2] eqn:Eu.
    assert (H1' : forall c, c < 16 -> K.add (T.coord 4 u1 c) (K.mul K.i (T.coord 4 (T.conjugate 4 u2) c)) = K.zero)
      by (intros c Hc; specialize (H1 c Hc); unfold ST.phi in H1; cbn [fst snd] in H1; exact H1).
    assert (H2' : forall c, c < 16 -> K.sub (T.coord 4 u1 c) (K.mul K.i (T.coord 4 (T.conjugate 4 u2) c)) = K.zero)
      by (intros c Hc; specialize (H2 c Hc); unfold ST.psi in H2; cbn [fst snd] in H2; exact H2).
    simpl. f_equal; apply eq_zero_of_coords; intros c Hc; simpl in Hc.
    + specialize (H1' c Hc). specialize (H2' c Hc).
      apply (PK.mul_zero_l (K.add K.one K.one)); [|exact two_ne].
      transitivity (K.add (K.add (T.coord 4 u1 c) (K.mul K.i (T.coord 4 (T.conjugate 4 u2) c)))
                          (K.sub (T.coord 4 u1 c) (K.mul K.i (T.coord 4 (T.conjugate 4 u2) c)))); [ring|].
      rewrite H1', H2'. ring.
    + specialize (H1' c Hc). specialize (H2' c Hc).
      assert (Hcj : T.coord 4 (T.conjugate 4 u2) c = K.zero).
      { apply (PK.mul_zero_l (K.mul (K.add K.one K.one) K.i)).
        - transitivity (K.sub (K.add (T.coord 4 u1 c) (K.mul K.i (T.coord 4 (T.conjugate 4 u2) c)))
                              (K.sub (T.coord 4 u1 c) (K.mul K.i (T.coord 4 (T.conjugate 4 u2) c)))); [ring|].
          rewrite H1', H2'. ring.
        - intros Hz. apply i_ne. apply (PK.mul_zero_l (K.add K.one K.one)); [exact Hz|exact two_ne]. }
      rewrite coord_conj in Hcj by exact Hc. destruct (Nat.eqb c 0); [exact Hcj|].
      replace (T.coord 4 u2 c) with (K.opp (K.opp (T.coord 4 u2 c))) by ring. rewrite Hcj. ring.
Qed.

End Stiefel.
End StiefelZeroDivisor.
