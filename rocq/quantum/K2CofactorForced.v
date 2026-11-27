(** Forced accumulation for the factored cofactor checker: after each row of a product the trie is walked
    completely, so the kernel holds no unevaluated insertion between rows.

    Convention: the tries, the polynomials and the certificate data are those of K2CofactorCertificate.v and
    K2CofactorFactored.v; [check_factoredF] requires p > 0 as [check_factored] does.

    Mechanism: [check_factoredF] has the shape of [check_factored] of K2CofactorFactored.v with [tmul], [tcombo]
    and [hfold] replaced by variants that evaluate the trie after each row; [check_factoredF_eq] states that the
    result equals [check_factored], so [check_factoredF_sound] has the conclusion of [check_factored_sound]. The
    walk [tforce] returns a boolean that the match discards in both branches. *)

From Stdlib Require Import ZArith List Bool NArith.
Require Import HilbertCellCertificate K2CofactorCertificate K2CofactorFactored.
Import ListNotations.
Open Scope Z_scope.

Fixpoint tforce (t : tr) : bool :=
  match t with
  | TL => false
  | TN l v r => xorb (xorb (tforce l) (tforce r)) (Z.eqb v 0)
  end.

Definition stepF (s : Z) (g : poly) (t : tr) (a : mono * Z) : tr :=
  let t' := trow s a g t in
  match tforce t' with true => t' | false => t' end.

Lemma stepF_eq (s : Z) (g : poly) (t : tr) (a : mono * Z) : stepF s g t a = trow s a g t.
Proof. unfold stepF. destruct (tforce (trow s a g t)); reflexivity. Qed.

Definition tmulF (s : Z) (t : tr) (f g : poly) : tr := fold_left (stepF s g) f t.

Lemma tmulF_eq (s : Z) (g : poly) (f : poly) : forall t, tmulF s t f g = tmul s t f g.
Proof.
  induction f as [|a f IH]; intros t; unfold tmulF, tmul in *; cbn [fold_left]; [reflexivity|].
  rewrite stepF_eq. apply IH.
Qed.

Fixpoint tcomboF (s : Z) (t : tr) (cs gs : list poly) : tr :=
  match cs, gs with
  | c :: cs', g :: gs' => tcomboF s (tmulF s t c g) cs' gs'
  | _, _ => t
  end.

Lemma tcomboF_eq (s : Z) : forall cs gs t, tcomboF s t cs gs = tcombo s t cs gs.
Proof.
  induction cs as [|c cs IH]; intros gs t; destruct gs as [|g gs]; cbn [tcomboF tcombo]; try reflexivity.
  rewrite tmulF_eq. apply IH.
Qed.

Fixpoint hfoldF (t : tr) (hs : list (poly * poly)) : tr :=
  match hs with
  | [] => t
  | gh :: r => hfoldF (tmulF (-1) t (fst gh) (snd gh)) r
  end.

Lemma hfoldF_eq (hs : list (poly * poly)) : forall t, hfoldF t hs = hfold t hs.
Proof.
  induction hs as [|gh hs IH]; intros t; cbn [hfoldF hfold]; [reflexivity|].
  rewrite tmulF_eq. apply IH.
Qed.

Definition check_factoredF (p : Z) (n : nat) (J G : list poly) (q : list (Z * list nat)) (c : kcert) : bool :=
  Z.ltb 0 p &&
  negb (Z.eqb (const_coef (k_u c) mod p) 0) &&
  wf_b n (k_u c) && forallb (wf_b n) (k_cofs c) &&
  Nat.eqb (length (k_cofs c)) (length J + n * tri (length G)) &&
  tall p (hfoldF (tcomboF (-1) (tmulF 1 TL (k_u c) (subst_q n G q)) (firstn (length J) (k_cofs c)) J)
    (hlist p n G (map (norm_poly p)
      (stage1 n (seq 0 n) (chunk (tri (length G)) n (skipn (length J) (k_cofs c)))
        (repeat [] (tri (length G))))))).

(** The forced variant equals [check_factored]: [tmulF_eq], [tcomboF_eq] and [hfoldF_eq] rewrite each forced
    step to its plain step, since [stepF] returns the same trie in both branches of its match. *)
Lemma check_factoredF_eq (p : Z) (n : nat) (J G : list poly) (q : list (Z * list nat)) (c : kcert) :
  check_factoredF p n J G q c = check_factored p n J G q c.
Proof.
  unfold check_factoredF, check_factored.
  rewrite tmulF_eq, tcomboF_eq, hfoldF_eq. reflexivity.
Qed.

Theorem check_factoredF_sound (p : Z) (n : nat) (J G : list poly) (q : list (Z * list nat)) (c : kcert) :
  check_factoredF p n J G q c = true ->
  in_local_ideal p n (J ++ m_products n G 2) (subst_q n G q).
Proof. rewrite check_factoredF_eq. apply check_factored_sound. Qed.

Definition check_data_factoredF (p : Z) (n : nat) (J G : list poly) (q : list (Z * list nat))
  (b : N) (dat : kdata) : bool :=
  check_factoredF p n J G q (decode_cert b n (length J + n * tri (length G)) dat).

Theorem check_data_factoredF_sound (p : Z) (n : nat) (J G : list poly) (q : list (Z * list nat))
  (b : N) (dat : kdata) :
  check_data_factoredF p n J G q b dat = true ->
  in_local_ideal p n (J ++ m_products n G 2) (subst_q n G q).
Proof. unfold check_data_factoredF. apply check_factoredF_sound. Qed.

Lemma toy_acceptedF : check_factoredF 7 1 toy_J toy_G toy_q toy_cert = true.
Proof. vm_compute. reflexivity. Qed.

Lemma toy_data_rejectedF : check_data_factoredF 7 1 toy_J toy_G toy_q 15 (toy_data 2) = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions check_data_factoredF_sound.
