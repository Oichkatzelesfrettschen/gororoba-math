(** * The factored cofactor certificate as the per-quadric hypothesis of the K2 Hilbert bound.

    [check_factored_sound] of K2CofactorFactored.v concludes [in_local_ideal] for the quadric
    [subst_q n G q] over [J ++ m_products n G 2]. [LI_of_ili] of K2HilbertBound.v turns that conclusion
    into [LI], the per-quadric hypothesis of [hilbert_upper_bound_of_red], [hilbert_upper_sel_of_red] and
    [hilbert_cell_of_red]. The theorems below state the two steps and their composition: a factored
    certificate for each quadric of [Q], together with an accepted [check_red], yields the span of the
    degree-[d] products modulo [J ++ m_products n G d].

    Convention: [kcert], [kdata] and the generator list [J ++ m_products n G 2] are those of
    K2CofactorCertificate.v; the quadric [q] is read through [subst_q n G] as there; [LI] and [check_red]
    are those of K2HilbertBound.v. *)

From Stdlib Require Import ZArith Lia List Bool PeanoNat NArith Znumtheory.
Require Import HilbertCellCertificate K2CofactorCertificate K2CofactorFactored K2HilbertBound.
Import ListNotations.
Open Scope Z_scope.

Theorem check_factored_LI (p : Z) (n : nat) (J G : list poly) (q : list (Z * list nat)) (c : kcert) :
  check_factored p n J G q c = true ->
  LI p n (J ++ m_products n G 2) (subst_q n G q).
Proof. intros H. apply LI_of_ili. exact (check_factored_sound _ _ _ _ _ _ H). Qed.

Theorem check_data_factored_LI (p : Z) (n : nat) (J G : list poly) (q : list (Z * list nat))
  (b : N) (dat : kdata) :
  check_data_factored p n J G q b dat = true ->
  LI p n (J ++ m_products n G 2) (subst_q n G q).
Proof. intros H. apply LI_of_ili. exact (check_data_factored_sound _ _ _ _ _ _ _ H). Qed.

(** The checker of a list of quadrics: one certificate for each quadric, in order. *)
Definition check_factored_all (p : Z) (n : nat) (J G : list poly) (Q : list (list (Z * list nat)))
  (cs : list kcert) : bool :=
  Nat.eqb (length cs) (length Q) &&
  forallb (fun qc => check_factored p n J G (fst qc) (snd qc)) (combine Q cs).

Lemma check_factored_all_members (p : Z) (n : nat) (J G : list poly) (Q : list (list (Z * list nat))) :
  forall cs, check_factored_all p n J G Q cs = true ->
  forall q, In q Q -> exists c, check_factored p n J G q c = true.
Proof.
  induction Q as [|q0 Q IH]; intros cs H q Hq; [destruct Hq|].
  unfold check_factored_all in H. apply andb_true_iff in H as [Hl Hf].
  apply Nat.eqb_eq in Hl.
  destruct cs as [|c0 cs]; [discriminate Hl|].
  cbn [combine forallb fst snd] in Hf. apply andb_true_iff in Hf as [H0 Hf].
  destruct Hq as [Hq | Hq].
  - subst q0. exists c0. exact H0.
  - cbn [length] in Hl. apply (IH cs); [|exact Hq].
    unfold check_factored_all. apply andb_true_iff. split;
      [apply Nat.eqb_eq; lia|exact Hf].
Qed.

Theorem hilbert_upper_bound_of_factored (p : Z) (n : nat) (J G : list poly) (d : nat)
  (Q : list (list (Z * list nat))) (S : list mono) (red : list red_entry) (cs : list kcert) :
  prime p ->
  check_red p n G d Q S red = true ->
  check_factored_all p n J G Q cs = true ->
  spans_mod p n (J ++ m_products n G d) (products n G d) (map (ymono n G) S).
Proof.
  intros Hp Hr Hc. refine (hilbert_upper_bound_of_red p n J G d Q S red Hp Hr _).
  intros q Hq. destruct (check_factored_all_members p n J G Q cs Hc q Hq) as [c Hqc].
  exact (check_factored_LI p n J G q c Hqc).
Qed.

(** Toy instance of K2HilbertBound.v: the unfactored certificate of its quadric is accepted by the
    factored checker. *)
Lemma toy_factored_all_accepted :
  check_factored_all 7 1 kb_toy_J kb_toy_G kb_toy_Q kb_toy_cof = true.
Proof. vm_compute. reflexivity. Qed.

Theorem toy_bound_factored :
  spans_mod 7 1 (kb_toy_J ++ m_products 1 kb_toy_G 3) (products 1 kb_toy_G 3)
    (map (ymono 1 kb_toy_G) kb_toy_S).
Proof.
  exact (hilbert_upper_bound_of_factored 7 1 _ _ 3 _ _ _ _ prime_7 toy_red_accepted toy_factored_all_accepted).
Qed.

Print Assumptions check_factored_LI.
Print Assumptions check_data_factored_LI.
Print Assumptions hilbert_upper_bound_of_factored.
Print Assumptions toy_bound_factored.
