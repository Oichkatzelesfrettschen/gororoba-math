(** The real case: every nonzero A_5 Stiefel element over the real numbers is a zero divisor.

    Cplx is the field R x R with (a, b)(c, d) = (ac - bd, ad + bc) and i = (0, 1); StiefelZeroDivisor
    applies to it. re and im take real and imaginary parts coordinatewise from the tower over Cplx to the
    tower over R, and emb embeds the real tower. Multiplication by an embedded real element on either side
    commutes with re and im (mul_emb), so a complex annihilator x of a real y gives the real annihilators
    re x and im x, one of them nonzero. *)

From Stdlib Require Import Reals Lra Lia Field Ring List PeanoNat.
Require Import CdTowerRing Pfaffian StiefelA5Transport StiefelA5ZeroDivisor.
Import ListNotations.
Local Open Scope R_scope.

Module RBase <: CommutativeRing.
  Definition t := R.
  Definition zero := 0.
  Definition one := 1.
  Definition add := Rplus.
  Definition mul := Rmult.
  Definition sub := Rminus.
  Definition opp := Ropp.
  Lemma ring_th : ring_theory zero one add mul sub opp (@eq t).
  Proof. exact RTheory. Qed.
End RBase.

Module Cplx <: PfFieldI.
  Definition t := (R * R)%type.
  Definition zero : t := (0, 0).
  Definition one : t := (1, 0).
  Definition add (x y : t) : t := (fst x + fst y, snd x + snd y).
  Definition mul (x y : t) : t := (fst x * fst y - snd x * snd y, fst x * snd y + snd x * fst y).
  Definition opp (x : t) : t := (- fst x, - snd x).
  Definition sub (x y : t) : t := add x (opp y).
  Definition inv (x : t) : t :=
    (fst x / (fst x * fst x + snd x * snd x), - snd x / (fst x * fst x + snd x * snd x)).
  Definition div (x y : t) : t := mul x (inv y).
  Definition i : t := (0, 1).

  Ltac pair_ring := intros; repeat match goal with p : t |- _ => destruct p end;
    unfold zero, one, add, mul, opp, sub, i; apply injective_projections; simpl; ring.

  Lemma ring_th : ring_theory zero one add mul sub opp (@eq t).
  Proof. constructor; pair_ring. Qed.

  Lemma norm_nonzero (x : t) : x <> zero -> fst x * fst x + snd x * snd x <> 0.
  Proof.
    destruct x as [a b]. simpl. intros H N. apply H. unfold zero.
    assert (a = 0) by nra. assert (b = 0) by nra. subst. reflexivity.
  Qed.

  Lemma field_th : field_theory zero one add mul sub opp div inv (@eq t).
  Proof.
    constructor.
    - exact ring_th.
    - unfold one, zero. intros H. injection H. lra.
    - reflexivity.
    - intros [a b] Hp. pose proof (norm_nonzero (a, b) Hp) as N. simpl in N.
      unfold inv, mul, one. simpl. f_equal; field; exact N.
  Qed.

  Definition eq_dec (x y : t) : {x = y} + {x <> y}.
  Proof.
    destruct x as [a b], y as [c d].
    destruct (Req_EM_T a c) as [->|H1]; [|right; intros E; injection E; intros; contradiction].
    destruct (Req_EM_T b d) as [->|H2]; [left; reflexivity|right; intros E; injection E; intros; contradiction].
  Defined.

  Lemma two_nonzero : add one one <> zero.
  Proof. unfold add, one, zero. simpl. intros E. injection E. lra. Qed.

  Lemma i_squared : mul i i = opp one.
  Proof. unfold mul, i, opp, one. simpl. f_equal; ring. Qed.
End Cplx.

Module CZ := StiefelZeroDivisor Cplx.

Ltac rring := match goal with |- ?a = ?b => change (@eq R a b) end; ring.
Module CT := CZ.T.
Module RT := RingTower RBase.

Fixpoint re (k : nat) : CT.cd k -> RT.cd k :=
  match k as d return CT.cd d -> RT.cd d with
  | O => fun v => fst v
  | S j => fun v => (re j (fst v), re j (snd v))
  end.

Fixpoint im (k : nat) : CT.cd k -> RT.cd k :=
  match k as d return CT.cd d -> RT.cd d with
  | O => fun v => snd v
  | S j => fun v => (im j (fst v), im j (snd v))
  end.

Fixpoint emb (k : nat) : RT.cd k -> CT.cd k :=
  match k as d return RT.cd d -> CT.cd d with
  | O => fun v => (v, 0)
  | S j => fun v => (emb j (fst v), emb j (snd v))
  end.

Lemma re_add k : forall u v, re k (CT.add k u v) = RT.add k (re k u) (re k v).
Proof. induction k as [|k IH]; intros [u1 u2] [v1 v2]; simpl; [reflexivity|]. rewrite !IH. reflexivity. Qed.

Lemma im_add k : forall u v, im k (CT.add k u v) = RT.add k (im k u) (im k v).
Proof. induction k as [|k IH]; intros [u1 u2] [v1 v2]; simpl; [reflexivity|]. rewrite !IH. reflexivity. Qed.

Lemma re_neg k : forall u, re k (CT.scale k CT.neg_one u) = RT.scale k RT.neg_one (re k u).
Proof.
  induction k as [|k IH]; intros u.
  - destruct u as [x y]. unfold CT.neg_one, RT.neg_one. simpl. unfold Cplx.mul, Cplx.opp, Cplx.one, RBase.mul, RBase.opp, RBase.one. simpl. rring.
  - destruct u as [u1 u2]. simpl. rewrite !IH. reflexivity.
Qed.

Lemma im_neg k : forall u, im k (CT.scale k CT.neg_one u) = RT.scale k RT.neg_one (im k u).
Proof.
  induction k as [|k IH]; intros u.
  - destruct u as [x y]. unfold CT.neg_one, RT.neg_one. simpl. unfold Cplx.mul, Cplx.opp, Cplx.one, RBase.mul, RBase.opp, RBase.one. simpl. rring.
  - destruct u as [u1 u2]. simpl. rewrite !IH. reflexivity.
Qed.

Lemma re_conj k : forall u, re k (CT.conjugate k u) = RT.conjugate k (re k u).
Proof. induction k as [|k IH]; intros u; [reflexivity|]. destruct u as [u1 u2]. simpl. rewrite IH, re_neg. reflexivity. Qed.

Lemma im_conj k : forall u, im k (CT.conjugate k u) = RT.conjugate k (im k u).
Proof. induction k as [|k IH]; intros u; [reflexivity|]. destruct u as [u1 u2]. simpl. rewrite IH, im_neg. reflexivity. Qed.

Lemma emb_neg k : forall y, CT.scale k CT.neg_one (emb k y) = emb k (RT.scale k RT.neg_one y).
Proof.
  induction k as [|k IH]; intros y.
  - unfold CT.neg_one, RT.neg_one. simpl. unfold Cplx.mul, Cplx.opp, Cplx.one, RBase.mul, RBase.opp, RBase.one.
    apply injective_projections; simpl; rring.
  - destruct y as [p q]. simpl. rewrite !IH. reflexivity.
Qed.

Lemma emb_conj k : forall y, CT.conjugate k (emb k y) = emb k (RT.conjugate k y).
Proof.
  induction k as [|k IH]; intros y; [reflexivity|]. destruct y as [y1 y2]. simpl. rewrite IH, emb_neg. reflexivity.
Qed.

Lemma mul_emb k : forall y x,
  re k (CT.mul k (emb k y) x) = RT.mul k y (re k x) /\ im k (CT.mul k (emb k y) x) = RT.mul k y (im k x) /\
  re k (CT.mul k x (emb k y)) = RT.mul k (re k x) y /\ im k (CT.mul k x (emb k y)) = RT.mul k (im k x) y.
Proof.
  induction k as [|k IH]; intros y x.
  - destruct x as [p q]. simpl. unfold Cplx.mul, RBase.mul. simpl. repeat split; rring.
  - destruct y as [y1 y2], x as [x1 x2]. simpl.
    rewrite !re_add, !im_add, !re_neg, !im_neg, !emb_conj.
    destruct (IH y1 x1) as [A1 [B1 [C1 D1]]]. destruct (IH y2 (CT.conjugate k x1)) as [A2 [B2 [C2 D2]]].
    destruct (IH (RT.conjugate k y2) x2) as [A3 [B3 [C3 D3]]]. destruct (IH y1 x2) as [A4 [B4 [C4 D4]]].
    destruct (IH y2 x2) as [A5 [B5 [C5 D5]]]. destruct (IH (RT.conjugate k y1) x1) as [A6 [B6 [C6 D6]]].
    destruct (IH y2 (CT.conjugate k x2)) as [A7 [B7 [C7 D7]]]. destruct (IH y1 (CT.conjugate k x1)) as [A8 [B8 [C8 D8]]].
    destruct (IH y2 x1) as [A9 [B9 [C9 D9]]]. destruct (IH (RT.conjugate k y1) x2) as [A10 [B10 [C10 D10]]].
    rewrite ?A1, ?B1, ?C1, ?D1, ?A2, ?B2, ?C2, ?D2, ?A3, ?B3, ?C3, ?D3, ?A4, ?B4, ?C4, ?D4, ?A5, ?B5, ?C5, ?D5,
            ?A6, ?B6, ?C6, ?D6, ?A7, ?B7, ?C7, ?D7, ?A8, ?B8, ?C8, ?D8, ?A9, ?B9, ?C9, ?D9, ?A10, ?B10, ?C10, ?D10.
    rewrite ?re_conj, ?im_conj. repeat split; reflexivity.
Qed.

Fixpoint rsum (n : nat) (f : nat -> R) : R := match n with O => 0 | S m => rsum m f + f m end.

Fixpoint rmk (k : nat) (f : nat -> R) : RT.cd k :=
  match k as d return RT.cd d with
  | O => f O
  | S j => (rmk j f, rmk j (fun i => f (i + Nat.pow 2 j)%nat))
  end.

(** The real Stiefel element (p, q) with pure halves of coordinates a_k and b_k, k = 1..15. *)
Definition ry5 (a b : nat -> R) : RT.cd 5 :=
  (rmk 4 (fun j => if Nat.eqb j 0 then 0 else a j), rmk 4 (fun j => if Nat.eqb j 0 then 0 else b j)).

Lemma mk_ext k : forall f g, (forall j, f j = g j) -> CZ.ST.mk k f = CZ.ST.mk k g.
Proof.
  induction k as [|k IH]; intros f g H; simpl; [apply H|].
  f_equal; apply IH; intros j; apply H.
Qed.

Lemma emb_rmk k : forall f, emb k (rmk k f) = CZ.ST.mk k (fun j => (f j, 0)).
Proof. induction k as [|k IH]; intros f; simpl; [reflexivity|]. rewrite !IH. reflexivity. Qed.

Lemma emb_pair k p q : emb (S k) (p, q) = (emb k p, emb k q).
Proof. reflexivity. Qed.

Lemma re_zero k : re k (CT.zero k) = RT.zero k.
Proof. induction k as [|k IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma im_zero k : im k (CT.zero k) = RT.zero k.
Proof. induction k as [|k IH]; simpl; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma zero_of_parts k : forall x, re k x = RT.zero k -> im k x = RT.zero k -> x = CT.zero k.
Proof.
  induction k as [|k IH]; intros x Hr Hi.
  - destruct x as [p q]. simpl in *. subst. reflexivity.
  - destruct x as [x1 x2]. simpl in *. injection Hr as Hr1 Hr2. injection Hi as Hi1 Hi2.
    rewrite (IH x1), (IH x2); auto.
Qed.

Lemma rt_eq_dec k : forall u v : RT.cd k, {u = v} + {u <> v}.
Proof.
  induction k as [|k IH]; intros u v.
  - exact (Req_EM_T u v).
  - destruct u as [u1 u2], v as [v1 v2]. destruct (IH u1 v1) as [->|N]; [|right; intros E; injection E; intros; contradiction].
    destruct (IH u2 v2) as [->|N]; [left; reflexivity|right; intros E; injection E; intros; contradiction].
Defined.

Lemma sumk_emb n (g : nat -> R) : CZ.PK.P.sumk n (fun m => (g m, 0)) = (rsum n g, 0).
Proof.
  induction n as [|n IH]; [reflexivity|]. simpl. rewrite IH. unfold Cplx.add. simpl.
  apply injective_projections; simpl; ring.
Qed.

Theorem real_stiefel_zero_divisor (a b : nat -> R) :
  rsum 15 (fun m => a (S m) * a (S m)) = rsum 15 (fun m => b (S m) * b (S m)) ->
  rsum 15 (fun m => a (S m) * b (S m)) = 0 ->
  exists x : RT.cd 5, x <> RT.zero 5 /\ RT.mul 5 (ry5 a b) x = RT.zero 5.
Proof.
  intros Hn Ho.
  set (ca := fun j => (a j, 0) : Cplx.t). set (cb := fun j => (b j, 0) : Cplx.t).
  assert (Esq : forall (f g : nat -> R), CZ.PK.P.sumk 15 (fun m => Cplx.mul ((f (S m), 0) : Cplx.t) ((g (S m), 0) : Cplx.t))
                    = (rsum 15 (fun m => f (S m) * g (S m)), 0)).
  { intros f g. rewrite <- sumk_emb. apply CZ.PK.P.sumk_ext. intros m _. unfold Cplx.mul. simpl.
    apply injective_projections; simpl; ring. }
  assert (Hn' : CZ.PK.P.sumk 15 (fun m => Cplx.mul (ca (S m)) (ca (S m))) = CZ.PK.P.sumk 15 (fun m => Cplx.mul (cb (S m)) (cb (S m)))).
  { unfold ca, cb. rewrite !Esq, Hn. reflexivity. }
  assert (Ho' : CZ.PK.P.sumk 15 (fun m => Cplx.mul (ca (S m)) (cb (S m))) = Cplx.zero).
  { unfold ca, cb. rewrite Esq, Ho. reflexivity. }
  destruct (CZ.stiefel_zero_divisor ca cb Hn' Ho') as [x [Hx Hyx]].
  assert (Ey : CZ.ST.y5 ca cb = emb 5 (ry5 a b)).
  { unfold CZ.ST.y5, ry5. rewrite emb_pair, !emb_rmk. f_equal; apply mk_ext; intros j; unfold CZ.ST.pureA, ca, cb;
      destruct (Nat.eqb j 0); reflexivity. }
  rewrite Ey in Hyx.
  destruct (mul_emb 5 (ry5 a b) x) as [Hre [Him _]].
  rewrite Hyx, re_zero in Hre. rewrite Hyx, im_zero in Him.
  destruct (rt_eq_dec 5 (re 5 x) (RT.zero 5)) as [Zr|Nr].
  - exists (im 5 x). split; [|symmetry; exact Him].
    intros Zi. apply Hx. apply zero_of_parts; assumption.
  - exists (re 5 x). split; [exact Nr|symmetry; exact Hre].
Qed.
