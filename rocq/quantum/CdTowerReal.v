(** The Cayley-Dickson pair tower with real coefficients: cd 0 is the Stdlib
    real line R and cd (k + 1) is cd k * cd k, with the doubling
    (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)) that
    gororoba_quantum/cd_core.py cd_sign reads and that
    CdImaginarySumConference.v states over the integers. The definitions and
    the linear laws below are that file's, restated with R in place of Z, so
    that a theorem of the integer tower whose proof cancels nonzero factors
    without dividing carries over to every element with real coordinates.
    Coordinate i of a level-(j + 1) element lies in its first half when
    i < 2^j, so index bit j selects the doubling half as in cd_sign.

    Every lemma closes with the coordinate extensionality lemma ext and the
    real ring, so its proof term depends on the Stdlib construction of R and
    on nothing else; Print Assumptions lists that construction's axioms. *)

From Stdlib Require Import Reals Lia Lra.
Open Scope R_scope.

Fixpoint cd (k : nat) : Type :=
  match k with O => R | S j => (cd j * cd j)%type end.

Fixpoint zero (k : nat) : cd k :=
  match k with O => 0 | S j => (zero j, zero j) end.

Fixpoint one (k : nat) : cd k :=
  match k with O => 1 | S j => (one j, zero j) end.

Fixpoint add (k : nat) : cd k -> cd k -> cd k :=
  match k as d return cd d -> cd d -> cd d with
  | O => Rplus
  | S j => fun x y => (add j (fst x) (fst y), add j (snd x) (snd y))
  end.

Fixpoint scale (k : nat) (r : R) : cd k -> cd k :=
  match k as d return cd d -> cd d with
  | O => fun v => r * v
  | S j => fun v => (scale j r (fst v), scale j r (snd v))
  end.

Fixpoint conjugate (k : nat) : cd k -> cd k :=
  match k as d return cd d -> cd d with
  | O => fun v => v
  | S j => fun v => (conjugate j (fst v), scale j (-1) (snd v))
  end.

Fixpoint mul (k : nat) : cd k -> cd k -> cd k :=
  match k as d return cd d -> cd d -> cd d with
  | O => Rmult
  | S j => fun x y =>
      (add j (mul j (fst x) (fst y)) (scale j (-1) (mul j (conjugate j (snd y)) (snd x))),
       add j (mul j (snd y) (fst x)) (mul j (snd x) (conjugate j (fst y))))
  end.

Fixpoint re (k : nat) : cd k -> R :=
  match k as d return cd d -> R with
  | O => fun v => v
  | S j => fun v => re j (fst v)
  end.

Fixpoint dot (k : nat) : cd k -> cd k -> R :=
  match k as d return cd d -> cd d -> R with
  | O => Rmult
  | S j => fun x y => dot j (fst x) (fst y) + dot j (snd x) (snd y)
  end.

Fixpoint coord (k : nat) : cd k -> nat -> R :=
  match k as d return cd d -> nat -> R with
  | O => fun v _ => v
  | S j => fun v i =>
      if Nat.ltb i (Nat.pow 2 j) then coord j (fst v) i else coord j (snd v) (i - Nat.pow 2 j)
  end.

(** Coordinates decide equality, which reduces each vector identity below to
    an identity of real linear combinations. *)

Lemma coord_add k : forall x y i, coord k (add k x y) i = coord k x i + coord k y i.
Proof.
  induction k as [|j IH]; intros x y i; simpl.
  - reflexivity.
  - destruct (Nat.ltb i (Nat.pow 2 j)); apply IH.
Qed.

Lemma coord_scale k : forall r x i, coord k (scale k r x) i = r * coord k x i.
Proof.
  induction k as [|j IH]; intros r x i; simpl.
  - reflexivity.
  - destruct (Nat.ltb i (Nat.pow 2 j)); apply IH.
Qed.

Lemma coord_zero k : forall i, coord k (zero k) i = 0.
Proof.
  induction k as [|j IH]; intro i; simpl.
  - reflexivity.
  - destruct (Nat.ltb i (Nat.pow 2 j)); apply IH.
Qed.

Lemma ext k : forall x y, (forall i, (i < Nat.pow 2 k)%nat -> coord k x i = coord k y i) -> x = y.
Proof.
  induction k as [|j IH]; intros x y H.
  - exact (H O (Nat.lt_0_1)).
  - destruct x as [x1 x2], y as [y1 y2]. simpl in H. f_equal; apply IH; intros i Hi.
    + specialize (H i ltac:(simpl; lia)). rewrite (proj2 (Nat.ltb_lt _ _) Hi) in H. exact H.
    + specialize (H (i + Nat.pow 2 j)%nat ltac:(simpl; lia)).
      rewrite (proj2 (Nat.ltb_ge _ _)) in H by lia.
      replace (i + Nat.pow 2 j - Nat.pow 2 j)%nat with i in H by lia. exact H.
Qed.

Create Rewrite HintDb coord.
Hint Rewrite coord_add coord_scale coord_zero : coord.
Ltac vec := apply ext; intros ? _; autorewrite with coord; ring.

(** Linear structure of conjugation and multiplication at every level. *)

Lemma scale_zero k : forall r, scale k r (zero k) = zero k.
Proof. intro r. vec. Qed.

Lemma conj_add k : forall x y, conjugate k (add k x y) = add k (conjugate k x) (conjugate k y).
Proof.
  induction k as [|j IH]; intros x y; simpl.
  - reflexivity.
  - rewrite IH. f_equal. vec.
Qed.

Lemma conj_scale k : forall r x, conjugate k (scale k r x) = scale k r (conjugate k x).
Proof.
  induction k as [|j IH]; intros r x; simpl.
  - reflexivity.
  - rewrite IH. f_equal. vec.
Qed.

Lemma conj_zero k : conjugate k (zero k) = zero k.
Proof.
  induction k as [|j IH]; simpl.
  - reflexivity.
  - rewrite IH, scale_zero. reflexivity.
Qed.

Lemma conj_one k : conjugate k (one k) = one k.
Proof.
  induction k as [|j IH]; simpl.
  - reflexivity.
  - rewrite IH, scale_zero. reflexivity.
Qed.

Lemma conj_conj k : forall x, conjugate k (conjugate k x) = x.
Proof.
  induction k as [|j IH]; intro x; simpl.
  - reflexivity.
  - destruct x as [x1 x2]. simpl. rewrite IH. f_equal. vec.
Qed.

Lemma mul_linear k :
  (forall x y z, mul k (add k x y) z = add k (mul k x z) (mul k y z)) /\
  (forall x y z, mul k z (add k x y) = add k (mul k z x) (mul k z y)) /\
  (forall r x z, mul k (scale k r x) z = scale k r (mul k x z)) /\
  (forall r x z, mul k z (scale k r x) = scale k r (mul k z x)).
Proof.
  induction k as [|j IH]; simpl.
  - repeat split; intros; ring.
  - destruct IH as [Al [Ar [Sl Sr]]].
    repeat split.
    + intros [x1 x2] [y1 y2] [z1 z2]; simpl; rewrite ?Al, ?Ar, ?Sl, ?Sr; f_equal; vec.
    + intros [x1 x2] [y1 y2] [z1 z2]; simpl; rewrite ?conj_add, ?Al, ?Ar, ?Sl, ?Sr; f_equal; vec.
    + intros r [x1 x2] [z1 z2]; simpl; rewrite ?Al, ?Ar, ?Sl, ?Sr; f_equal; vec.
    + intros r [x1 x2] [z1 z2]; simpl; rewrite ?conj_scale, ?Al, ?Ar, ?Sl, ?Sr; f_equal; vec.
Qed.

Lemma mul_add_l k : forall x y z, mul k (add k x y) z = add k (mul k x z) (mul k y z).
Proof. apply mul_linear. Qed.
Lemma mul_add_r k : forall x y z, mul k z (add k x y) = add k (mul k z x) (mul k z y).
Proof. apply mul_linear. Qed.
Lemma mul_scale_l k : forall r x z, mul k (scale k r x) z = scale k r (mul k x z).
Proof. apply mul_linear. Qed.
Lemma mul_scale_r k : forall r x z, mul k z (scale k r x) = scale k r (mul k z x).
Proof. apply mul_linear. Qed.

Lemma mul_zero k : (forall z, mul k (zero k) z = zero k) /\ (forall z, mul k z (zero k) = zero k).
Proof.
  induction k as [|j IH]; simpl.
  - split; intros; ring.
  - destruct IH as [Zl Zr]. split; intros [z1 z2]; simpl; rewrite ?conj_zero, ?Zl, ?Zr; f_equal; vec.
Qed.

Lemma mul_zero_l k z : mul k (zero k) z = zero k. Proof. apply mul_zero. Qed.
Lemma mul_zero_r k z : mul k z (zero k) = zero k. Proof. apply mul_zero. Qed.

Lemma mul_one k : (forall x, mul k (one k) x = x) /\ (forall x, mul k x (one k) = x).
Proof.
  induction k as [|j IH]; simpl.
  - split; [exact Rmult_1_l | exact Rmult_1_r].
  - destruct IH as [Ol Or]. destruct (mul_zero j) as [Zl Zr].
    split; intros [x1 x2]; simpl; rewrite ?conj_zero, ?conj_one, ?Ol, ?Or, ?Zl, ?Zr; f_equal; vec.
Qed.

Lemma mul_one_l k x : mul k (one k) x = x. Proof. apply mul_one. Qed.
Lemma mul_one_r k x : mul k x (one k) = x. Proof. apply mul_one. Qed.

Lemma conj_mul k : forall x y, conjugate k (mul k x y) = mul k (conjugate k y) (conjugate k x).
Proof.
  induction k as [|j IH]; intros x y; simpl.
  - ring.
  - destruct x as [x1 x2], y as [y1 y2]. simpl.
    rewrite ?conj_add, ?conj_scale, ?IH, ?conj_conj, ?mul_scale_l, ?mul_scale_r. f_equal; vec.
Qed.

Lemma add_conj k : forall x, add k x (conjugate k x) = scale k (2 * re k x) (one k).
Proof.
  induction k as [|j IH]; intro x; simpl.
  - change (x + x = 2 * x * 1). ring.
  - destruct x as [x1 x2]. simpl. rewrite IH, scale_zero. f_equal. vec.
Qed.

Create Rewrite HintDb alg.
Hint Rewrite mul_add_l mul_add_r mul_scale_l mul_scale_r conj_add conj_scale conj_mul conj_conj
  conj_one conj_zero mul_one_l mul_one_r mul_zero_l mul_zero_r : alg.

(** conj(x) = 2 re(x) 1 - x: conjugation is the reflection through the real
    line, which every identity of the form x (conj(x) y) = conj(x) (x y)
    reads as bilinearity. *)

Lemma conj_split k x : conjugate k x = add k (scale k (2 * re k x) (one k)) (scale k (-1) x).
Proof.
  transitivity (add k (add k x (conjugate k x)) (scale k (-1) x)); [vec | now rewrite add_conj].
Qed.

(** The coordinate inner product: bilinear, symmetric, conjugation-invariant,
    and a sum of squares. *)

Lemma dot_linear k :
  (forall x y z, dot k (add k x y) z = dot k x z + dot k y z) /\
  (forall x y z, dot k z (add k x y) = dot k z x + dot k z y) /\
  (forall r x z, dot k (scale k r x) z = r * dot k x z) /\
  (forall r x z, dot k z (scale k r x) = r * dot k z x).
Proof.
  induction k as [|j IH]; simpl.
  - repeat split; intros; cbv [dot add scale cd]; ring.
  - destruct IH as [Al [Ar [Sl Sr]]].
    repeat split; intros; cbn [dot add scale fst snd]; rewrite ?Al, ?Ar, ?Sl, ?Sr; ring.
Qed.

Lemma dot_add_l k x y z : dot k (add k x y) z = dot k x z + dot k y z. Proof. apply dot_linear. Qed.
Lemma dot_add_r k x y z : dot k z (add k x y) = dot k z x + dot k z y. Proof. apply dot_linear. Qed.
Lemma dot_scale_l k r x z : dot k (scale k r x) z = r * dot k x z. Proof. apply dot_linear. Qed.
Lemma dot_scale_r k r x z : dot k z (scale k r x) = r * dot k z x. Proof. apply dot_linear. Qed.

Lemma dot_conj k : forall x y, dot k (conjugate k x) y = dot k x (conjugate k y).
Proof.
  induction k as [|j IH]; intros x y.
  - reflexivity.
  - destruct x as [x1 x2], y as [y1 y2]. cbn [dot conjugate fst snd].
    rewrite IH, dot_scale_l, dot_scale_r. reflexivity.
Qed.

Create Rewrite HintDb dotlin.
Hint Rewrite dot_add_l dot_add_r dot_scale_l dot_scale_r : dotlin.

Lemma dot_comm k : forall x y, dot k x y = dot k y x.
Proof.
  induction k as [|j IH]; intros x y; simpl.
  - ring.
  - rewrite (IH (fst x)), (IH (snd x)). reflexivity.
Qed.

Lemma dot_zero_l k : forall x, dot k (zero k) x = 0.
Proof.
  induction k as [|j IH]; intro x; simpl.
  - ring.
  - rewrite !IH. ring.
Qed.

Lemma dot_zero_r k : forall x, dot k x (zero k) = 0.
Proof. intro x. rewrite dot_comm. apply dot_zero_l. Qed.

Lemma re_zero k : re k (zero k) = 0.
Proof. induction k as [|j IH]; simpl; [reflexivity | exact IH]. Qed.

Lemma re_one k : re k (one k) = 1.
Proof. induction k as [|j IH]; simpl; [reflexivity | exact IH]. Qed.

Lemma dot_one_r k : forall x, dot k x (one k) = re k x.
Proof.
  induction k as [|j IH]; intro x; simpl.
  - ring.
  - rewrite IH, dot_zero_r. ring.
Qed.

Lemma dot_self_nonneg k : forall x, 0 <= dot k x x.
Proof.
  induction k as [|j IH]; intro x; simpl.
  - nra.
  - pose proof (IH (fst x)). pose proof (IH (snd x)). lra.
Qed.

Lemma dot_self_zero k : forall x, dot k x x = 0 -> x = zero k.
Proof.
  induction k as [|j IH]; intros x H; simpl in *.
  - nra.
  - destruct x as [x1 x2]. simpl in H.
    pose proof (dot_self_nonneg j x1). pose proof (dot_self_nonneg j x2).
    rewrite (IH x1), (IH x2); [reflexivity | lra | lra].
Qed.
