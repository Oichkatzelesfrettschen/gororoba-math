(** The Cayley-Dickson pair tower over a commutative ring, with the laws that
    hold for every coefficient ring and the exact scope of the kernel swap.

    CdTowerDomain.v states the tower over an ordered integral domain and
    proves Corollary 9.3 of Biss, Dugger and Isaksen (math/0511691),
    a z = 0 exactly when z a = 0, from a vanishing sum of squares vanishing
    termwise. The functor RingTower states the same doubling
    (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)) over a signature that
    holds the ring laws alone, CommutativeRing, so it covers coefficient
    rings that admit no such order, such as Q(i), the complex numbers and
    the finite fields. On it, for every level:

    - kernel_conj: a z = 0 exactly when conj(z) conj(a) = 0, from the
      anti-automorphism law conj(x y) = conj(y) conj(x). Conjugation is
      additive, commutes with scalars and is an involution, so it restricts
      to a linear bijection of ker L_a onto ker R_(conj a).
    - pure_kernel_conj: for a with conj(a) = -a (re_zero_pure: every a with
      re(a) = 0), a z = 0 exactly when conj(z) a = 0, so
      ker R_a = conj(ker L_a).
    - reflect_mul: the map (a, b) -> (a, -b) of level k + 1 preserves the
      product. With reflect_add, reflect_scale, reflect_one, reflect_conj
      and reflect_involutive it is an involutive algebra automorphism that
      commutes with conjugation, and reflect_kernel carries ker L_x onto
      ker L_(reflect x).
    - two_zero_commutative: when 2 = 0 conjugation is the identity and the
      product commutes. level_one_commutative: level 1 commutes over every
      ring, so level 2 is the first level where a z = 0 and z a = 0 can
      differ.
    - diag_mul: a map of level k that preserves sums, scalars, products and
      conjugates extends to level k + 1 by acting on both halves, and the
      extension has the same four properties (diag_add, diag_scale,
      diag_conj), so it extends again.
    - lift_mul: x -> (x, 0) embeds each level in the next as a subalgebra.

    The functor RingTowerI adds an element i with i i = -1. At level 2
    write ((x0, x1), (x2, x3)) as x0 + x1 e_1 + x2 e_2 + x3 e_3. Then
    a = e_1 + i e_2 is pure with a a = 0, w = a e_1 = -1 - i e_3 satisfies
    a w = 0, and w a = -2 a (nilpotent_witness, witness_nilpotent). Lifted
    to level k + 2 this gives kernel_swap_iff_two_zero: over a commutative
    ring that holds a square root of -1, the swap a z = 0 -> z a = 0 holds
    at a level of at least 2 exactly when 2 = 0, and
    pure_kernel_swap_two_zero: the swap for pure a alone already forces
    2 = 0. kernel_swap_witness names the pair when 2 differs from 0. So
    the ring laws alone do not give Corollary 9.3: the ordered-domain
    hypotheses of CdTowerDomain.v suffice for it, 2 = 0 suffices for it,
    and a square root of -1 with 2 different from 0 refutes it, while
    pure_kernel_conj holds in every case.

    Instances: the Gaussian integers Z[i] as pairs of integers, a subring
    of Q(i), and Zmod 5 with i = 2 from CdTwistedProduct.v. In both 2
    differs from 0, so the swap fails at every level from the quaternions
    on, level 5 (dimension 32) included.

    No step uses an order, cancellation, division or decidable equality on
    the coefficients. *)

From Stdlib Require Import Ring Lia ZArith Zmod.
Require CdTwistedProduct.

Create Rewrite HintDb cring_coord.

Module Type CommutativeRing.
  Parameter t : Type.
  Parameter zero one : t.
  Parameter add mul sub : t -> t -> t.
  Parameter opp : t -> t.
  Axiom ring_th : ring_theory zero one add mul sub opp (@eq t).
End CommutativeRing.

Module RingTower (D : CommutativeRing).

Add Ring commutative_ring : D.ring_th.

Definition two : D.t := D.add D.one D.one.
Definition neg_one : D.t := D.opp D.one.

Ltac dring := try unfold neg_one; try unfold two; ring.

(** The tower, with the definitions of CdTowerDomain.v. *)

Fixpoint cd (k : nat) : Type :=
  match k with O => D.t | S j => (cd j * cd j)%type end.

Fixpoint zero (k : nat) : cd k :=
  match k with O => D.zero | S j => (zero j, zero j) end.

Fixpoint one (k : nat) : cd k :=
  match k with O => D.one | S j => (one j, zero j) end.

Fixpoint add (k : nat) : cd k -> cd k -> cd k :=
  match k as d return cd d -> cd d -> cd d with
  | O => D.add
  | S j => fun x y => (add j (fst x) (fst y), add j (snd x) (snd y))
  end.

Fixpoint scale (k : nat) (r : D.t) : cd k -> cd k :=
  match k as d return cd d -> cd d with
  | O => fun v => D.mul r v
  | S j => fun v => (scale j r (fst v), scale j r (snd v))
  end.

Fixpoint conjugate (k : nat) : cd k -> cd k :=
  match k as d return cd d -> cd d with
  | O => fun v => v
  | S j => fun v => (conjugate j (fst v), scale j neg_one (snd v))
  end.

Fixpoint mul (k : nat) : cd k -> cd k -> cd k :=
  match k as d return cd d -> cd d -> cd d with
  | O => D.mul
  | S j => fun x y =>
      (add j (mul j (fst x) (fst y)) (scale j neg_one (mul j (conjugate j (snd y)) (snd x))),
       add j (mul j (snd y) (fst x)) (mul j (snd x) (conjugate j (fst y))))
  end.

Fixpoint re (k : nat) : cd k -> D.t :=
  match k as d return cd d -> D.t with
  | O => fun v => v
  | S j => fun v => re j (fst v)
  end.

Fixpoint coord (k : nat) : cd k -> nat -> D.t :=
  match k as d return cd d -> nat -> D.t with
  | O => fun v _ => v
  | S j => fun v i =>
      if Nat.ltb i (Nat.pow 2 j) then coord j (fst v) i else coord j (snd v) (i - Nat.pow 2 j)
  end.

(** Coordinates decide equality, which reduces each vector identity below to
    an identity of linear combinations in the ring. *)

Lemma coord_add k : forall x y i, coord k (add k x y) i = D.add (coord k x i) (coord k y i).
Proof.
  induction k as [|j IH]; intros x y i; simpl.
  - reflexivity.
  - destruct (Nat.ltb i (Nat.pow 2 j)); apply IH.
Qed.

Lemma coord_scale k : forall r x i, coord k (scale k r x) i = D.mul r (coord k x i).
Proof.
  induction k as [|j IH]; intros r x i; simpl.
  - reflexivity.
  - destruct (Nat.ltb i (Nat.pow 2 j)); apply IH.
Qed.

Lemma coord_zero k : forall i, coord k (zero k) i = D.zero.
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

Hint Rewrite coord_add coord_scale coord_zero : cring_coord.
Ltac vec := apply ext; intros ? _; autorewrite with cring_coord; dring.

(** Linear structure of conjugation and multiplication at every level. *)

Lemma scale_zero k : forall r, scale k r (zero k) = zero k.
Proof. intro r. vec. Qed.

Lemma scale_neg_neg k x : scale k neg_one (scale k neg_one x) = x.
Proof. vec. Qed.

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
  - repeat split; intros; dring.
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
  - split; intros; dring.
  - destruct IH as [Zl Zr]. split; intros [z1 z2]; simpl; rewrite ?conj_zero, ?Zl, ?Zr; f_equal; vec.
Qed.

Lemma mul_zero_l k z : mul k (zero k) z = zero k. Proof. apply mul_zero. Qed.
Lemma mul_zero_r k z : mul k z (zero k) = zero k. Proof. apply mul_zero. Qed.

Lemma mul_one k : (forall x, mul k (one k) x = x) /\ (forall x, mul k x (one k) = x).
Proof.
  induction k as [|j IH]; simpl.
  - split; intros; dring.
  - destruct IH as [Ol Or]. destruct (mul_zero j) as [Zl Zr].
    split; intros [x1 x2]; simpl; rewrite ?conj_zero, ?conj_one, ?Ol, ?Or, ?Zl, ?Zr; f_equal; vec.
Qed.

Lemma mul_one_l k x : mul k (one k) x = x. Proof. apply mul_one. Qed.
Lemma mul_one_r k x : mul k x (one k) = x. Proof. apply mul_one. Qed.

(** The anti-automorphism law. *)

Lemma conj_mul k : forall x y, conjugate k (mul k x y) = mul k (conjugate k y) (conjugate k x).
Proof.
  induction k as [|j IH]; intros x y; simpl.
  - dring.
  - destruct x as [x1 x2], y as [y1 y2]. simpl.
    rewrite ?conj_add, ?conj_scale, ?IH, ?conj_conj, ?mul_scale_l, ?mul_scale_r. f_equal; vec.
Qed.

Lemma add_conj k : forall x, add k x (conjugate k x) = scale k (D.mul two (re k x)) (one k).
Proof.
  induction k as [|j IH]; intro x; simpl.
  - unfold two. dring.
  - destruct x as [x1 x2]. simpl. rewrite IH, scale_zero. f_equal. vec.
Qed.

(** conj(x) = 2 re(x) 1 - x. *)

Lemma conj_split k x : conjugate k x = add k (scale k (D.mul two (re k x)) (one k)) (scale k neg_one x).
Proof.
  transitivity (add k (add k x (conjugate k x)) (scale k neg_one x)); [vec | now rewrite add_conj].
Qed.

(** Kernels of left and right multiplication. Conjugation carries the
    kernel of L_a onto the kernel of R_(conj a); for a pure a, where
    conj(a) = -a, that is the kernel of R_a. *)

Theorem kernel_conj k a z : mul k a z = zero k <-> mul k (conjugate k z) (conjugate k a) = zero k.
Proof.
  split; intro H.
  - rewrite <- conj_mul, H. apply conj_zero.
  - rewrite <- (conj_conj k (mul k a z)), conj_mul, H. apply conj_zero.
Qed.

Definition pure k (a : cd k) : Prop := conjugate k a = scale k neg_one a.

Lemma re_zero_pure k a : re k a = D.zero -> pure k a.
Proof. intro H. unfold pure. rewrite conj_split, H. vec. Qed.

Lemma scale_neg_one_zero k x : scale k neg_one x = zero k <-> x = zero k.
Proof.
  split; intro H.
  - rewrite <- (scale_neg_neg k x), H. apply scale_zero.
  - rewrite H. apply scale_zero.
Qed.

Theorem pure_kernel_conj k a z : pure k a -> (mul k a z = zero k <-> mul k (conjugate k z) a = zero k).
Proof.
  intro P. rewrite kernel_conj, P, mul_scale_r. apply scale_neg_one_zero.
Qed.

Theorem pure_kernel_conj_right k a w : pure k a -> (mul k w a = zero k <-> mul k a (conjugate k w) = zero k).
Proof.
  intro P. rewrite (pure_kernel_conj k a (conjugate k w) P), conj_conj. reflexivity.
Qed.

(** When 2 = 0 conjugation is the identity, so the anti-automorphism law
    reads x y = y x. *)

Lemma two_zero_conj k x : two = D.zero -> conjugate k x = x.
Proof.
  intro H. rewrite conj_split. apply ext. intros i _. autorewrite with cring_coord.
  transitivity (D.sub (coord k x i) (D.mul two (D.sub (coord k x i) (D.mul (re k x) (coord k (one k) i))))).
  - dring.
  - rewrite H. ring.
Qed.

Theorem two_zero_commutative k x y : two = D.zero -> mul k x y = mul k y x.
Proof.
  intro H. rewrite <- (two_zero_conj k (mul k x y) H), conj_mul, !(two_zero_conj k _ H). reflexivity.
Qed.

(** Levels 0 and 1 are commutative over every commutative ring. *)

Lemma level_one_commutative (x y : cd 1) : mul 1 x y = mul 1 y x.
Proof.
  destruct x as [a b], y as [c d]. cbv [mul add scale conjugate fst snd neg_one]. f_equal; ring.
Qed.

(** The reflection of level k + 1 that negates the second half. *)

Definition reflect k (x : cd (S k)) : cd (S k) := (fst x, scale k neg_one (snd x)).

Theorem reflect_mul k x y : reflect k (mul (S k) x y) = mul (S k) (reflect k x) (reflect k y).
Proof.
  destruct x as [a b], y as [c d]. unfold reflect. cbn [mul fst snd].
  rewrite ?conj_scale, ?mul_scale_l, ?mul_scale_r. f_equal; vec.
Qed.

Lemma reflect_add k x y : reflect k (add (S k) x y) = add (S k) (reflect k x) (reflect k y).
Proof. destruct x as [a b], y as [c d]. unfold reflect. cbn [add fst snd]. f_equal. vec. Qed.

Lemma reflect_scale k r x : reflect k (scale (S k) r x) = scale (S k) r (reflect k x).
Proof. destruct x as [a b]. unfold reflect. cbn [scale fst snd]. f_equal. vec. Qed.

Lemma reflect_zero k : reflect k (zero (S k)) = zero (S k).
Proof. unfold reflect. cbn [zero fst snd]. rewrite scale_zero. reflexivity. Qed.

Lemma reflect_one k : reflect k (one (S k)) = one (S k).
Proof. unfold reflect. cbn [one fst snd]. rewrite scale_zero. reflexivity. Qed.

Lemma reflect_conj k x : reflect k (conjugate (S k) x) = conjugate (S k) (reflect k x).
Proof. reflexivity. Qed.

Lemma reflect_involutive k x : reflect k (reflect k x) = x.
Proof. destruct x as [a b]. unfold reflect. cbn [fst snd]. rewrite scale_neg_neg. reflexivity. Qed.

Theorem reflect_kernel k x z :
  mul (S k) x z = zero (S k) <-> mul (S k) (reflect k x) (reflect k z) = zero (S k).
Proof.
  split; intro H.
  - rewrite <- reflect_mul, H. apply reflect_zero.
  - rewrite <- (reflect_involutive k (mul (S k) x z)), reflect_mul, H. apply reflect_zero.
Qed.

(** The diagonal extension (a, b) -> (f a, f b) of a map f of level k. When
    f preserves sums, scalars, products and conjugates, so does the
    extension; reflect and every diagonal extension of it are such maps. *)

Definition diag k (f : cd k -> cd k) (x : cd (S k)) : cd (S k) := (f (fst x), f (snd x)).

Section Diagonal.
  Variable k : nat.
  Variable f : cd k -> cd k.
  Hypothesis f_add : forall x y, f (add k x y) = add k (f x) (f y).
  Hypothesis f_scale : forall r x, f (scale k r x) = scale k r (f x).
  Hypothesis f_mul : forall x y, f (mul k x y) = mul k (f x) (f y).
  Hypothesis f_conj : forall x, f (conjugate k x) = conjugate k (f x).

  Lemma diag_add x y : diag k f (add (S k) x y) = add (S k) (diag k f x) (diag k f y).
  Proof. unfold diag. cbn [add fst snd]. rewrite !f_add. reflexivity. Qed.

  Lemma diag_scale r x : diag k f (scale (S k) r x) = scale (S k) r (diag k f x).
  Proof. unfold diag. cbn [scale fst snd]. rewrite !f_scale. reflexivity. Qed.

  Lemma diag_conj x : diag k f (conjugate (S k) x) = conjugate (S k) (diag k f x).
  Proof. unfold diag. cbn [conjugate fst snd]. rewrite f_conj, f_scale. reflexivity. Qed.

  Lemma diag_one : f (one k) = one k -> diag k f (one (S k)) = one (S k).
  Proof.
    intro H. unfold diag. cbn [one fst snd]. rewrite H. f_equal.
    rewrite <- (scale_zero k D.zero) at 1. rewrite f_scale. vec.
  Qed.

  Theorem diag_mul x y : diag k f (mul (S k) x y) = mul (S k) (diag k f x) (diag k f y).
  Proof.
    destruct x as [a b], y as [c d]. unfold diag. cbn [mul fst snd].
    rewrite !f_add, !f_scale, !f_mul, !f_conj. reflexivity.
  Qed.
End Diagonal.

Theorem diag_reflect_mul k x y :
  diag (S k) (reflect k) (mul (S (S k)) x y) =
  mul (S (S k)) (diag (S k) (reflect k) x) (diag (S k) (reflect k) y).
Proof.
  apply diag_mul;
    [apply reflect_add | intros; apply reflect_scale | apply reflect_mul | intros; apply reflect_conj].
Qed.

(** The subalgebra embedding x -> (x, 0), iterated k times from level j. *)

Fixpoint lift (j k : nat) : cd j -> cd (k + j) :=
  match k as n return cd j -> cd (n + j) with
  | O => fun x => x
  | S n => fun x => (lift j n x, zero (n + j))
  end.

Lemma embed_mul j (a c : cd j) : mul (S j) (a, zero j) (c, zero j) = (mul j a c, zero j).
Proof. cbn [mul fst snd]. rewrite conj_zero, !mul_zero_l. f_equal; vec. Qed.

Lemma lift_mul j k x y : mul (k + j) (lift j k x) (lift j k y) = lift j k (mul j x y).
Proof.
  induction k as [|n IH]; [reflexivity |].
  cbn [lift Nat.add]. rewrite embed_mul, IH. reflexivity.
Qed.

Lemma lift_zero j k : lift j k (zero j) = zero (k + j).
Proof. induction k as [|n IH]; [reflexivity |]. cbn [lift Nat.add zero]. rewrite IH. reflexivity. Qed.

Lemma lift_zero_inv j k x : lift j k x = zero (k + j) -> x = zero j.
Proof.
  induction k as [|n IH]; intro H; [exact H |].
  apply IH. exact (f_equal fst H).
Qed.

Lemma lift_scale j k r x : scale (k + j) r (lift j k x) = lift j k (scale j r x).
Proof.
  induction k as [|n IH]; [reflexivity |].
  cbn [lift Nat.add scale fst snd]. rewrite IH, scale_zero. reflexivity.
Qed.

Lemma lift_conj j k x : conjugate (k + j) (lift j k x) = lift j k (conjugate j x).
Proof.
  induction k as [|n IH]; [reflexivity |].
  cbn [lift Nat.add conjugate fst snd]. rewrite IH, scale_zero. reflexivity.
Qed.

Lemma lift_pure j k x : pure j x -> pure (k + j) (lift j k x).
Proof. unfold pure. intro P. rewrite lift_conj, P, lift_scale. reflexivity. Qed.

End RingTower.

(** A commutative ring with a square root of -1. *)

Module Type CommutativeRingWithI.
  Include CommutativeRing.
  Parameter i : t.
  Axiom i_squared : mul i i = opp one.
End CommutativeRingWithI.

Module RingTowerI (D : CommutativeRingWithI).
Module T := RingTower D.
Add Ring commutative_ring_with_i : D.ring_th.

(** With ((x0, x1), (x2, x3)) = x0 + x1 e_1 + x2 e_2 + x3 e_3: nilpotent2
    is e_1 + i e_2 and witness2 is the product nilpotent2 e_1 = -1 - i e_3
    (witness2_product). *)

Definition nilpotent2 : T.cd 2 := ((D.zero, D.one), (D.i, D.zero)).
Definition witness2 : T.cd 2 := ((D.opp D.one, D.zero), (D.zero, D.opp D.i)).

Ltac level2 :=
  cbv [T.mul T.add T.scale T.conjugate T.zero T.pure T.neg_one T.two nilpotent2 witness2 fst snd];
  f_equal; f_equal; ring [D.i_squared].

Lemma nilpotent2_pure : T.pure 2 nilpotent2.
Proof. level2. Qed.

Lemma nilpotent2_square : T.mul 2 nilpotent2 nilpotent2 = T.zero 2.
Proof. level2. Qed.

Lemma witness2_product : T.mul 2 nilpotent2 ((D.zero, D.one), (D.zero, D.zero)) = witness2.
Proof. level2. Qed.

Lemma nilpotent2_witness2 : T.mul 2 nilpotent2 witness2 = T.zero 2.
Proof. level2. Qed.

Lemma witness2_nilpotent2 : T.mul 2 witness2 nilpotent2 = T.scale 2 (D.opp T.two) nilpotent2.
Proof. level2. Qed.

(** The pair at level k + 2. *)

Definition nilpotent k : T.cd (k + 2) := T.lift 2 k nilpotent2.
Definition witness k : T.cd (k + 2) := T.lift 2 k witness2.

Lemma nilpotent_pure k : T.pure (k + 2) (nilpotent k).
Proof. apply T.lift_pure, nilpotent2_pure. Qed.

Theorem nilpotent_witness k : T.mul (k + 2) (nilpotent k) (witness k) = T.zero (k + 2).
Proof. unfold nilpotent, witness. rewrite T.lift_mul, nilpotent2_witness2. apply T.lift_zero. Qed.

Theorem witness_nilpotent k :
  T.mul (k + 2) (witness k) (nilpotent k) = T.scale (k + 2) (D.opp T.two) (nilpotent k).
Proof. unfold nilpotent, witness. rewrite T.lift_mul, witness2_nilpotent2, T.lift_scale. reflexivity. Qed.

Lemma witness_nilpotent_zero k : T.mul (k + 2) (witness k) (nilpotent k) = T.zero (k + 2) -> T.two = D.zero.
Proof.
  unfold nilpotent, witness. rewrite T.lift_mul, witness2_nilpotent2. intro H.
  pose proof (f_equal (fun v : T.cd 2 => snd (fst v)) (T.lift_zero_inv 2 k _ H)) as E.
  cbv [T.scale T.zero nilpotent2 fst snd] in E.
  transitivity (D.opp (D.mul (D.opp T.two) D.one)); [ring | rewrite E; ring].
Qed.

Theorem kernel_swap_witness k :
  T.two <> D.zero ->
  T.pure (k + 2) (nilpotent k) /\
  T.mul (k + 2) (nilpotent k) (witness k) = T.zero (k + 2) /\
  T.mul (k + 2) (witness k) (nilpotent k) <> T.zero (k + 2).
Proof.
  intro N. split; [apply nilpotent_pure | split; [apply nilpotent_witness |]].
  intro H. exact (N (witness_nilpotent_zero k H)).
Qed.

Theorem pure_kernel_swap_two_zero k :
  (forall a z, T.pure (k + 2) a -> T.mul (k + 2) a z = T.zero (k + 2) -> T.mul (k + 2) z a = T.zero (k + 2)) ->
  T.two = D.zero.
Proof.
  intro S. exact (witness_nilpotent_zero k (S _ _ (nilpotent_pure k) (nilpotent_witness k))).
Qed.

Theorem kernel_swap_iff_two_zero k :
  (forall a z, T.mul (k + 2) a z = T.zero (k + 2) -> T.mul (k + 2) z a = T.zero (k + 2)) <-> T.two = D.zero.
Proof.
  split.
  - intro S. apply (pure_kernel_swap_two_zero k). intros a z _. apply S.
  - intros H a z E. rewrite (T.two_zero_commutative (k + 2) z a H). exact E.
Qed.

End RingTowerI.

(** The Gaussian integers Z[i] as pairs (re, im). *)

Module GaussianIntegers <: CommutativeRingWithI.
  Definition t := (Z * Z)%type.
  Definition zero : t := (0, 0)%Z.
  Definition one : t := (1, 0)%Z.
  Definition add (x y : t) : t := (fst x + fst y, snd x + snd y)%Z.
  Definition mul (x y : t) : t := (fst x * fst y - snd x * snd y, fst x * snd y + snd x * fst y)%Z.
  Definition sub (x y : t) : t := (fst x - fst y, snd x - snd y)%Z.
  Definition opp (x : t) : t := (- fst x, - snd x)%Z.
  Lemma ring_th : ring_theory zero one add mul sub opp (@eq t).
  Proof.
    constructor; intros; repeat match goal with x : t |- _ => destruct x end;
      unfold zero, one, add, mul, sub, opp; cbn [fst snd]; f_equal; ring.
  Qed.
  Definition i : t := (0, 1)%Z.
  Lemma i_squared : mul i i = opp one.
  Proof. reflexivity. Qed.
End GaussianIntegers.

Module GaussianTower := RingTowerI GaussianIntegers.

Lemma gaussian_two_nonzero : GaussianTower.T.two <> GaussianIntegers.zero.
Proof. discriminate. Qed.

Theorem gaussian_kernel_swap_fails k :
  ~ (forall a z, GaussianTower.T.pure (k + 2) a ->
       GaussianTower.T.mul (k + 2) a z = GaussianTower.T.zero (k + 2) ->
       GaussianTower.T.mul (k + 2) z a = GaussianTower.T.zero (k + 2)).
Proof. intro S. exact (gaussian_two_nonzero (GaussianTower.pure_kernel_swap_two_zero k S)). Qed.

(** Zmod 5, where 2 2 = -1. *)

Module Mod5Tower := RingTowerI CdTwistedProduct.Zmod5.

Lemma mod5_two_nonzero : Mod5Tower.T.two <> CdTwistedProduct.Zmod5.zero.
Proof. intro H. apply (f_equal (@Zmod.to_Z 5)) in H. vm_compute in H. discriminate. Qed.

Theorem mod5_kernel_swap_fails k :
  ~ (forall a z, Mod5Tower.T.pure (k + 2) a ->
       Mod5Tower.T.mul (k + 2) a z = Mod5Tower.T.zero (k + 2) ->
       Mod5Tower.T.mul (k + 2) z a = Mod5Tower.T.zero (k + 2)).
Proof. intro S. exact (mod5_two_nonzero (Mod5Tower.pure_kernel_swap_two_zero k S)). Qed.
