(** Left and right annihilators coincide in the integer pair tower of
    CdImaginarySumConference.v at every level k: a z = 0 exactly when z a = 0,
    so a b = 1 forces b a = 1 (direct finiteness) and every right inverse b of
    a satisfies <a, a> b = conj(a) + w with a w = 0.

    The mechanism is the purity of annihilators, Lemmas 9.4 and 9.5 of Biss,
    Dugger and Isaksen, Large annihilators in Cayley-Dickson algebras, whose
    Corollary 9.3 is the kernel equality. The proof here follows
    docs/notes/topics/cd-one-sided-inverses.md: the norm law
    x conj(x) = conj(x) x = <x, x> 1 (its Lemma 2), the trace-form adjoint
    identities <x y, z> = <y, conj(x) z> = <x, z conj(y)> (its Lemma 3, the
    paper's Lemma 3.4), and the two products <a z, z> = <z, z> re(a) and
    <a z, a> = <a, a> re(z) that make a and z pure whenever a z = 0 with both
    nonzero (its Lemma 4). Pure elements satisfy conj(x) = -x, so a z = 0
    gives z a = (-z)(-a) = conj(z) conj(a) = conj(a z) = 0. No step uses
    associativity, alternativity or multiplicativity of the norm, and no step
    divides: each cancellation is of a nonzero integer factor <x, x>, which is
    a sum of squares and vanishes only at x = 0. *)

From Stdlib Require Import ZArith Lia.
Require Import CdImaginarySumConference.
Open Scope Z_scope.

(** The trace form is symmetric, vanishes against zero, and reads the real
    part against one. *)

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
  - rewrite !IH. reflexivity.
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

(** <x, x> is a sum of squares: nonnegative, and zero only at x = 0. *)

Lemma dot_self_nonneg k : forall x, 0 <= dot k x x.
Proof.
  induction k as [|j IH]; intro x; simpl.
  - nia.
  - pose proof (IH (fst x)). pose proof (IH (snd x)). lia.
Qed.

Lemma dot_self_zero k : forall x, dot k x x = 0 -> x = zero k.
Proof.
  induction k as [|j IH]; intros x H; simpl in *.
  - nia.
  - destruct x as [x1 x2]. simpl in H.
    pose proof (dot_self_nonneg j x1). pose proof (dot_self_nonneg j x2).
    rewrite (IH x1), (IH x2); [reflexivity | lia | lia].
Qed.

(** Lemma 2 of the note: x conj(x) = conj(x) x = <x, x> 1. The doubling step
    cancels the mixed terms -x2 x1 + x2 x1 and collects <x1, x1> + <x2, x2>. *)

Theorem norm_mul k :
  (forall x, mul k x (conjugate k x) = scale k (dot k x x) (one k)) /\
  (forall x, mul k (conjugate k x) x = scale k (dot k x x) (one k)).
Proof.
  induction k as [|j IH]; simpl.
  - split; intro x; ring.
  - destruct IH as [NR NL].
    split; intros [x1 x2]; cbn [mul conjugate dot scale add fst snd one zero];
      autorewrite with alg; rewrite ?NR, ?NL; f_equal; vec.
Qed.

Lemma norm_mul_r k x : mul k x (conjugate k x) = scale k (dot k x x) (one k).
Proof. apply norm_mul. Qed.
Lemma norm_mul_l k x : mul k (conjugate k x) x = scale k (dot k x x) (one k).
Proof. apply norm_mul. Qed.

(** Lemma 3 of the note: L_x has adjoint L_conj(x) and R_y has adjoint
    R_conj(y). The doubling step matches the four terms of each side through
    the level-j identities in the order the note lists them. *)

Theorem adjoint k :
  (forall x y z, dot k (mul k x y) z = dot k y (mul k (conjugate k x) z)) /\
  (forall x y z, dot k (mul k x y) z = dot k x (mul k z (conjugate k y))).
Proof.
  induction k as [|j IH]; simpl.
  - split; intros; ring.
  - destruct IH as [AL AR].
    split; intros [x1 x2] [y1 y2] [z1 z2]; cbn [mul conjugate dot scale add fst snd];
      autorewrite with alg dotlin.
    + rewrite (AL x1 y1 z1), (AL (conjugate j y2) x2 z1), (AR y2 x1 z2), (AR x2 (conjugate j y1) z2).
      rewrite (dot_comm j y2 (mul j x2 (conjugate j z1))), (AR x2 (conjugate j z1) y2).
      rewrite (dot_comm j y1 (mul j (conjugate j z2) x2)), (AL (conjugate j z2) x2 y1).
      rewrite !conj_conj. ring.
    + rewrite (AR x1 y1 z1), (AL (conjugate j y2) x2 z1), (AL y2 x1 z2), (AR x2 (conjugate j y1) z2).
      rewrite !conj_conj. ring.
Qed.

Lemma adjoint_l k x y z : dot k (mul k x y) z = dot k y (mul k (conjugate k x) z).
Proof. apply adjoint. Qed.
Lemma adjoint_r k x y z : dot k (mul k x y) z = dot k x (mul k z (conjugate k y)).
Proof. apply adjoint. Qed.

(** The two products behind Lemma 4: <a z, z> = <z, z> re(a) and
    <a z, a> = <a, a> re(z). *)

Lemma dot_mul_self_r k a z : dot k (mul k a z) z = dot k z z * re k a.
Proof. rewrite adjoint_r, norm_mul_r, dot_scale_r, dot_one_r. ring. Qed.

Lemma dot_mul_self_l k a z : dot k (mul k a z) a = dot k a a * re k z.
Proof. rewrite adjoint_l, norm_mul_l, dot_scale_r, dot_one_r. ring. Qed.

(** Lemma 4 of the note (Lemmas 9.4 and 9.5 of the paper): a z = 0 with a and
    z nonzero makes both pure, and the same holds for z a = 0. *)

Theorem purity_left k a z :
  mul k a z = zero k -> a <> zero k -> z <> zero k -> re k a = 0 /\ re k z = 0.
Proof.
  intros H Ha Hz.
  pose proof (dot_mul_self_r k a z) as Pz. pose proof (dot_mul_self_l k a z) as Pa.
  rewrite H, dot_zero_l in Pz, Pa.
  split.
  - destruct (proj1 (Z.mul_eq_0 _ _) (eq_sym Pz)) as [N|R]; [exfalso; apply Hz, dot_self_zero, N | exact R].
  - destruct (proj1 (Z.mul_eq_0 _ _) (eq_sym Pa)) as [N|R]; [exfalso; apply Ha, dot_self_zero, N | exact R].
Qed.

(** A pure element is its own negative under conjugation. *)

Lemma conj_pure k x : re k x = 0 -> conjugate k x = scale k (-1) x.
Proof. intro H. rewrite conj_split, H. vec. Qed.

(** The theorem: a z = 0 implies z a = 0. The zero cases of a and z are
    decided through <x, x> = 0, and the remaining case conjugates a z = 0
    with both factors pure. *)

Theorem kernel_swap k a z : mul k a z = zero k -> mul k z a = zero k.
Proof.
  intro H.
  destruct (Z.eq_dec (dot k a a) 0) as [Na|Na].
  { rewrite (dot_self_zero k a Na). apply mul_zero. }
  destruct (Z.eq_dec (dot k z z) 0) as [Nz|Nz].
  { rewrite (dot_self_zero k z Nz). apply mul_zero. }
  assert (Ha : a <> zero k) by (intro E; apply Na; rewrite E; apply dot_zero_l).
  assert (Hz : z <> zero k) by (intro E; apply Nz; rewrite E; apply dot_zero_l).
  destruct (purity_left k a z H Ha Hz) as [Ra Rz].
  pose proof (conj_mul k a z) as C.
  rewrite H, conj_zero, (conj_pure k a Ra), (conj_pure k z Rz), mul_scale_l, mul_scale_r in C.
  apply ext. intros i _.
  pose proof (f_equal (fun v => coord k v i) C) as Ci. cbn beta in Ci.
  autorewrite with coord in Ci. rewrite coord_zero. lia.
Qed.

Theorem kernel_equality k a z : mul k a z = zero k <-> mul k z a = zero k.
Proof. split; apply kernel_swap. Qed.

Theorem purity_right k a z :
  mul k z a = zero k -> a <> zero k -> z <> zero k -> re k a = 0 /\ re k z = 0.
Proof. intros H. apply purity_left, kernel_swap, H. Qed.

(** The corollary: direct finiteness, and the right inverses of a as the
    integer-cleared affine family <a, a> b = conj(a) + w with a w = 0. *)

Theorem right_inverse_affine k a b :
  mul k a b = one k ->
  mul k a (add k (scale k (dot k a a) b) (scale k (-1) (conjugate k a))) = zero k.
Proof.
  intro H. rewrite mul_add_r, !mul_scale_r, H, norm_mul_r. vec.
Qed.

Theorem direct_finiteness k a b : mul k a b = one k -> mul k b a = one k.
Proof.
  intro H.
  assert (Na : dot k a a <> 0).
  { intro N. apply dot_self_zero in N. rewrite N in H. destruct (mul_zero k) as [Z0 _].
    rewrite Z0 in H. pose proof (f_equal (re k) H) as R. rewrite re_zero, re_one in R. discriminate. }
  pose proof (kernel_swap k _ _ (right_inverse_affine k a b H)) as W.
  rewrite mul_add_l, !mul_scale_l, norm_mul_l in W.
  apply ext. intros i _.
  pose proof (f_equal (fun v => coord k v i) W) as Wi. cbn beta in Wi.
  autorewrite with coord in Wi.
  apply (proj1 (Z.mul_cancel_l _ _ _ Na)). lia.
Qed.
