(** Left and right annihilators coincide in the real pair tower of
    CdTowerReal.v at every level k: a z = 0 exactly when z a = 0 for every
    pair of elements with real coordinates, so a b = 1 forces b a = 1 and
    every right inverse of a nonzero a is conj(a)/<a, a> + w with a w = 0.

    The route is Lemma 9.2 and Corollary 9.3 of Biss, Dugger and Isaksen,
    Large annihilators in Cayley-Dickson algebras: x y = 0, conj(x) y = 0 and
    x conj(y) = 0 are equivalent, because the norm of conj(x) y is
    <y, x (conj(x) y)> by the adjoint identity of Lemma 3.4 and
    x (conj(x) y) = conj(x) (x y) for every x and y. That identity, which
    the paper calls a straightforward calculation, is bilinearity once
    conj(x) = 2 re(x) 1 - x: both sides read 2 re(x) (x y) - x (x y). The
    mirror identity (x y) conj(y) = (x conj(y)) y is the same reflection on
    the right. Corollary 9.3 then conjugates x y = 0 to conj(y) conj(x) = 0
    and applies the equivalences twice; the purity of annihilators (Lemmas
    9.4 and 9.5) and Lemmas 2.6 and 2.8 on the real parts of commutators and
    associators follow from the same adjoint identities. CdAnnihilatorSymmetry.v
    proves the integer-tower statement by the trace-form route of
    docs/notes/topics/cd-one-sided-inverses.md; here the real coefficients
    admit division, so the right-inverse family is stated in the note's
    affine form.

    No step uses associativity, alternativity or multiplicativity of the
    norm, which fail from k = 4 on. *)

From Stdlib Require Import Reals Lia Lra.
Require Import CdTowerReal.
Open Scope R_scope.

(** Lemma 2 of the note (Lemma 3.6 of the paper): x conj(x) = conj(x) x =
    <x, x> 1. The doubling step cancels the mixed terms -x2 x1 + x2 x1 and
    collects <x1, x1> + <x2, x2>. *)

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

(** Lemma 3 of the note (Lemma 3.4 of the paper): L_x has adjoint L_conj(x)
    and R_y has adjoint R_conj(y). *)

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

(** Lemmas 2.6 and 2.8 of the paper: the real part of a product is
    <x y, 1>, and the adjoints move each factor to the other side, so the
    real part ignores the order of two factors and the bracketing of three. *)

Theorem re_commutator k x y : re k (mul k x y) = re k (mul k y x).
Proof.
  rewrite <- !dot_one_r, adjoint_l, (adjoint_r k y x (one k)), mul_one_r, mul_one_l. reflexivity.
Qed.

Theorem re_associator k x y z : re k (mul k (mul k x y) z) = re k (mul k x (mul k y z)).
Proof.
  rewrite <- !dot_one_r, (adjoint_r k (mul k x y) z (one k)), (adjoint_r k x y), (adjoint_r k x (mul k y z) (one k)),
    !mul_one_l, conj_mul. reflexivity.
Qed.

(** The identity of Lemma 9.2, x (conj(x) y) = conj(x) (x y), and its mirror
    (x y) conj(y) = (x conj(y)) y: conj(x) = 2 re(x) 1 - x turns each side
    into 2 re(x) (x y) - x (x y). *)

Theorem conj_mul_left k x y : mul k x (mul k (conjugate k x) y) = mul k (conjugate k x) (mul k x y).
Proof. rewrite (conj_split k x). autorewrite with alg. reflexivity. Qed.

Theorem conj_mul_right k x y : mul k (mul k x y) (conjugate k y) = mul k (mul k x (conjugate k y)) y.
Proof. rewrite (conj_split k y). autorewrite with alg. reflexivity. Qed.

(** Lemma 9.2: x y = 0, conj(x) y = 0 and x conj(y) = 0 are equivalent. The
    norm of conj(x) y is <y, x (conj(x) y)> = <y, conj(x) (x y)>, which x y = 0
    annihilates; the converse substitutes conj(x) for x. *)

Lemma conj_left_zero k x y : mul k x y = zero k -> mul k (conjugate k x) y = zero k.
Proof.
  intro H. apply dot_self_zero.
  rewrite adjoint_l, conj_conj, conj_mul_left, H, mul_zero_r. apply dot_zero_r.
Qed.

Lemma conj_right_zero k x y : mul k x y = zero k -> mul k x (conjugate k y) = zero k.
Proof.
  intro H. apply dot_self_zero.
  rewrite adjoint_r, conj_conj, <- conj_mul_right, H, mul_zero_l. apply dot_zero_r.
Qed.

Theorem lemma_9_2 k x y :
  (mul k x y = zero k <-> mul k (conjugate k x) y = zero k) /\
  (mul k x y = zero k <-> mul k x (conjugate k y) = zero k).
Proof.
  split; split; intro H.
  - apply conj_left_zero, H.
  - rewrite <- (conj_conj k x). apply conj_left_zero, H.
  - apply conj_right_zero, H.
  - rewrite <- (conj_conj k y). apply conj_right_zero, H.
Qed.

(** Corollary 9.3: a z = 0 implies z a = 0. Conjugation gives
    conj(z) conj(a) = 0, the first equivalence removes the conjugation of z
    and the second removes that of a. *)

Theorem kernel_swap k a z : mul k a z = zero k -> mul k z a = zero k.
Proof.
  intro H.
  pose proof (f_equal (conjugate k) H) as C. rewrite conj_mul, conj_zero in C.
  apply conj_left_zero in C. rewrite conj_conj in C.
  apply conj_right_zero in C. rewrite conj_conj in C. exact C.
Qed.

Theorem kernel_equality k a z : mul k a z = zero k <-> mul k z a = zero k.
Proof. split; apply kernel_swap. Qed.

(** Lemma 9.4 (Lemma 4 of the note): a z = 0 with a and z nonzero makes both
    pure. a z = 0 and conj(a) z = 0 give (a + conj(a)) z = 2 re(a) z = 0, so
    re(a) = 0 since z is nonzero; the kernel swap gives the same for z. *)

Lemma scale_zero_factor k r x : scale k r x = zero k -> x <> zero k -> r = 0.
Proof.
  intros H Hx. destruct (Req_dec r 0) as [E|E]; [exact E | exfalso]. apply Hx. apply ext. intros i _.
  pose proof (f_equal (fun v => coord k v i) H) as Hi. cbn beta in Hi.
  rewrite coord_scale, coord_zero in Hi. rewrite coord_zero.
  destruct (Rmult_integral _ _ Hi) as [Z|Z]; [contradiction | exact Z].
Qed.

Lemma re_left_zero k a z : mul k a z = zero k -> z <> zero k -> re k a = 0.
Proof.
  intros H Hz.
  pose proof (conj_left_zero k a z H) as C.
  assert (S : scale k (2 * re k a) z = zero k).
  { rewrite <- (mul_one_l k z), <- mul_scale_l, <- add_conj, mul_add_l, H, C. vec. }
  pose proof (scale_zero_factor k _ _ S Hz). lra.
Qed.

Theorem purity_left k a z :
  mul k a z = zero k -> a <> zero k -> z <> zero k -> re k a = 0 /\ re k z = 0.
Proof.
  intros H Ha Hz. split.
  - exact (re_left_zero k a z H Hz).
  - exact (re_left_zero k z a (kernel_swap k a z H) Ha).
Qed.

Theorem purity_right k a z :
  mul k z a = zero k -> a <> zero k -> z <> zero k -> re k a = 0 /\ re k z = 0.
Proof. intros H. apply purity_left, kernel_swap, H. Qed.

(** The corollary: direct finiteness, and the right inverses of a as the
    affine family conj(a)/<a, a> + w with a w = 0. *)

Lemma dot_self_pos k a : a <> zero k -> 0 < dot k a a.
Proof.
  intro Ha. pose proof (dot_self_nonneg k a).
  destruct (Rle_lt_or_eq_dec _ _ H) as [L|E]; [exact L | exfalso]. apply Ha, dot_self_zero. lra.
Qed.

Lemma one_nonzero k : one k <> zero k.
Proof. intro E. pose proof (f_equal (re k) E) as R. rewrite re_one, re_zero in R. lra. Qed.

Lemma right_inverse_nonzero k a b : mul k a b = one k -> a <> zero k.
Proof. intros H E. rewrite E, mul_zero_l in H. exact (one_nonzero k (eq_sym H)). Qed.

Theorem right_inverse_affine k a b :
  mul k a b = one k ->
  mul k a (add k b (scale k (-1) (scale k (/ dot k a a) (conjugate k a)))) = zero k.
Proof.
  intro H. pose proof (dot_self_pos k a (right_inverse_nonzero k a b H)) as P.
  rewrite mul_add_r, !mul_scale_r, H, norm_mul_r. apply ext. intros i _.
  autorewrite with coord. field. lra.
Qed.

Theorem right_inverse_form k a b :
  mul k a b = one k ->
  exists w, mul k a w = zero k /\ b = add k (scale k (/ dot k a a) (conjugate k a)) w.
Proof.
  intro H.
  exists (add k b (scale k (-1) (scale k (/ dot k a a) (conjugate k a)))).
  split; [exact (right_inverse_affine k a b H) | vec].
Qed.

Theorem direct_finiteness k a b : mul k a b = one k -> mul k b a = one k.
Proof.
  intro H. pose proof (dot_self_pos k a (right_inverse_nonzero k a b H)) as P.
  pose proof (kernel_swap k _ _ (right_inverse_affine k a b H)) as W.
  rewrite mul_add_l, !mul_scale_l, norm_mul_l in W.
  apply ext. intros i _.
  pose proof (f_equal (fun v => coord k v i) W) as Wi. cbn beta in Wi.
  autorewrite with coord in Wi.
  replace (/ dot k a a * (dot k a a * coord k (one k) i)) with (coord k (one k) i) in Wi by (field; lra).
  lra.
Qed.
