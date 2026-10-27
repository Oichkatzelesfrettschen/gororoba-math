(** The Cayley-Dickson pair tower over an abstract ordered coefficient
    domain, as one functor. CdImaginarySumConference.v states the tower over
    the integers and CdTowerReal.v over the Stdlib reals, with the same
    doubling (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)) that
    gororoba_quantum/cd_core.py cd_sign reads, and CdAnnihilatorSymmetry.v
    and CdAnnihilatorSymmetryReal.v prove the annihilator theorems on each.
    Every vector identity of those files closes with coordinate
    extensionality and the ring tactic, the order enters only through
    squares being nonnegative and a sum of nonnegative terms vanishing
    termwise, and cancellation enters only through the absence of zero
    divisors. OrderedDomain names exactly those facts: a commutative ring
    with a relation le such that 0 <= a a, nonnegative terms add to a
    nonnegative sum, a vanishing sum of nonnegative terms vanishes termwise,
    a b = 0 forces a factor to vanish, and 1 differs from 0. The functor
    CdTower proves, for every level, the linear laws, the norm law (Lemma
    3.6 of Biss, Dugger and Isaksen, math/0511691), the adjoints (Lemma
    3.4), Lemmas 2.6 and 2.8 on real parts, Corollary 2.9 (flexibility),
    Lemma 9.2 with its identity, Corollary 9.3 (ker L_a = ker R_a), Lemma
    9.4 (purity), Lemma 9.5 (orthogonality to the adjoined unit) and direct
    finiteness with the integer-cleared inverse family
    <a, a> b = conj(a) + w. The affine family conj(a)/<a, a> + w needs
    division and stays in CdAnnihilatorSymmetryReal.v.

    ZDomain and RDomain prove the signature from Stdlib (Zth and RTheory
    for the ring laws, Z.square_nonneg, Zmult_integral, Rmult_le_pos,
    Rplus_eq_0_l and Rmult_integral for the order and cancellation), and
    ZTower and RTower are the two instances. The bridge lemmas at the end
    identify each instance's operations with the ones of the integer and
    real files, so every theorem of the functor restates the corresponding
    theorem of those files in its own vocabulary: the real statements rest
    on the two Stdlib real-construction axioms, the integer statements on
    none.

    No step uses associativity, alternativity or multiplicativity of the
    norm, which fail from level 4 on, and no proof decides equality on the
    coefficient domain. *)

From Stdlib Require Import Ring Lia ZArith Reals.

Create Rewrite HintDb domain_coord.
Create Rewrite HintDb domain_alg.
Create Rewrite HintDb domain_dotlin.

Module Type OrderedDomain.
  Parameter t : Type.
  Parameter zero one : t.
  Parameter add mul sub : t -> t -> t.
  Parameter opp : t -> t.
  Parameter le : t -> t -> Prop.
  Axiom ring_th : ring_theory zero one add mul sub opp (@eq t).
  Axiom one_neq_zero : one <> zero.
  Axiom sq_nonneg : forall a, le zero (mul a a).
  Axiom add_nonneg : forall a b, le zero a -> le zero b -> le zero (add a b).
  Axiom nonneg_sum_zero : forall a b, le zero a -> le zero b -> add a b = zero -> a = zero.
  Axiom mul_integral : forall a b, mul a b = zero -> a = zero \/ b = zero.
End OrderedDomain.

Module CdTower (D : OrderedDomain).

Add Ring domain_ring : D.ring_th.

Definition two : D.t := D.add D.one D.one.
Definition neg_one : D.t := D.opp D.one.

Ltac dring := try unfold neg_one; try unfold two; ring.

(** Consequences of the signature: 2 and -1 are nonzero, a square vanishes
    only at zero, and a doubled element vanishes only at zero. *)

Lemma two_neq_zero : two <> D.zero.
Proof.
  intro E. apply D.one_neq_zero.
  assert (L : D.le D.zero D.one).
  { replace D.one with (D.mul D.one D.one) by dring. apply D.sq_nonneg. }
  exact (D.nonneg_sum_zero D.one D.one L L E).
Qed.

Lemma neg_one_neq_zero : neg_one <> D.zero.
Proof.
  intro E. apply D.one_neq_zero.
  transitivity (D.opp neg_one); [unfold neg_one; ring | rewrite E; ring].
Qed.

Lemma sq_zero a : D.mul a a = D.zero -> a = D.zero.
Proof. intro H. destruct (D.mul_integral a a H); assumption. Qed.

Lemma double_zero a : D.add a a = D.zero -> a = D.zero.
Proof.
  intro H. destruct (D.mul_integral two a) as [E|E]; [| exfalso; exact (two_neq_zero E) | exact E].
  transitivity (D.add a a); [unfold two; ring | exact H].
Qed.

Lemma nonneg_sum_zero_r a b : D.le D.zero a -> D.le D.zero b -> D.add a b = D.zero -> b = D.zero.
Proof.
  intros La Lb H. apply (D.nonneg_sum_zero b a Lb La). rewrite <- H. dring.
Qed.

(** The tower. *)

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

Fixpoint dot (k : nat) : cd k -> cd k -> D.t :=
  match k as d return cd d -> cd d -> D.t with
  | O => D.mul
  | S j => fun x y => D.add (dot j (fst x) (fst y)) (dot j (snd x) (snd y))
  end.

Fixpoint coord (k : nat) : cd k -> nat -> D.t :=
  match k as d return cd d -> nat -> D.t with
  | O => fun v _ => v
  | S j => fun v i =>
      if Nat.ltb i (Nat.pow 2 j) then coord j (fst v) i else coord j (snd v) (i - Nat.pow 2 j)
  end.

(** Coordinates decide equality, which reduces each vector identity below to
    an identity of linear combinations in the domain. *)

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

Hint Rewrite coord_add coord_scale coord_zero : domain_coord.
Ltac vec := apply ext; intros ? _; autorewrite with domain_coord; dring.

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

Hint Rewrite mul_add_l mul_add_r mul_scale_l mul_scale_r conj_add conj_scale conj_mul conj_conj
  conj_one conj_zero mul_one_l mul_one_r mul_zero_l mul_zero_r : domain_alg.

(** conj(x) = 2 re(x) 1 - x: conjugation is the reflection through the real
    line, which every identity of the form x (conj(x) y) = conj(x) (x y)
    reads as bilinearity. *)

Lemma conj_split k x : conjugate k x = add k (scale k (D.mul two (re k x)) (one k)) (scale k neg_one x).
Proof.
  transitivity (add k (add k x (conjugate k x)) (scale k neg_one x)); [vec | now rewrite add_conj].
Qed.

(** The coordinate inner product: bilinear, symmetric, conjugation-invariant,
    and a sum of squares. *)

Lemma dot_linear k :
  (forall x y z, dot k (add k x y) z = D.add (dot k x z) (dot k y z)) /\
  (forall x y z, dot k z (add k x y) = D.add (dot k z x) (dot k z y)) /\
  (forall r x z, dot k (scale k r x) z = D.mul r (dot k x z)) /\
  (forall r x z, dot k z (scale k r x) = D.mul r (dot k z x)).
Proof.
  induction k as [|j IH]; simpl.
  - repeat split; intros; dring.
  - destruct IH as [Al [Ar [Sl Sr]]].
    repeat split; intros; cbn [dot add scale fst snd]; rewrite ?Al, ?Ar, ?Sl, ?Sr; dring.
Qed.

Lemma dot_add_l k x y z : dot k (add k x y) z = D.add (dot k x z) (dot k y z). Proof. apply dot_linear. Qed.
Lemma dot_add_r k x y z : dot k z (add k x y) = D.add (dot k z x) (dot k z y). Proof. apply dot_linear. Qed.
Lemma dot_scale_l k r x z : dot k (scale k r x) z = D.mul r (dot k x z). Proof. apply dot_linear. Qed.
Lemma dot_scale_r k r x z : dot k z (scale k r x) = D.mul r (dot k z x). Proof. apply dot_linear. Qed.

Lemma dot_conj k : forall x y, dot k (conjugate k x) y = dot k x (conjugate k y).
Proof.
  induction k as [|j IH]; intros x y.
  - reflexivity.
  - destruct x as [x1 x2], y as [y1 y2]. cbn [dot conjugate fst snd].
    rewrite IH, dot_scale_l, dot_scale_r. reflexivity.
Qed.

Hint Rewrite dot_add_l dot_add_r dot_scale_l dot_scale_r : domain_dotlin.

Lemma dot_comm k : forall x y, dot k x y = dot k y x.
Proof.
  induction k as [|j IH]; intros x y; simpl.
  - dring.
  - rewrite (IH (fst x)), (IH (snd x)). reflexivity.
Qed.

Lemma dot_zero_l k : forall x, dot k (zero k) x = D.zero.
Proof.
  induction k as [|j IH]; intro x; simpl.
  - dring.
  - rewrite !IH. dring.
Qed.

Lemma dot_zero_r k : forall x, dot k x (zero k) = D.zero.
Proof. intro x. rewrite dot_comm. apply dot_zero_l. Qed.

Lemma re_zero k : re k (zero k) = D.zero.
Proof. induction k as [|j IH]; simpl; [reflexivity | exact IH]. Qed.

Lemma re_one k : re k (one k) = D.one.
Proof. induction k as [|j IH]; simpl; [reflexivity | exact IH]. Qed.

Lemma dot_one_r k : forall x, dot k x (one k) = re k x.
Proof.
  induction k as [|j IH]; intro x; simpl.
  - dring.
  - rewrite IH, dot_zero_r. dring.
Qed.

Lemma re_add k x y : re k (add k x y) = D.add (re k x) (re k y).
Proof. rewrite <- !dot_one_r. apply dot_add_l. Qed.

Lemma re_scale k r x : re k (scale k r x) = D.mul r (re k x).
Proof. rewrite <- !dot_one_r. apply dot_scale_l. Qed.

Lemma dot_self_nonneg k : forall x, D.le D.zero (dot k x x).
Proof.
  induction k as [|j IH]; intro x; simpl.
  - apply D.sq_nonneg.
  - apply D.add_nonneg; apply IH.
Qed.

Lemma dot_self_zero k : forall x, dot k x x = D.zero -> x = zero k.
Proof.
  induction k as [|j IH]; intros x H; simpl in *.
  - exact (sq_zero x H).
  - destruct x as [x1 x2]. simpl in H.
    pose proof (dot_self_nonneg j x1) as N1. pose proof (dot_self_nonneg j x2) as N2.
    rewrite (IH x1 (D.nonneg_sum_zero _ _ N1 N2 H)), (IH x2 (nonneg_sum_zero_r _ _ N1 N2 H)). reflexivity.
Qed.

(** Lemma 3.6 of the paper: x conj(x) = conj(x) x = <x, x> 1. *)

Theorem norm_mul k :
  (forall x, mul k x (conjugate k x) = scale k (dot k x x) (one k)) /\
  (forall x, mul k (conjugate k x) x = scale k (dot k x x) (one k)).
Proof.
  induction k as [|j IH]; simpl.
  - split; intro x; dring.
  - destruct IH as [NR NL].
    split; intros [x1 x2]; cbn [mul conjugate dot scale add fst snd one zero];
      autorewrite with domain_alg; rewrite ?NR, ?NL; f_equal; vec.
Qed.

Lemma norm_mul_r k x : mul k x (conjugate k x) = scale k (dot k x x) (one k).
Proof. apply norm_mul. Qed.
Lemma norm_mul_l k x : mul k (conjugate k x) x = scale k (dot k x x) (one k).
Proof. apply norm_mul. Qed.

(** Lemma 3.4 of the paper: L_x has adjoint L_conj(x) and R_y has adjoint
    R_conj(y). *)

Theorem adjoint k :
  (forall x y z, dot k (mul k x y) z = dot k y (mul k (conjugate k x) z)) /\
  (forall x y z, dot k (mul k x y) z = dot k x (mul k z (conjugate k y))).
Proof.
  induction k as [|j IH]; simpl.
  - split; intros; dring.
  - destruct IH as [AL AR].
    split; intros [x1 x2] [y1 y2] [z1 z2]; cbn [mul conjugate dot scale add fst snd];
      autorewrite with domain_alg domain_dotlin.
    + rewrite (AL x1 y1 z1), (AL (conjugate j y2) x2 z1), (AR y2 x1 z2), (AR x2 (conjugate j y1) z2).
      rewrite (dot_comm j y2 (mul j x2 (conjugate j z1))), (AR x2 (conjugate j z1) y2).
      rewrite (dot_comm j y1 (mul j (conjugate j z2) x2)), (AL (conjugate j z2) x2 y1).
      rewrite !conj_conj. dring.
    + rewrite (AR x1 y1 z1), (AL (conjugate j y2) x2 z1), (AL y2 x1 z2), (AR x2 (conjugate j y1) z2).
      rewrite !conj_conj. dring.
Qed.

Lemma adjoint_l k x y z : dot k (mul k x y) z = dot k y (mul k (conjugate k x) z).
Proof. apply adjoint. Qed.
Lemma adjoint_r k x y z : dot k (mul k x y) z = dot k x (mul k z (conjugate k y)).
Proof. apply adjoint. Qed.

(** Lemmas 2.6 and 2.8 of the paper: the real part of a product is
    <x y, 1>, and the adjoints move each factor to the other side. *)

Theorem re_commutator k x y : re k (mul k x y) = re k (mul k y x).
Proof.
  rewrite <- !dot_one_r, adjoint_l, (adjoint_r k y x (one k)), mul_one_r, mul_one_l. reflexivity.
Qed.

Theorem re_associator k x y z : re k (mul k (mul k x y) z) = re k (mul k x (mul k y z)).
Proof.
  rewrite <- !dot_one_r, (adjoint_r k (mul k x y) z (one k)), (adjoint_r k x y), (adjoint_r k x (mul k y z) (one k)),
    !mul_one_l, conj_mul. reflexivity.
Qed.

(** Corollary 2.9 (flexibility): the trilinear sum
    x (y z) - (x y) z + z (y x) - (z y) x vanishes at a real argument, so
    conjugating one argument negates it, while the anti-automorphism law
    conjugates it to minus the sum of the conjugates; it is therefore its own
    conjugate, a real element whose real part Lemma 2.8 cancels. *)

Definition flex_sum k x y z : cd k :=
  add k (add k (mul k x (mul k y z)) (scale k neg_one (mul k (mul k x y) z)))
        (add k (mul k z (mul k y x)) (scale k neg_one (mul k (mul k z y) x))).

Lemma flex_sum_conj_l k x y z : flex_sum k (conjugate k x) y z = scale k neg_one (flex_sum k x y z).
Proof. unfold flex_sum. rewrite (conj_split k x). autorewrite with domain_alg. vec. Qed.

Lemma flex_sum_conj_m k x y z : flex_sum k x (conjugate k y) z = scale k neg_one (flex_sum k x y z).
Proof. unfold flex_sum. rewrite (conj_split k y). autorewrite with domain_alg. vec. Qed.

Lemma flex_sum_conj_r k x y z : flex_sum k x y (conjugate k z) = scale k neg_one (flex_sum k x y z).
Proof. unfold flex_sum. rewrite (conj_split k z). autorewrite with domain_alg. vec. Qed.

Lemma conj_flex_sum k x y z :
  conjugate k (flex_sum k x y z) = scale k neg_one (flex_sum k (conjugate k x) (conjugate k y) (conjugate k z)).
Proof. unfold flex_sum. autorewrite with domain_alg. vec. Qed.

Lemma flex_sum_self_conj k x y z : conjugate k (flex_sum k x y z) = flex_sum k x y z.
Proof. rewrite conj_flex_sum, flex_sum_conj_l, flex_sum_conj_m, flex_sum_conj_r. vec. Qed.

Lemma re_flex_sum k x y z : re k (flex_sum k x y z) = D.zero.
Proof.
  unfold flex_sum. rewrite !re_add, !re_scale, (re_associator k x y z), (re_associator k z y x). unfold neg_one. dring.
Qed.

Theorem flex_sum_zero k x y z : flex_sum k x y z = zero k.
Proof.
  pose proof (add_conj k (flex_sum k x y z)) as H.
  rewrite flex_sum_self_conj, re_flex_sum in H.
  apply ext. intros i _. pose proof (f_equal (fun v => coord k v i) H) as Hi. cbn beta in Hi.
  autorewrite with domain_coord in Hi. rewrite coord_zero. apply double_zero. rewrite Hi. dring.
Qed.

Theorem flexible k x y : mul k (mul k x y) x = mul k x (mul k y x).
Proof.
  pose proof (flex_sum_zero k x y x) as H. unfold flex_sum in H.
  apply ext. intros i _. pose proof (f_equal (fun v => coord k v i) H) as Hi. cbn beta in Hi.
  autorewrite with domain_coord in Hi.
  assert (E : D.sub (coord k (mul k x (mul k y x)) i) (coord k (mul k (mul k x y) x) i) = D.zero).
  { apply double_zero. rewrite <- Hi. dring. }
  transitivity (D.sub (coord k (mul k x (mul k y x)) i)
                      (D.sub (coord k (mul k x (mul k y x)) i) (coord k (mul k (mul k x y) x) i)));
    [ring | rewrite E; ring].
Qed.

(** The identity of Lemma 9.2, x (conj(x) y) = conj(x) (x y), and its mirror. *)

Theorem conj_mul_left k x y : mul k x (mul k (conjugate k x) y) = mul k (conjugate k x) (mul k x y).
Proof. rewrite (conj_split k x). autorewrite with domain_alg. reflexivity. Qed.

Theorem conj_mul_right k x y : mul k (mul k x y) (conjugate k y) = mul k (mul k x (conjugate k y)) y.
Proof. rewrite (conj_split k y). autorewrite with domain_alg. reflexivity. Qed.

(** Lemma 9.2: x y = 0, conj(x) y = 0 and x conj(y) = 0 are equivalent. *)

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

(** Corollary 9.3: a z = 0 exactly when z a = 0. *)

Theorem kernel_swap k a z : mul k a z = zero k -> mul k z a = zero k.
Proof.
  intro H.
  pose proof (f_equal (conjugate k) H) as C. rewrite conj_mul, conj_zero in C.
  apply conj_left_zero in C. rewrite conj_conj in C.
  apply conj_right_zero in C. rewrite conj_conj in C. exact C.
Qed.

Theorem kernel_equality k a z : mul k a z = zero k <-> mul k z a = zero k.
Proof. split; apply kernel_swap. Qed.

(** Lemma 9.4: a z = 0 with a and z nonzero makes both pure. The scalar
    factor of a vanishing multiple of a nonzero vector vanishes, because the
    norm of r x is r r <x, x> and the domain has no zero divisors. *)

Lemma scale_zero_factor k r x : scale k r x = zero k -> x <> zero k -> r = D.zero.
Proof.
  intros H Hx. pose proof (f_equal (fun v => dot k v v) H) as N. cbn beta in N.
  rewrite dot_scale_l, dot_scale_r, dot_zero_l in N.
  destruct (D.mul_integral _ _ N) as [E|E]; [exact E |].
  destruct (D.mul_integral _ _ E) as [E'|E']; [exact E' | exfalso; exact (Hx (dot_self_zero k x E'))].
Qed.

Lemma re_left_zero k a z : mul k a z = zero k -> z <> zero k -> re k a = D.zero.
Proof.
  intros H Hz.
  pose proof (conj_left_zero k a z H) as C.
  assert (S : scale k (D.mul two (re k a)) z = zero k).
  { rewrite <- (mul_one_l k z), <- mul_scale_l, <- add_conj, mul_add_l, H, C. vec. }
  destruct (D.mul_integral _ _ (scale_zero_factor k _ _ S Hz)) as [E|E]; [exfalso; exact (two_neq_zero E) | exact E].
Qed.

Theorem purity_left k a z :
  mul k a z = zero k -> a <> zero k -> z <> zero k -> re k a = D.zero /\ re k z = D.zero.
Proof.
  intros H Ha Hz. split.
  - exact (re_left_zero k a z H Hz).
  - exact (re_left_zero k z a (kernel_swap k a z H) Ha).
Qed.

Theorem purity_right k a z :
  mul k z a = zero k -> a <> zero k -> z <> zero k -> re k a = D.zero /\ re k z = D.zero.
Proof. intros H. apply purity_left, kernel_swap, H. Qed.

(** Lemma 9.5: a zero divisor of level k + 1 is orthogonal to span(1, i),
    with i = (0, 1) the adjoined unit, because (a, b)(c, d) = 0 with a pure
    gives (-conj(d), c)(b, a) = 0 and Lemma 9.4 makes b pure. *)

Definition i_unit k : cd (S k) := (zero k, one k).

Lemma dot_i_unit k (x : cd (S k)) : dot (S k) x (i_unit k) = re k (snd x).
Proof. destruct x as [a b]. cbn [dot i_unit fst snd]. rewrite dot_zero_r, dot_one_r. dring. Qed.

Lemma imaginary_conj k a : re k a = D.zero -> conjugate k a = scale k neg_one a.
Proof. intro Ha. rewrite conj_split, Ha. vec. Qed.

Lemma swap_zero_divisor k (a b c d : cd k) :
  mul (S k) (a, b) (c, d) = zero (S k) -> re k a = D.zero ->
  mul (S k) (scale k neg_one (conjugate k d), c) (b, a) = zero (S k).
Proof.
  intros H Ha. pose proof (imaginary_conj k a Ha) as Ca.
  pose proof (f_equal fst H) as H1. pose proof (f_equal snd H) as H2. cbn [mul fst snd zero] in H1, H2.
  cbn [mul fst snd zero]. f_equal.
  - rewrite mul_scale_l, Ca, mul_scale_l, <- H1. vec.
  - pose proof (f_equal (conjugate k) H2) as C.
    rewrite conj_add, !conj_mul, conj_conj, conj_zero, Ca, mul_scale_l in C.
    rewrite mul_scale_r. exact C.
Qed.

Lemma swap_nonzero k (c d : cd k) :
  (c, d) <> zero (S k) -> (scale k neg_one (conjugate k d), c) <> zero (S k).
Proof.
  intros H E. apply H. pose proof (f_equal fst E) as E1. pose proof (f_equal snd E) as E2.
  cbn [fst snd zero] in E1, E2. cbn [zero]. subst c. f_equal.
  assert (Cd : conjugate k d = zero k).
  { apply ext. intros i _. pose proof (f_equal (fun v => coord k v i) E1) as Hi. cbn beta in Hi.
    rewrite coord_scale, coord_zero in Hi. rewrite coord_zero.
    destruct (D.mul_integral _ _ Hi) as [Z|Z]; [exfalso; exact (neg_one_neq_zero Z) | exact Z]. }
  rewrite <- (conj_conj k d), Cd. apply conj_zero.
Qed.

Theorem lemma_9_5 k (x y : cd (S k)) :
  mul (S k) x y = zero (S k) -> y <> zero (S k) ->
  dot (S k) x (one (S k)) = D.zero /\ dot (S k) x (i_unit k) = D.zero.
Proof.
  intros H Hy. destruct x as [a b], y as [c d].
  pose proof (re_left_zero (S k) (a, b) (c, d) H Hy) as Ha. cbn [re fst] in Ha.
  split.
  - rewrite dot_one_r. exact Ha.
  - rewrite dot_i_unit. cbn [snd].
    exact (re_left_zero (S k) (b, a) _ (kernel_swap (S k) _ _ (swap_zero_divisor k a b c d H Ha))
             (swap_nonzero k c d Hy)).
Qed.

Theorem annihilator_orthogonal k (x y : cd (S k)) :
  x <> zero (S k) -> mul (S k) x y = zero (S k) ->
  dot (S k) y (one (S k)) = D.zero /\ dot (S k) y (i_unit k) = D.zero.
Proof. intros Hx H. exact (lemma_9_5 k y x (kernel_swap (S k) x y H) Hx). Qed.

(** Direct finiteness with the integer-cleared inverse family
    <a, a> b = conj(a) + w, a w = 0: a annihilates <a, a> b - conj(a), the
    kernel swap moves a to the right, and <a, a> cancels because the domain
    has no zero divisors. *)

Lemma one_nonzero k : one k <> zero k.
Proof. intro E. pose proof (f_equal (re k) E) as R. rewrite re_one, re_zero in R. exact (D.one_neq_zero R). Qed.

Lemma right_inverse_nonzero k a b : mul k a b = one k -> a <> zero k.
Proof. intros H E. rewrite E, mul_zero_l in H. exact (one_nonzero k (eq_sym H)). Qed.

Theorem right_inverse_affine k a b :
  mul k a b = one k ->
  mul k a (add k (scale k (dot k a a) b) (scale k neg_one (conjugate k a))) = zero k.
Proof.
  intro H. rewrite mul_add_r, !mul_scale_r, H, norm_mul_r. vec.
Qed.

Theorem direct_finiteness k a b : mul k a b = one k -> mul k b a = one k.
Proof.
  intro H.
  assert (Na : dot k a a <> D.zero).
  { intro N. exact (right_inverse_nonzero k a b H (dot_self_zero k a N)). }
  pose proof (kernel_swap k _ _ (right_inverse_affine k a b H)) as W.
  rewrite mul_add_l, !mul_scale_l, norm_mul_l in W.
  apply ext. intros i _.
  pose proof (f_equal (fun v => coord k v i) W) as Wi. cbn beta in Wi.
  autorewrite with domain_coord in Wi.
  assert (E : D.mul (dot k a a) (D.sub (coord k (mul k b a) i) (coord k (one k) i)) = D.zero).
  { rewrite <- Wi. unfold neg_one. dring. }
  destruct (D.mul_integral _ _ E) as [Z|Z]; [exfalso; exact (Na Z) |].
  transitivity (D.add (D.sub (coord k (mul k b a) i) (coord k (one k) i)) (coord k (one k) i)); [ring | rewrite Z; ring].
Qed.

End CdTower.

(** The integers. *)

Module ZDomain <: OrderedDomain.
  Definition t := Z.
  Definition zero := 0%Z.
  Definition one := 1%Z.
  Definition add := Z.add.
  Definition mul := Z.mul.
  Definition sub := Z.sub.
  Definition opp := Z.opp.
  Definition le := Z.le.
  Lemma ring_th : ring_theory zero one add mul sub opp (@eq t). Proof. exact Zth. Qed.
  Lemma one_neq_zero : one <> zero. Proof. discriminate. Qed.
  Lemma sq_nonneg : forall a, le zero (mul a a). Proof. exact Z.square_nonneg. Qed.
  Lemma add_nonneg : forall a b, le zero a -> le zero b -> le zero (add a b).
  Proof. unfold le, zero, add. intros. lia. Qed.
  Lemma nonneg_sum_zero : forall a b, le zero a -> le zero b -> add a b = zero -> a = zero.
  Proof. unfold le, zero, add. intros. lia. Qed.
  Lemma mul_integral : forall a b, mul a b = zero -> a = zero \/ b = zero. Proof. exact Zmult_integral. Qed.
End ZDomain.

(** The Stdlib reals. *)

Module RDomain <: OrderedDomain.
  Definition t := R.
  Definition zero := 0%R.
  Definition one := 1%R.
  Definition add := Rplus.
  Definition mul := Rmult.
  Definition sub := Rminus.
  Definition opp := Ropp.
  Definition le := Rle.
  Lemma ring_th : ring_theory zero one add mul sub opp (@eq t). Proof. exact RTheory. Qed.
  Lemma one_neq_zero : one <> zero. Proof. exact R1_neq_R0. Qed.
  Lemma sq_nonneg : forall a, le zero (mul a a).
  Proof. intro a. destruct (Rle_or_lt 0 a) as [L|L]; [exact (Rmult_le_pos a a L L) |].
    rewrite <- Rmult_opp_opp. apply Rmult_le_pos; apply Ropp_0_ge_le_contravar; apply Rle_ge, Rlt_le, L. Qed.
  Lemma add_nonneg : forall a b, le zero a -> le zero b -> le zero (add a b). Proof. exact Rplus_le_le_0_compat. Qed.
  Lemma nonneg_sum_zero : forall a b, le zero a -> le zero b -> add a b = zero -> a = zero. Proof. exact Rplus_eq_0_l. Qed.
  Lemma mul_integral : forall a b, mul a b = zero -> a = zero \/ b = zero. Proof. exact Rmult_integral. Qed.
End RDomain.

Module ZTower := CdTower ZDomain.
Module RTower := CdTower RDomain.

(** The field extension: an ordered domain whose nonzero elements invert
    gives the affine inverse family of the real file, b = conj(a)/<a, a> + w
    with a w = 0, from the integer-cleared one. *)

Module Type OrderedField.
  Include OrderedDomain.
  Parameter inv : t -> t.
  Axiom inv_l : forall a, a <> zero -> mul (inv a) a = one.
End OrderedField.

Module CdTowerField (F : OrderedField).
Module T := CdTower F.
Add Ring field_domain_ring : F.ring_th.

Theorem right_inverse_form k a b :
  T.mul k a b = T.one k ->
  exists w, T.mul k a w = T.zero k /\ b = T.add k (T.scale k (F.inv (T.dot k a a)) (T.conjugate k a)) w.
Proof.
  intro H.
  assert (Na : T.dot k a a <> F.zero).
  { intro N. exact (T.right_inverse_nonzero k a b H (T.dot_self_zero k a N)). }
  pose proof (F.inv_l _ Na) as I.
  exists (T.add k b (T.scale k T.neg_one (T.scale k (F.inv (T.dot k a a)) (T.conjugate k a)))).
  split.
  - rewrite T.mul_add_r, !T.mul_scale_r, H, T.norm_mul_r. apply T.ext. intros i _.
    rewrite T.coord_add, !T.coord_scale, T.coord_zero.
    transitivity (F.sub (T.coord k (T.one k) i) (F.mul (F.mul (F.inv (T.dot k a a)) (T.dot k a a)) (T.coord k (T.one k) i))).
    + unfold T.neg_one. ring.
    + rewrite I. ring.
  - apply T.ext. intros i _. rewrite !T.coord_add, !T.coord_scale. unfold T.neg_one. ring.
Qed.
End CdTowerField.

Module RField <: OrderedField.
  Include RDomain.
  Definition inv := Rinv.
  Lemma inv_l : forall a, a <> zero -> mul (inv a) a = one. Proof. exact Rinv_l. Qed.
End RField.

Module RFieldTower := CdTowerField RField.
