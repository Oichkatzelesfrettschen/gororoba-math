(** Right multiplication by the imaginary sum s = e_1 + ... + e_(n-1) of the
    Cayley-Dickson algebra of dimension n = 2^k is a skew conference matrix:
    <x s, y> = - <x, y s> and <x s, y s> = (n - 1) <x, y> for every k, so
    I + R_s is a skew Hadamard matrix.

    The tower is the recursive pair construction with integer coefficients,
    (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)), the doubling that
    gororoba_quantum/cd_core.py cd_sign reads and that open_gororoba
    proofs/theories/RecursiveCDTower.v defines over the reals; negation is
    scaling by -1. Coordinate i of a level-(j + 1) element lies in its first
    half when i < 2^j, so index bit j selects the doubling half as in cd_sign.

    The imaginary sum doubles as s' = (s, 1 + s). The induction carries three
    laws from s to s': s (s x) = (x s) s = -(n - 1) x and s (x s) = (s x) s.
    The last one, flexibility of s, is proved here rather than assumed. *)

From Stdlib Require Import ZArith Lia.
Open Scope Z_scope.

Fixpoint cd (k : nat) : Type :=
  match k with O => Z | S j => (cd j * cd j)%type end.

Fixpoint zero (k : nat) : cd k :=
  match k with O => 0 | S j => (zero j, zero j) end.

Fixpoint one (k : nat) : cd k :=
  match k with O => 1 | S j => (one j, zero j) end.

Fixpoint add (k : nat) : cd k -> cd k -> cd k :=
  match k as d return cd d -> cd d -> cd d with
  | O => Z.add
  | S j => fun x y => (add j (fst x) (fst y), add j (snd x) (snd y))
  end.

Fixpoint scale (k : nat) (r : Z) : cd k -> cd k :=
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
  | O => Z.mul
  | S j => fun x y =>
      (add j (mul j (fst x) (fst y)) (scale j (-1) (mul j (conjugate j (snd y)) (snd x))),
       add j (mul j (snd y) (fst x)) (mul j (snd x) (conjugate j (fst y))))
  end.

Fixpoint re (k : nat) : cd k -> Z :=
  match k as d return cd d -> Z with
  | O => fun v => v
  | S j => fun v => re j (fst v)
  end.

Fixpoint dot (k : nat) : cd k -> cd k -> Z :=
  match k as d return cd d -> cd d -> Z with
  | O => Z.mul
  | S j => fun x y => dot j (fst x) (fst y) + dot j (snd x) (snd y)
  end.

Fixpoint coord (k : nat) : cd k -> nat -> Z :=
  match k as d return cd d -> nat -> Z with
  | O => fun v _ => v
  | S j => fun v i =>
      if Nat.ltb i (Nat.pow 2 j) then coord j (fst v) i else coord j (snd v) (i - Nat.pow 2 j)
  end.

(** The imaginary sum and n - 1 = 2^k - 1. *)
Fixpoint isum (k : nat) : cd k :=
  match k with O => 0 | S j => (isum j, add j (one j) (isum j)) end.

Fixpoint m (k : nat) : Z :=
  match k with O => 0 | S j => 2 * m j + 1 end.

Lemma m_S j : m (S j) = 2 * m j + 1.
Proof. reflexivity. Qed.
Arguments m : simpl never.

(** Coordinates decide equality, which reduces each vector identity below to
    an identity of integer linear combinations. *)

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

Lemma mul_one k : (forall x, mul k (one k) x = x) /\ (forall x, mul k x (one k) = x).
Proof.
  induction k as [|j IH]; simpl.
  - split; [exact Z.mul_1_l | exact Z.mul_1_r].
  - destruct IH as [Ol Or]. destruct (mul_zero j) as [Zl Zr].
    split; intros [x1 x2]; simpl; rewrite ?conj_zero, ?conj_one, ?Ol, ?Or, ?Zl, ?Zr; f_equal; vec.
Qed.

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

Lemma conj_isum k : conjugate k (isum k) = scale k (-1) (isum k).
Proof.
  induction k as [|j IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Create Rewrite HintDb alg.
Hint Rewrite mul_add_l mul_add_r mul_scale_l mul_scale_r conj_add conj_scale conj_mul conj_conj
  conj_one conj_zero conj_isum : alg.

Lemma mul_one_l k x : mul k (one k) x = x. Proof. apply mul_one. Qed.
Lemma mul_one_r k x : mul k x (one k) = x. Proof. apply mul_one. Qed.
Hint Rewrite mul_one_l mul_one_r : alg.

Lemma conj_split k x : conjugate k x = add k (scale k (2 * re k x) (one k)) (scale k (-1) x).
Proof.
  transitivity (add k (add k x (conjugate k x)) (scale k (-1) x)); [vec | now rewrite add_conj].
Qed.

(** The induction step. Expanding s' = (s, 1 + s) through the doubling leaves
    the squares in terms of s (s y), (y s) s and (s y) s - s (y s), which the
    hypotheses close. The two commutation components also carry x + conj x,
    a real multiple of 1; after conj x = 2 re(x) 1 - x they close through
    s s = -(n - 1) 1, the first law applied to 1. *)
Theorem isum_laws k :
  (forall x, mul k (isum k) (mul k (isum k) x) = scale k (- m k) x) /\
  (forall x, mul k (mul k x (isum k)) (isum k) = scale k (- m k) x) /\
  (forall x, mul k (isum k) (mul k x (isum k)) = mul k (mul k (isum k) x) (isum k)).
Proof.
  induction k as [|j IH]; simpl.
  - repeat split; intro x; cbv [mul isum scale m cd]; ring.
  - destruct IH as [L2 [R2 F]]. rewrite m_S. set (M := m j) in *. clearbody M.
    assert (Sq : mul j (isum j) (isum j) = scale j (- M) (one j)).
    { rewrite <- (mul_one_r j (isum j)) at 2. rewrite L2. reflexivity. }
    repeat split; intros [x1 x2]; cbn [mul conjugate isum scale add fst snd one zero];
      autorewrite with alg;
      rewrite ?(conj_split j x1), ?(conj_split j x2); autorewrite with alg;
      rewrite ?L2, ?R2, ?F, ?Sq; f_equal; vec.
Qed.

(** The coordinate inner product and the skew form of L_s and R_s. *)

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

Theorem isum_skew k :
  (forall x y, dot k (mul k (isum k) x) y = - dot k x (mul k (isum k) y)) /\
  (forall x y, dot k (mul k x (isum k)) y = - dot k x (mul k y (isum k))).
Proof.
  induction k as [|j IH].
  - split; intros x y; cbv [dot mul isum cd]; ring.
  - destruct IH as [SkL SkR].
    split; intros [x1 x2] [y1 y2]; cbn [dot mul conjugate isum scale add fst snd one zero];
      repeat progress (autorewrite with alg dotlin; rewrite ?SkL, ?SkR, ?dot_conj); ring.
Qed.

(** n - 1 = 2^k - 1, and the conference and Hadamard identities. *)

Lemma m_closed k : m k = 2 ^ Z.of_nat k - 1.
Proof.
  induction k as [|j IH].
  - reflexivity.
  - rewrite m_S, IH, Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Theorem isum_conference k : forall x y,
  dot k (mul k x (isum k)) (mul k y (isum k)) = (2 ^ Z.of_nat k - 1) * dot k x y.
Proof.
  intros x y. destruct (isum_skew k) as [_ SkR]. destruct (isum_laws k) as [_ [R2 _]].
  rewrite SkR, R2, dot_scale_r, m_closed. ring.
Qed.

Theorem isum_skew_hadamard k : forall x y,
  dot k (add k x (mul k x (isum k))) (add k y (mul k y (isum k))) = 2 ^ Z.of_nat k * dot k x y.
Proof.
  intros x y. destruct (isum_skew k) as [_ SkR].
  rewrite !dot_add_l, !dot_add_r, isum_conference, (SkR x y). ring.
Qed.
