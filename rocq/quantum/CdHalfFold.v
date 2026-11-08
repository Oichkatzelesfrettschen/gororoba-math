(** The half-operand fold of the Cayley-Dickson kernel: in the pair tower at
    level k + 1 with the doubling (a, b)(c, d) = (ac - conj(d) b,
    da + b conj(c)), left multiplication by an operand that lives in one
    half has a kernel that is the product of two copies of the kernel one
    level down.

    First half: (a, 0)(c, d) = (ac, da), so (a, 0)(c, d) = 0 exactly when
    a c = 0 and a d = 0; the second component d a = 0 becomes a d = 0 by the
    kernel equality a z = 0 <-> z a = 0 (Corollary 9.3 of Biss, Dugger and
    Isaksen, math/0511691).

    Second half: (0, b)(c, d) = (-conj(d) b, b conj(c)), so (0, b)(c, d) = 0
    exactly when conj(d) b = 0 and b conj(c) = 0. Lemma 9.2 (x y = 0 <->
    conj(x) y = 0 <-> x conj(y) = 0) removes the two conjugations, and the
    kernel equality turns d b = 0 into b d = 0.

    The statements and proofs are generic over the ordered coefficient domain
    of CdTowerDomain.v: the functor HalfFold takes the coefficient
    signature, proves both folds on the tower CdTower D from that file's
    kernel_equality and lemma_9_2, and ZHalf and RHalf instantiate it at the
    integers and the Stdlib reals. RealHalfFold restates both theorems in the
    vocabulary of CdTowerReal.v through the operation identities of
    CdTowerDomainR.v. Nothing is re-proved: the only new reasoning is the
    componentwise computation of the two products. No step uses
    associativity, alternativity or multiplicativity of the norm, which fail
    from level 4 on.

    Consequence: the nullity of left multiplication by (a, 0) or (0, a) at
    level k + 1 is twice the nullity of left multiplication by a at level k,
    which is the doubling of |S+| on the low and the high pairs in
    docs/notes/singular_sector_dynamics.md.

    The dimension statement of that consequence is RealHalfFoldDimension: a
    kernel is the product of two copies of the kernel one level down, and a
    basis of m vectors of a subspace W1 and one of n vectors of W2 give a
    basis of m + n vectors of the product, so whenever ker L_a has a basis of
    n vectors at level k, ker L_(a, 0) and ker L_(0, a) have bases of 2n
    vectors at level k + 1 and the rank 2^k - n doubles to 2^(k + 1) - 2n.
    The existence of a basis of every subspace of R^(2^k) and the invariance
    of the basis size are the standard finite-dimensional facts that enter
    through the hypothesis; the rank is the dimension 2^k minus the nullity.

    Open statement, the cross-operand fold, not proved here. Let h = 2^k with
    k >= 3, let 0 < i < h and 0 <= j < h, let t = +1 or t = -1, and let
    n_m(x) be the nullity of left multiplication by x at dimension m. Then
    n_2h(e_i + t e_(h+j)) = 0 when j = 0 or j = i, and otherwise
    n_2h(e_i + t e_(h+j)) = h - 4 - 2 n_h(e_i + t e_j). The case i = 0 is the
    scalar-plus-high operand and is no instance of the rule: its value at
    h = 16, n_32 = 0, is recorded in docs/evidence/a5-w8-twisted-product (the
    spectrum of the 512 mixed basis pairs, whose 420 pairs with i, j >= 1 and
    i != j follow the rule and whose 92 remaining pairs have n_32 = 0). The
    mixed pair (a, 0), (0, x) of docs/notes/singular_sector_dynamics.md
    carries |S+| = 2(h - 4 - |S+(a, x)|) and nullity = |S+|/2. The paper
    proof is in docs/notes/singular_sector_dynamics.md (the mixed-pair
    bullet: the off-diagonal anticommutator is built from [L_a, R_x] and
    [R_a, L_x], and census Theorem 3 puts omega(a, c, x) = +1 for c outside
    span(a, x) exactly when c lies in S+(a, x) of the level below), and
    scripts/singular_sector_dynamics.py checks the recursion at every pair
    through D = 512. A Rocq proof needs the census Theorem 3 sign identity
    omega(a, c, x) on the tower, which no file under proofs/ states yet. *)

From Stdlib Require Import Reals List Lia.
Require Import CdTowerDomain.
Require CdTowerReal CdTowerDomainR.

Module HalfFold (D : OrderedDomain).
  Module T := CdTower D.
  Import T.

  Lemma pair_zero k (p q : cd k) : @eq (cd (S k)) (p, q) (zero (S k)) <-> p = zero k /\ q = zero k.
  Proof.
    cbn [zero]. split.
    - intro H. split; [exact (f_equal fst H) | exact (f_equal snd H)].
    - intros [Hp Hq]. rewrite Hp, Hq. reflexivity.
  Qed.

  Lemma add_zero_l k (x : cd k) : add k (zero k) x = x.
  Proof. vec. Qed.

  Lemma add_zero_r k (x : cd k) : add k x (zero k) = x.
  Proof. vec. Qed.

  Lemma scale_neg_one_zero k (x : cd k) : scale k neg_one x = zero k <-> x = zero k.
  Proof.
    split; intro H.
    - transitivity (scale k neg_one (scale k neg_one x)); [vec |].
      rewrite H. apply scale_zero.
    - rewrite H. apply scale_zero.
  Qed.

  (** The two products of a half operand, computed componentwise. *)

  Lemma mul_low k (a c d : cd k) : mul (S k) (a, zero k) (c, d) = (mul k a c, mul k d a).
  Proof.
    cbn [mul fst snd]. rewrite mul_zero_r, mul_zero_l, scale_zero, add_zero_r, add_zero_r. reflexivity.
  Qed.

  Lemma mul_high k (b c d : cd k) :
    mul (S k) (zero k, b) (c, d) = (scale k neg_one (mul k (conjugate k d) b), mul k b (conjugate k c)).
  Proof.
    cbn [mul fst snd]. rewrite mul_zero_l, mul_zero_r, add_zero_l, add_zero_l. reflexivity.
  Qed.

  Theorem first_half k (a c d : cd k) :
    mul (S k) (a, zero k) (c, d) = zero (S k) <-> mul k a c = zero k /\ mul k a d = zero k.
  Proof.
    rewrite mul_low, pair_zero. apply and_iff_compat_l. apply kernel_equality.
  Qed.

  Theorem second_half k (b c d : cd k) :
    mul (S k) (zero k, b) (c, d) = zero (S k) <-> mul k b c = zero k /\ mul k b d = zero k.
  Proof.
    rewrite mul_high, pair_zero, scale_neg_one_zero.
    destruct (lemma_9_2 k b c) as [_ Hc]. destruct (lemma_9_2 k d b) as [Hd _].
    rewrite <- Hc, <- Hd, (kernel_equality k d b). tauto.
  Qed.
End HalfFold.

Module ZHalf := HalfFold ZDomain.
Module RHalf := HalfFold RDomain.

(** The real tower of CdTowerReal.v, the vocabulary of
    CdAnnihilatorSymmetryReal.v. *)

Module RealHalfFold.
  Import CdTowerReal.

  Theorem first_half k (a c d : cd k) :
    mul (S k) (a, zero k) (c, d) = zero (S k) <-> mul k a c = zero k /\ mul k a d = zero k.
  Proof.
    rewrite <- !CdTowerDomainR.RBridge.mul_eq, <- !CdTowerDomainR.RBridge.zero_eq.
    apply RHalf.first_half.
  Qed.

  Theorem second_half k (b c d : cd k) :
    mul (S k) (zero k, b) (c, d) = zero (S k) <-> mul k b c = zero k /\ mul k b d = zero k.
  Proof.
    rewrite <- !CdTowerDomainR.RBridge.mul_eq, <- !CdTowerDomainR.RBridge.zero_eq.
    apply RHalf.second_half.
  Qed.
End RealHalfFold.

(** Dimension of the kernels of a half operand. A subspace W of the real tower
    has dimension n when n vectors of W are linearly independent and span W. *)

Module RealHalfFoldDimension.
  Import CdTowerReal ListNotations.

  Fixpoint lin_comb k (cs : list R) (vs : list (cd k)) : cd k :=
    match cs, vs with
    | c :: cs', v :: vs' => add k (scale k c v) (lin_comb k cs' vs')
    | _, _ => zero k
    end.

  Definition independent k (vs : list (cd k)) : Prop :=
    forall cs, length cs = length vs -> lin_comb k cs vs = zero k -> Forall (fun c => c = 0%R) cs.

  Definition spans k (W : cd k -> Prop) (vs : list (cd k)) : Prop :=
    forall w, W w -> exists cs, length cs = length vs /\ lin_comb k cs vs = w.

  Definition has_dim k (W : cd k -> Prop) (n : nat) : Prop :=
    exists vs : list (cd k), length vs = n /\ Forall W vs /\ independent k vs /\ spans k W vs.

  Lemma add_zero_left k (x : cd k) : add k (zero k) x = x.
  Proof. vec. Qed.

  Lemma add_zero_right k (x : cd k) : add k x (zero k) = x.
  Proof. vec. Qed.

  Lemma lin_comb_app k (cs1 cs2 : list R) (vs1 vs2 : list (cd k)) :
    length cs1 = length vs1 ->
    lin_comb k (cs1 ++ cs2) (vs1 ++ vs2) = add k (lin_comb k cs1 vs1) (lin_comb k cs2 vs2).
  Proof.
    revert vs1. induction cs1 as [|c cs1 IH]; intros [|v vs1] H; simpl in H |- *; try discriminate.
    - symmetry. apply add_zero_left.
    - rewrite (IH vs1 ltac:(lia)). vec.
  Qed.

  Lemma lin_comb_low k (cs : list R) (vs : list (cd k)) :
    lin_comb (S k) cs (map (fun v => (v, zero k)) vs) = (lin_comb k cs vs, zero k).
  Proof.
    revert vs. induction cs as [|c cs IH]; intros [|v vs]; simpl; try reflexivity.
    rewrite IH. simpl. f_equal. rewrite scale_zero. apply add_zero_left.
  Qed.

  Lemma lin_comb_high k (cs : list R) (vs : list (cd k)) :
    lin_comb (S k) cs (map (fun v => (zero k, v)) vs) = (zero k, lin_comb k cs vs).
  Proof.
    revert vs. induction cs as [|c cs IH]; intros [|v vs]; simpl; try reflexivity.
    rewrite IH. simpl. f_equal. rewrite scale_zero. apply add_zero_left.
  Qed.

  Lemma has_dim_equivalent k (W W' : cd k -> Prop) n :
    (forall w, W w <-> W' w) -> has_dim k W n -> has_dim k W' n.
  Proof.
    intros E [vs [len [F [I S]]]]. exists vs. split; [exact len|]. split.
    - eapply Forall_impl; [|exact F]. intros v Hv. apply E. exact Hv.
    - split; [exact I|]. intros w Hw. apply S. apply E. exact Hw.
  Qed.

  (** A basis of m vectors of W1 and one of n vectors of W2, both subspaces
      of level k, give a basis of m + n vectors of the product subspace of
      level k + 1. *)
  Theorem product_dimension k (W1 W2 : cd k -> Prop) m n :
    W1 (zero k) -> W2 (zero k) -> has_dim k W1 m -> has_dim k W2 n ->
    has_dim (S k) (fun p => W1 (fst p) /\ W2 (snd p)) (m + n)%nat.
  Proof.
    intros Z1 Z2 [vs1 [len1 [F1 [I1 S1]]]] [vs2 [len2 [F2 [I2 S2]]]].
    exists (map (fun v => (v, zero k)) vs1 ++ map (fun v => (zero k, v)) vs2).
    split; [rewrite length_app, !length_map; lia|]. split; [|split].
    - apply Forall_app. split; apply Forall_forall; intros p Hp.
      + apply in_map_iff in Hp. destruct Hp as [v [<- Hv]]. simpl.
        split; [exact (proj1 (Forall_forall _ _) F1 v Hv) | exact Z2].
      + apply in_map_iff in Hp. destruct Hp as [v [<- Hv]]. simpl.
        split; [exact Z1 | exact (proj1 (Forall_forall _ _) F2 v Hv)].
    - intros cs hl hz. rewrite length_app, !length_map in hl.
      rewrite <- (firstn_skipn m cs) in hz |- *.
      rewrite lin_comb_app in hz by (rewrite length_firstn, length_map; lia).
      rewrite lin_comb_low, lin_comb_high in hz. simpl in hz.
      rewrite add_zero_right, add_zero_left in hz.
      pose proof (f_equal fst hz) as Hfst. pose proof (f_equal snd hz) as Hsnd. simpl in Hfst, Hsnd.
      apply Forall_app. split.
      + apply I1; [rewrite length_firstn; lia | exact Hfst].
      + apply I2; [rewrite length_skipn; lia | exact Hsnd].
    - intros [w1 w2] [H1 H2].
      destruct (S1 w1 H1) as [cs1 [l1 e1]]. destruct (S2 w2 H2) as [cs2 [l2 e2]].
      exists (cs1 ++ cs2). split; [rewrite !length_app, !length_map; lia|].
      rewrite lin_comb_app by (rewrite length_map; exact l1).
      rewrite lin_comb_low, lin_comb_high, e1, e2. simpl. rewrite add_zero_right, add_zero_left. reflexivity.
  Qed.

  Definition ker_left k (a : cd k) : cd k -> Prop := fun c => mul k a c = zero k.

  Lemma ker_left_zero k (a : cd k) : ker_left k a (zero k).
  Proof. unfold ker_left. apply mul_zero_r. Qed.

  (** The nullity of left multiplication by (a, 0) is twice that of a. *)
  Theorem half_fold_dimension_low k (a : cd k) n :
    has_dim k (ker_left k a) n -> has_dim (S k) (ker_left (S k) (a, zero k)) (n + n).
  Proof.
    intro H. eapply has_dim_equivalent;
      [|exact (product_dimension k _ _ n n (ker_left_zero k a) (ker_left_zero k a) H H)].
    intros [c d]. unfold ker_left. simpl. symmetry. apply RealHalfFold.first_half.
  Qed.

  (** The same for (0, b), through the second fold. *)
  Theorem half_fold_dimension_high k (b : cd k) n :
    has_dim k (ker_left k b) n -> has_dim (S k) (ker_left (S k) (zero k, b)) (n + n).
  Proof.
    intro H. eapply has_dim_equivalent;
      [|exact (product_dimension k _ _ n n (ker_left_zero k b) (ker_left_zero k b) H H)].
    intros [c d]. unfold ker_left. simpl. symmetry. apply RealHalfFold.second_half.
  Qed.

  (** The rank is the dimension 2^k minus the nullity. *)
  Definition rank_of_nullity k (nullity : nat) : nat := (Nat.pow 2 k - nullity)%nat.

  Theorem half_fold_rank k (nullity : nat) :
    (nullity <= Nat.pow 2 k)%nat ->
    (rank_of_nullity (S k) (nullity + nullity) = 2 * rank_of_nullity k nullity)%nat.
  Proof. intro H. unfold rank_of_nullity. simpl. lia. Qed.
End RealHalfFoldDimension.
