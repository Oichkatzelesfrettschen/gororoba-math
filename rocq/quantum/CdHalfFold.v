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

    Open statement, the cross-operand fold, not proved here. For indices
    i, j below h = D/2 at dimension 2D = 2h, the two-term nullity of
    e_i +- e_(h+j) is n_2D(e_i +- e_(h+j)) = h - 4 - 2 n_h(e_i +- e_j) for
    e_(h+j) outside the span of e_i and e_0 (the mixed pair
    (a, 0), (0, x) of the note, |S+| = 2(h - 4 - |S+(a, x)|), nullity =
    |S+|/2). The paper proof is in docs/notes/singular_sector_dynamics.md
    (the mixed-pair bullet: the off-diagonal anticommutator is built from
    [L_a, R_x] and [R_a, L_x], and census Theorem 3 puts omega(a, c, x) = +1
    for c outside span(a, x) exactly when c lies in S+(a, x) of the level
    below), and scripts/singular_sector_dynamics.py checks the recursion at
    every pair through D = 512. A Rocq proof needs the census Theorem 3
    sign identity omega(a, c, x) on the tower, which no file under proofs/
    states yet. *)

From Stdlib Require Import Reals.
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
