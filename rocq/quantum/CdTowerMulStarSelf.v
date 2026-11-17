(** The product of a vector with its conjugate at the doubled level of the
    commutative-ring pair tower: the Rocq bridge of the Lean theorem
    CayleyDickson.mul_star_self of
    lean/GororobaMath/CayleyDickson/Basic.lean.

    Convention: the tower and product of CdTowerRing.v,
    (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)), with conjugation
    conj(a, b) = (conj a, -b) that is the identity at level 0. The Lean
    double CayleyDickson A has the same product on pairs (x.re, x.im) with
    star in place of conj, and the Lean theorem reads
    x * star x = (x.re * star x.re + star x.im * x.im, 0). A level S k
    vector is the pair (fst x, snd x) of level k vectors, so the Lean
    statement at A = the level k tower is mul_star_self below, with the
    level k product and conjugation in place of the Lean ones and zero k in
    the second half.

    The functor MulStarSelf restates the theorem at the coefficient ring D:

    - mul_star_self is CayleyDickson.mul_star_self.
    - star_mul_self is CayleyDickson.star_mul_self, the same step with the
      factors exchanged. It is stated for the pair; the Lean headline row
      cites mul_star_self.
    - mul_conj_scalar is a consequence at every level: x conj(x) is the
      real part of x conj(x) times the unit, by induction on the level with
      mul_star_self as the step. The Lean module holds no such statement,
      since its theorem is one doubling of an arbitrary star ring.

    The Rocq statements are narrower than the Lean one: the coefficients
    form a commutative ring whose conjugation is the identity (the
    signature CommutativeRing), where Lean takes every NonAssocRing with a
    StarRing, and the ring A of the doubling is a level of this tower,
    where Lean takes an arbitrary star ring. IntegerMulStarSelf
    instantiates the functor at the integers (IntegerRing). *)

From Stdlib Require Import Ring ZArith.
Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange.

Module MulStarSelf (D : CommutativeRing).
Module B := RingTowerBasis D.
Import B B.T.
Add Ring mul_star_self_ring : D.ring_th.

Theorem mul_star_self k (x : cd (S k)) :
  mul (S k) x (conjugate (S k) x) =
  (add k (mul k (fst x) (conjugate k (fst x))) (mul k (conjugate k (snd x)) (snd x)), zero k).
Proof.
  destruct x as [a b]. simpl.
  rewrite !conj_scale, !conj_conj, !mul_scale_l, scale_neg_neg.
  f_equal. vec.
Qed.

Theorem star_mul_self k (x : cd (S k)) :
  mul (S k) (conjugate (S k) x) x =
  (add k (mul k (conjugate k (fst x)) (fst x)) (mul k (conjugate k (snd x)) (snd x)), zero k).
Proof.
  destruct x as [a b]. simpl.
  rewrite !mul_scale_l, !mul_scale_r, scale_neg_neg.
  f_equal; vec.
Qed.

Lemma re_scale_one k r : re k (scale k r (one k)) = r.
Proof. rewrite re_scale, re_one. ring. Qed.

Lemma mul_conj_exists_scalar k x : exists r, mul k x (conjugate k x) = scale k r (one k).
Proof.
  induction k as [|j IH]; simpl in *.
  - exists (D.mul x x). simpl. ring.
  - destruct x as [a b]. destruct (IH a) as [r1 H1]. destruct (IH (conjugate j b)) as [r2 H2].
    rewrite conj_conj in H2.
    exists (D.add r1 r2). simpl.
    rewrite !conj_scale, !conj_conj, !mul_scale_l, scale_neg_neg, H1, H2.
    f_equal; vec.
Qed.

Theorem mul_conj_scalar k x :
  mul k x (conjugate k x) = scale k (re k (mul k x (conjugate k x))) (one k).
Proof.
  destruct (mul_conj_exists_scalar k x) as [r H]. rewrite H, re_scale_one. reflexivity.
Qed.

End MulStarSelf.

Module IntegerMulStarSelf := MulStarSelf IntegerRing.
