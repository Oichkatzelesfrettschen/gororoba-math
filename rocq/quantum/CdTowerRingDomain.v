(** The ordered-domain tower of CdTowerDomain.v is the commutative-ring tower
    of CdTowerRing.v at the same coefficients. An OrderedDomain holds every
    field of CommutativeRing, so RingTower applies to ZDomain and RDomain,
    and each operation of the result is convertible with the operation of
    ZTower and RTower: the carrier, zero, one, add, scale, conjugate, mul
    and re are the same fixpoints, and every *_eq lemma below closes by
    reflexivity. The product whose kernel swap RingTowerI refutes over a
    ring with a square root of -1 is therefore the product for which
    CdTower proves Corollary 9.3 over an ordered domain, and the two
    statements differ in their coefficients alone.

    ZRingBridge and RRingBridge restate the reflection (a, b) -> (a, -b) in
    the vocabulary of ZTower and RTower: it preserves the product, and it
    carries the annihilator of x onto the annihilator of its image. The
    integer statements hold with no axiom, the real ones on the two Stdlib
    real-construction axioms that RDomain's ring laws rest on. *)

Require Import CdTowerDomain CdTowerRing.

Module ZRing := RingTower ZDomain.
Module RRing := RingTower RDomain.

Module ZRingBridge.
  Lemma cd_eq : ZRing.cd = ZTower.cd. Proof. reflexivity. Qed.
  Lemma zero_eq : ZRing.zero = ZTower.zero. Proof. reflexivity. Qed.
  Lemma one_eq : ZRing.one = ZTower.one. Proof. reflexivity. Qed.
  Lemma add_eq : ZRing.add = ZTower.add. Proof. reflexivity. Qed.
  Lemma scale_eq : ZRing.scale = ZTower.scale. Proof. reflexivity. Qed.
  Lemma conjugate_eq : ZRing.conjugate = ZTower.conjugate. Proof. reflexivity. Qed.
  Lemma mul_eq : ZRing.mul = ZTower.mul. Proof. reflexivity. Qed.
  Lemma re_eq : ZRing.re = ZTower.re. Proof. reflexivity. Qed.

  Definition reflect k (x : ZTower.cd (S k)) : ZTower.cd (S k) :=
    (fst x, ZTower.scale k ZTower.neg_one (snd x)).

  Lemma reflect_eq : ZRing.reflect = reflect. Proof. reflexivity. Qed.

  Theorem reflect_mul k x y : reflect k (ZTower.mul (S k) x y) = ZTower.mul (S k) (reflect k x) (reflect k y).
  Proof. exact (ZRing.reflect_mul k x y). Qed.

  Theorem reflect_involutive k x : reflect k (reflect k x) = x.
  Proof. exact (ZRing.reflect_involutive k x). Qed.

  Theorem reflect_kernel k x z :
    ZTower.mul (S k) x z = ZTower.zero (S k) <-> ZTower.mul (S k) (reflect k x) (reflect k z) = ZTower.zero (S k).
  Proof. exact (ZRing.reflect_kernel k x z). Qed.

  Theorem pure_kernel_conj k a z :
    ZTower.conjugate k a = ZTower.scale k ZTower.neg_one a ->
    (ZTower.mul k a z = ZTower.zero k <-> ZTower.mul k (ZTower.conjugate k z) a = ZTower.zero k).
  Proof. exact (ZRing.pure_kernel_conj k a z). Qed.
End ZRingBridge.

Module RRingBridge.
  Lemma cd_eq : RRing.cd = RTower.cd. Proof. reflexivity. Qed.
  Lemma zero_eq : RRing.zero = RTower.zero. Proof. reflexivity. Qed.
  Lemma one_eq : RRing.one = RTower.one. Proof. reflexivity. Qed.
  Lemma add_eq : RRing.add = RTower.add. Proof. reflexivity. Qed.
  Lemma scale_eq : RRing.scale = RTower.scale. Proof. reflexivity. Qed.
  Lemma conjugate_eq : RRing.conjugate = RTower.conjugate. Proof. reflexivity. Qed.
  Lemma mul_eq : RRing.mul = RTower.mul. Proof. reflexivity. Qed.
  Lemma re_eq : RRing.re = RTower.re. Proof. reflexivity. Qed.

  Definition reflect k (x : RTower.cd (S k)) : RTower.cd (S k) :=
    (fst x, RTower.scale k RTower.neg_one (snd x)).

  Lemma reflect_eq : RRing.reflect = reflect. Proof. reflexivity. Qed.

  Theorem reflect_mul k x y : reflect k (RTower.mul (S k) x y) = RTower.mul (S k) (reflect k x) (reflect k y).
  Proof. exact (RRing.reflect_mul k x y). Qed.

  Theorem reflect_involutive k x : reflect k (reflect k x) = x.
  Proof. exact (RRing.reflect_involutive k x). Qed.

  Theorem reflect_kernel k x z :
    RTower.mul (S k) x z = RTower.zero (S k) <-> RTower.mul (S k) (reflect k x) (reflect k z) = RTower.zero (S k).
  Proof. exact (RRing.reflect_kernel k x z). Qed.

  Theorem pure_kernel_conj k a z :
    RTower.conjugate k a = RTower.scale k RTower.neg_one a ->
    (RTower.mul k a z = RTower.zero k <-> RTower.mul k (RTower.conjugate k z) a = RTower.zero k).
  Proof. exact (RRing.pure_kernel_conj k a z). Qed.
End RRingBridge.
