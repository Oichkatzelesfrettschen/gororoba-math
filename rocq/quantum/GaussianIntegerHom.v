(** Ring homomorphisms out of the Gaussian integers, and the cancellation law of the Gaussian integers.

    - [GaussianHom D]: for a commutative ring D with a square root i of -1, the map (a, b) -> a + b i from the
      Gaussian integers of CdTowerRing.v to D is a ring homomorphism.
    - [IdentityHom A]: the identity homomorphism of a commutative ring; [GaussianIdentity] is the one of the
      Gaussian integers.
    - [gaussian_regular]: a nonzero Gaussian integer is a nonzero divisor, from the norm identity
      (a c - b e)^2 + (a e + b c)^2 = (a^2 + b^2) (c^2 + e^2). *)

From Stdlib Require Import Ring Lia ZArith.
Require Import CdTowerRing CdTowerRingBaseChange.

Module GaussianHom (D : CommutativeRingWithI) <: RingHom GaussianIntegers D.
  Module Z_D := IntegerHom D.
  Add Ring gaussian_target : D.ring_th.
  Definition of_Z : Z -> D.t := Z_D.h.
  Lemma of_Z_zero : of_Z 0%Z = D.zero. Proof. exact Z_D.h_zero. Qed.
  Lemma of_Z_one : of_Z 1%Z = D.one. Proof. exact Z_D.h_one. Qed.
  Lemma of_Z_add : forall x y, of_Z (x + y)%Z = D.add (of_Z x) (of_Z y). Proof. exact Z_D.h_add. Qed.
  Lemma of_Z_mul : forall x y, of_Z (x * y)%Z = D.mul (of_Z x) (of_Z y). Proof. exact Z_D.h_mul. Qed.
  Lemma of_Z_opp : forall x, of_Z (- x)%Z = D.opp (of_Z x). Proof. exact Z_D.h_opp. Qed.
  Definition h (x : GaussianIntegers.t) : D.t := D.add (of_Z (fst x)) (D.mul (of_Z (snd x)) D.i).
  Lemma h_zero : h GaussianIntegers.zero = D.zero.
  Proof. unfold h, GaussianIntegers.zero. cbn [fst snd]. rewrite of_Z_zero. ring. Qed.
  Lemma h_one : h GaussianIntegers.one = D.one.
  Proof. unfold h, GaussianIntegers.one. cbn [fst snd]. rewrite of_Z_zero, of_Z_one. ring. Qed.
  Lemma h_add : forall x y, h (GaussianIntegers.add x y) = D.add (h x) (h y).
  Proof. intros [a b] [c d]. unfold h, GaussianIntegers.add. cbn [fst snd]. rewrite !of_Z_add. ring. Qed.
  Lemma h_mul : forall x y, h (GaussianIntegers.mul x y) = D.mul (h x) (h y).
  Proof.
    intros [a b] [c d]. unfold h, GaussianIntegers.mul. cbn [fst snd].
    replace (a * c - b * d)%Z with (a * c + - (b * d))%Z by ring.
    rewrite !of_Z_add, of_Z_opp, !of_Z_mul.
    transitivity (D.add (D.add (D.mul (of_Z a) (of_Z c))
                    (D.mul (D.mul D.i D.i) (D.mul (of_Z b) (of_Z d))))
                  (D.mul (D.add (D.mul (of_Z a) (of_Z d)) (D.mul (of_Z b) (of_Z c))) D.i)).
    - rewrite D.i_squared. ring.
    - ring.
  Qed.
  Lemma h_opp : forall x, h (GaussianIntegers.opp x) = D.opp (h x).
  Proof. intros [a b]. unfold h, GaussianIntegers.opp. cbn [fst snd]. rewrite !of_Z_opp. ring. Qed.
End GaussianHom.

Module IdentityHom (A : CommutativeRing) <: RingHom A A.
  Definition h (x : A.t) : A.t := x.
  Lemma h_zero : h A.zero = A.zero. Proof. reflexivity. Qed.
  Lemma h_one : h A.one = A.one. Proof. reflexivity. Qed.
  Lemma h_add : forall x y, h (A.add x y) = A.add (h x) (h y). Proof. reflexivity. Qed.
  Lemma h_mul : forall x y, h (A.mul x y) = A.mul (h x) (h y). Proof. reflexivity. Qed.
  Lemma h_opp : forall x, h (A.opp x) = A.opp (h x). Proof. reflexivity. Qed.
End IdentityHom.

Module GaussianIdentity := IdentityHom GaussianIntegers.

Lemma gaussian_regular : forall d x : GaussianIntegers.t,
  d <> GaussianIntegers.zero -> GaussianIntegers.mul d x = GaussianIntegers.zero -> x = GaussianIntegers.zero.
Proof.
  intros [a b] [c e] Hd E. unfold GaussianIntegers.mul, GaussianIntegers.zero in *. cbn [fst snd] in E.
  injection E as E1 E2.
  assert (N : ((a * a + b * b) * (c * c + e * e) = 0)%Z).
  { replace ((a * a + b * b) * (c * c + e * e))%Z
      with ((a * c - b * e) * (a * c - b * e) + (a * e + b * c) * (a * e + b * c))%Z by ring.
    rewrite E1, E2. reflexivity. }
  apply Z.mul_eq_0 in N. destruct N as [N | N].
  - exfalso. apply Hd. assert (a = 0%Z) by nia. assert (b = 0%Z) by nia. subst. reflexivity.
  - assert (c = 0%Z) by nia. assert (e = 0%Z) by nia. subst. reflexivity.
Qed.
