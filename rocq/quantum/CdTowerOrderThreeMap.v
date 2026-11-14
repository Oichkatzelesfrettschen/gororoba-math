(** The order-three map of the sedenions preserves products, over every
    commutative ring with a square root of 3 and an inverse of 2.

    For octonions A and B write A = re(A) + A' and B = re(B) + B'. The map
    psi(A, B) = (re(A) - A'/2 + (r3/2) B', re(B) - B'/2 - (r3/2) A'), with
    r3 r3 = 3, fixes the real parts of both halves and turns the pair of
    imaginary parts by a third of a turn; it is Eq. 61 of Gresnigt (arXiv
    2609.10569) in the pair coordinates of level 4. psi2 = 2 psi has
    coefficients in Z[r3].

    - Root3Integers is Z[sqrt 3] as pairs of integers, and Root3Hom is the
      homomorphism from it to a ring with a square root of 3.
    - images_basis_check: over Z[sqrt 3], psi2(e_i) psi2(e_j) =
      2 psi2(e_i e_j) for all 256 basis pairs of level 4, by computation.
    - psi2_mul: psi2(x) psi2(y) = 2 psi2(x y) for all x, y of level 4 over
      every commutative ring with a square root of 3, by
      scaled_multiplicative_transport and the identification
      target_map_psi2 of the transported map with the formula.
    - psi2_conj: psi2 commutes with conjugation at every level.
    - psi_mul: with 2 inv2 = 1, psi = inv2 psi2 satisfies
      psi(x y) = psi(x) psi(y) at level 4.
    - psi_diagonal_mul: (a, b) -> (psi a, psi b) preserves the product of
      level 5, by RingTower.diag_mul.

    Instances: Root3Map applies OrderThreeMap to Z[sqrt 3] itself, and
    Mod11 applies OrderThreeAutomorphism to Zmod 11, where 5 5 = 3 and
    2 6 = 1, so both signatures are satisfiable.

    The file proves that psi preserves sums, scalars, products and
    conjugates. It does not prove that psi is a bijection or that its cube
    is the identity. *)

From Stdlib Require Import Ring Lia PeanoNat ZArith InitialRing Setoid Zmod.
Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange.

Module Type RingWithRoot3.
  Include CommutativeRing.
  Parameter r3 : t.
  Axiom r3_squared : mul r3 r3 = add one (add one one).
End RingWithRoot3.

(** Z[sqrt 3] as pairs (a, b) = a + b sqrt 3. *)
Module Root3Integers <: RingWithRoot3.
  Definition t := (Z * Z)%type.
  Definition zero : t := (0, 0)%Z.
  Definition one : t := (1, 0)%Z.
  Definition add (x y : t) : t := (fst x + fst y, snd x + snd y)%Z.
  Definition mul (x y : t) : t := (fst x * fst y + 3 * (snd x * snd y), fst x * snd y + snd x * fst y)%Z.
  Definition sub (x y : t) : t := (fst x - fst y, snd x - snd y)%Z.
  Definition opp (x : t) : t := (- fst x, - snd x)%Z.
  Lemma ring_th : ring_theory zero one add mul sub opp (@eq t).
  Proof.
    constructor; intros; repeat match goal with x : t |- _ => destruct x end;
      unfold zero, one, add, mul, sub, opp; cbn [fst snd]; f_equal; ring.
  Qed.
  Definition r3 : t := (0, 1)%Z.
  Lemma r3_squared : mul r3 r3 = add one (add one one).
  Proof. reflexivity. Qed.
End Root3Integers.

Module Root3Hom (D : RingWithRoot3) <: RingHom Root3Integers D.
  Module Z_D := IntegerHom D.
  Add Ring root3_target : D.ring_th.
  Definition of_Z : Z -> D.t := Z_D.h.
  Lemma of_Z_zero : of_Z 0%Z = D.zero. Proof. exact Z_D.h_zero. Qed.
  Lemma of_Z_one : of_Z 1%Z = D.one. Proof. exact Z_D.h_one. Qed.
  Lemma of_Z_add : forall x y, of_Z (x + y)%Z = D.add (of_Z x) (of_Z y). Proof. exact Z_D.h_add. Qed.
  Lemma of_Z_mul : forall x y, of_Z (x * y)%Z = D.mul (of_Z x) (of_Z y). Proof. exact Z_D.h_mul. Qed.
  Lemma of_Z_opp : forall x, of_Z (- x)%Z = D.opp (of_Z x). Proof. exact Z_D.h_opp. Qed.
  Definition h (x : Root3Integers.t) : D.t := D.add (of_Z (fst x)) (D.mul (of_Z (snd x)) D.r3).
  Lemma h_zero : h Root3Integers.zero = D.zero.
  Proof. unfold h, Root3Integers.zero. cbn [fst snd]. rewrite of_Z_zero. ring. Qed.
  Lemma h_one : h Root3Integers.one = D.one.
  Proof.
    unfold h, Root3Integers.one. cbn [fst snd]. rewrite of_Z_zero, of_Z_one. ring.
  Qed.
  Lemma h_add : forall x y, h (Root3Integers.add x y) = D.add (h x) (h y).
  Proof. intros [a b] [c d]. unfold h, Root3Integers.add. cbn [fst snd]. rewrite !of_Z_add. ring. Qed.
  Lemma h_three : of_Z 3%Z = D.add D.one (D.add D.one D.one).
  Proof.
    change 3%Z with (1 + (1 + 1))%Z. rewrite !of_Z_add, of_Z_one. reflexivity.
  Qed.
  Lemma h_mul : forall x y, h (Root3Integers.mul x y) = D.mul (h x) (h y).
  Proof.
    intros [a b] [c d]. unfold h, Root3Integers.mul. cbn [fst snd].
    rewrite !of_Z_add, !of_Z_mul, h_three.
    transitivity (D.add (D.add (D.mul (of_Z a) (of_Z c))
                    (D.mul (D.mul D.r3 D.r3) (D.mul (of_Z b) (of_Z d))))
                  (D.mul (D.add (D.mul (of_Z a) (of_Z d)) (D.mul (of_Z b) (of_Z c))) D.r3)).
    - rewrite D.r3_squared. ring.
    - ring.
  Qed.
  Lemma h_opp : forall x, h (Root3Integers.opp x) = D.opp (h x).
  Proof. intros [a b]. unfold h, Root3Integers.opp. cbn [fst snd]. rewrite !of_Z_opp. ring. Qed.
End Root3Hom.

Module OrderThreeMap (D : RingWithRoot3).
Module H := Root3Hom D.
Module BC := BaseChange Root3Integers D H.
Import BC.
Add Ring order_three_target : D.ring_th.

(** Twice the map psi: (A, B) -> (3 re(A) - A + r3 (B - re(B)), 3 re(B) - B - r3 (A - re(A))), over
    Z[sqrt 3] and over the target ring. *)
Definition source_three : Root3Integers.t := (3, 0)%Z.
Definition source_psi2 k (x : TA.cd (S k)) : TA.cd (S k) :=
  let im y := TA.add k y (TA.scale k (Root3Integers.opp (TA.re k y)) (TA.one k)) in
  (TA.add k (TA.add k (TA.scale k (Root3Integers.mul source_three (TA.re k (fst x))) (TA.one k))
                      (TA.scale k TA.neg_one (fst x)))
            (TA.scale k Root3Integers.r3 (im (snd x))),
   TA.add k (TA.add k (TA.scale k (Root3Integers.mul source_three (TA.re k (snd x))) (TA.one k))
                      (TA.scale k TA.neg_one (snd x)))
            (TA.scale k (Root3Integers.opp Root3Integers.r3) (im (fst x)))).

Definition images (m : nat) : TA.cd 4 := source_psi2 3 (SA.basis 4 m).

Lemma images_basis_check : forall i j, (i < Nat.pow 2 4)%nat -> (j < Nat.pow 2 4)%nat ->
  TA.mul 4 (source_map 4 images (SA.basis 4 i)) (source_map 4 images (SA.basis 4 j)) =
  TA.scale 4 (2, 0)%Z (source_map 4 images (TA.mul 4 (SA.basis 4 i) (SA.basis 4 j))).
Proof.
  intros i j Hi Hj. change (Nat.pow 2 4) with 16%nat in Hi, Hj.
  do 16 (destruct i as [|i];
    [ do 16 (destruct j as [|j]; [vm_compute; reflexivity |]); exfalso; lia |]).
  exfalso; lia.
Qed.

Theorem target_images_mul : forall x y,
  TB.mul 4 (target_map 4 images x) (target_map 4 images y) =
  TB.scale 4 TB.two (target_map 4 images (TB.mul 4 x y)).
Proof.
  intros x y. rewrite (scaled_multiplicative_transport 4 images (2, 0)%Z images_basis_check x y).
  f_equal. unfold H.h, TB.two. cbn [fst snd].
  change 2%Z with (1 + 1)%Z. rewrite H.of_Z_add, H.of_Z_one, H.of_Z_zero. ring.
Qed.

(** The same formula over the target ring. *)
Definition three : D.t := D.add D.one (D.add D.one D.one).
Definition imaginary k (y : TB.cd k) : TB.cd k := TB.add k y (TB.scale k (D.opp (TB.re k y)) (TB.one k)).
Definition psi2 k (x : TB.cd (S k)) : TB.cd (S k) :=
  (TB.add k (TB.add k (TB.scale k (D.mul three (TB.re k (fst x))) (TB.one k)) (TB.scale k TB.neg_one (fst x)))
            (TB.scale k D.r3 (imaginary k (snd x))),
   TB.add k (TB.add k (TB.scale k (D.mul three (TB.re k (snd x))) (TB.one k)) (TB.scale k TB.neg_one (snd x)))
            (TB.scale k (D.opp D.r3) (imaginary k (fst x)))).

Lemma h_source_three : H.h source_three = three.
Proof.
  unfold H.h, source_three, three. cbn [fst snd]. rewrite H.h_three, H.of_Z_zero. ring.
Qed.

Lemma h_r3 : H.h Root3Integers.r3 = D.r3.
Proof. unfold H.h, Root3Integers.r3. cbn [fst snd]. rewrite H.of_Z_zero, H.of_Z_one. ring. Qed.

Lemma tmap_source_psi2 k x : tmap (S k) (source_psi2 k x) = psi2 k (tmap (S k) x).
Proof.
  destruct x as [a b]. unfold source_psi2, psi2, imaginary. cbn [tmap fst snd].
  rewrite !tmap_add, !tmap_scale, !tmap_add, !tmap_scale, !tmap_one, !H.h_mul, !H.h_opp, <- !tmap_re,
    h_source_three, h_r3, h_neg_one.
  reflexivity.
Qed.

Ltac psi_vector :=
  apply TB.ext; intros ? _;
  repeat (rewrite TB.coord_add || rewrite TB.coord_scale || rewrite TB.coord_zero);
  unfold three, TB.neg_one, TB.two; ring.

Lemma psi2_linear k : SB.linear (S k) (psi2 k).
Proof.
  split.
  - intros [a b] [c d]. unfold psi2, imaginary. cbn [TB.add fst snd]. rewrite !SB.re_add. f_equal; psi_vector.
  - intros r [a b]. unfold psi2, imaginary. cbn [TB.scale fst snd]. rewrite !SB.re_scale. f_equal; psi_vector.
Qed.

Lemma source_map_images : forall i, (i < Nat.pow 2 4)%nat ->
  source_map 4 images (SA.basis 4 i) = source_psi2 3 (SA.basis 4 i).
Proof.
  intros i Hi. change (Nat.pow 2 4) with 16%nat in Hi.
  do 16 (destruct i as [|i]; [vm_compute; reflexivity |]). exfalso; lia.
Qed.

Lemma target_map_psi2 : forall x, target_map 4 images x = psi2 3 x.
Proof.
  apply (SB.linear_ext 4 _ _ (target_map_linear 4 images) (psi2_linear 3)). intros i Hi.
  rewrite <- tmap_basis, target_map_tmap, source_map_images by assumption. apply tmap_source_psi2.
Qed.

(** Twice psi multiplies as 2 psi2(x y) = psi2(x) psi2(y) at level 4, over every commutative ring with a
    square root of 3. *)
Theorem psi2_mul : forall x y, TB.mul 4 (psi2 3 x) (psi2 3 y) = TB.scale 4 TB.two (psi2 3 (TB.mul 4 x y)).
Proof. intros x y. rewrite <- !target_map_psi2. apply target_images_mul. Qed.

(** psi2 commutes with conjugation at every level. *)
Theorem psi2_conj k x : psi2 k (TB.conjugate (S k) x) = TB.conjugate (S k) (psi2 k x).
Proof.
  destruct x as [a b]. unfold psi2, imaginary. cbn [TB.conjugate fst snd].
  rewrite !TB.conj_add, !TB.conj_scale, !TB.conj_add, !TB.conj_scale, !TB.conj_one, !SB.re_conj, !SB.re_scale.
  rewrite (TB.conj_split k a), (TB.conj_split k b).
  f_equal; psi_vector.
Qed.

End OrderThreeMap.

(** With 1/2 in the ring, psi = psi2 / 2 preserves products at level 4, and its extension to both halves
    preserves products at level 5. *)

Module Type RingWithRoot3Half.
  Include RingWithRoot3.
  Parameter inv2 : t.
  Axiom two_inverse : mul (add one one) inv2 = one.
End RingWithRoot3Half.

Module OrderThreeAutomorphism (D : RingWithRoot3Half).
Module M := OrderThreeMap D.
Import M M.BC.
Add Ring order_three_half : D.ring_th.

Definition psi k (x : TB.cd (S k)) : TB.cd (S k) := TB.scale (S k) D.inv2 (psi2 k x).

Ltac half_vector :=
  apply TB.ext; intros index _;
  repeat (rewrite TB.coord_add || rewrite TB.coord_scale || rewrite TB.coord_zero).

Lemma psi_add k x y : psi k (TB.add (S k) x y) = TB.add (S k) (psi k x) (psi k y).
Proof. unfold psi. rewrite (proj1 (psi2_linear k)). half_vector. ring. Qed.

Lemma psi_scale k r x : psi k (TB.scale (S k) r x) = TB.scale (S k) r (psi k x).
Proof. unfold psi. rewrite (proj2 (psi2_linear k)). half_vector. ring. Qed.

Lemma psi_conj k x : psi k (TB.conjugate (S k) x) = TB.conjugate (S k) (psi k x).
Proof. unfold psi. rewrite psi2_conj, TB.conj_scale. reflexivity. Qed.

Theorem psi_mul : forall x y, psi 3 (TB.mul 4 x y) = TB.mul 4 (psi 3 x) (psi 3 y).
Proof.
  intros x y. unfold psi. rewrite TB.mul_scale_l, TB.mul_scale_r, psi2_mul. half_vector.
  unfold TB.two.
  transitivity (D.mul (D.mul (D.mul (D.add D.one D.one) D.inv2) D.inv2)
                  (TB.coord 4 (psi2 3 (TB.mul 4 x y)) index)).
  - rewrite D.two_inverse. ring.
  - ring.
Qed.

(** The extension (a, b) -> (psi a, psi b) to level 5 preserves products. *)
Theorem psi_diagonal_mul : forall x y,
  TB.diag 4 (psi 3) (TB.mul 5 x y) = TB.mul 5 (TB.diag 4 (psi 3) x) (TB.diag 4 (psi 3) y).
Proof.
  apply TB.diag_mul; [apply psi_add | apply psi_scale | apply psi_mul | apply psi_conj].
Qed.

End OrderThreeAutomorphism.

(** The signatures are satisfiable: Z[sqrt 3] for the square root of 3, and Zmod 11 with 5 5 = 3 and
    2 6 = 1 for the square root together with the inverse of 2. *)

Module Root3Map := OrderThreeMap Root3Integers.

Module Zmod11 <: RingWithRoot3Half.
  Definition t := Zmod 11.
  Definition zero : t := Zmod.zero.
  Definition one : t := Zmod.one.
  Definition add : t -> t -> t := Zmod.add.
  Definition mul : t -> t -> t := Zmod.mul.
  Definition sub : t -> t -> t := Zmod.sub.
  Definition opp : t -> t := Zmod.opp.
  Lemma ring_th : ring_theory zero one add mul sub opp (@eq t).
  Proof. exact (Zmod.ring_theory 11). Qed.
  Definition r3 : t := Zmod.of_Z 11 5.
  Lemma r3_squared : mul r3 r3 = add one (add one one).
  Proof. vm_compute. reflexivity. Qed.
  Definition inv2 : t := Zmod.of_Z 11 6.
  Lemma two_inverse : mul (add one one) inv2 = one.
  Proof. vm_compute. reflexivity. Qed.
End Zmod11.

Module Mod11 := OrderThreeAutomorphism Zmod11.
