(** A structure-preserving bridge from the open recursive real tower
    (OpenGororoba.RecursiveCDTower: cd_tower, tower_mul, highest bit in the
    second pair component) to the real instance of the quantum functor
    (CdTowerDomain.RTower: cd, mul, coordinates below 2^j in the first pair
    component). Both towers double with
    (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)) and conj(a, b) =
    (conj a, -b); the open tower writes negation as Ropp and the quantum
    functor as scaling by neg_one, and the base case of to_quantum_neg is
    the ring identity -x = (-1) x. to_quantum is the identity on every
    coordinate and has the two-sided inverse of_quantum. The open basis unit
    of cube_decode a is the quantum unit with coordinate 1 at a and 0
    elsewhere, so the open basis-product theorem transports to the quantum
    tower. Before the proof, an exhaustive computation over the integer
    instance ZTower compares every quantum basis product at levels 1 to 5
    with the sign law sign_exponent that the open tower satisfies. *)

From Stdlib Require Import Reals ZArith Lia Bool List.
From OpenGororoba Require Import RecursiveCDTower SchreierSignCode
  CDTowerSignCorrespondence CDSignNumericCorrespondence CDAssociatorDoubling.
Require CdTowerDomain.

Locate Library OpenGororoba.RecursiveCDTower.
Locate Library CdTowerDomain.

Module Q := CdTowerDomain.RTower.
Module ZT := CdTowerDomain.ZTower.

(** Computed comparison over the integers: the quantum unit e_a of the
    integer functor instance, every product e_a e_b, against
    phase_sign (sign_exponent k a b) e_(a xor b) on every coordinate. *)

Fixpoint z_unit (k a : nat) : ZT.cd k :=
  match k as d return ZT.cd d with
  | O => 1%Z
  | S j => if Nat.ltb a (Nat.pow 2 j) then (z_unit j a, ZT.zero j)
           else (ZT.zero j, z_unit j (a - Nat.pow 2 j))
  end.

Definition z_coords (k : nat) (v : ZT.cd k) : list Z :=
  map (ZT.coord k v) (seq 0 (Nat.pow 2 k)).

Definition open_sign (k a b : nat) : Z :=
  phase_sign (sign_exponent k (cube_decode k a) (cube_decode k b)).

Definition product_agrees (k a b : nat) : bool :=
  forallb (fun pair => Z.eqb (fst pair) (snd pair))
    (combine (z_coords k (ZT.mul k (z_unit k a) (z_unit k b)))
             (z_coords k (ZT.scale k (open_sign k a b) (z_unit k (Nat.lxor a b))))).

Definition level_agrees (k : nat) : bool :=
  forallb (fun a => forallb (fun b => product_agrees k a b) (seq 0 (Nat.pow 2 k)))
    (seq 0 (Nat.pow 2 k)).

(** Calibration: a unit with the wrong sign at one pair is rejected. *)
Example computed_rejects_flipped_sign :
  Z.eqb (ZT.coord 3 (ZT.mul 3 (z_unit 3 1) (z_unit 3 2)) 3)
        (- ZT.coord 3 (ZT.scale 3 (open_sign 3 1 2) (z_unit 3 3)) 3) = false.
Proof. vm_compute. reflexivity. Qed.

Example computed_levels_one_to_five :
  level_agrees 1 && level_agrees 2 && level_agrees 3 && level_agrees 4 && level_agrees 5 = true.
Proof. vm_compute. reflexivity. Qed.

(** The bridge. *)

Fixpoint to_quantum (k : nat) : cd_tower k -> Q.cd k :=
  match k as d return cd_tower d -> Q.cd d with
  | O => fun v => v
  | S j => fun v => (to_quantum j (fst v), to_quantum j (snd v))
  end.

Fixpoint of_quantum (k : nat) : Q.cd k -> cd_tower k :=
  match k as d return Q.cd d -> cd_tower d with
  | O => fun v => v
  | S j => fun v => (of_quantum j (fst v), of_quantum j (snd v))
  end.

Lemma of_to_quantum k : forall v, of_quantum k (to_quantum k v) = v.
Proof. induction k as [|j IH]; intro v; [reflexivity|]. destruct v; simpl. rewrite !IH. reflexivity. Qed.

Lemma to_of_quantum k : forall v, to_quantum k (of_quantum k v) = v.
Proof. induction k as [|j IH]; intro v; [reflexivity|]. destruct v; simpl. rewrite !IH. reflexivity. Qed.

Lemma to_quantum_zero k : to_quantum k (tower_zero k) = Q.zero k.
Proof. induction k as [|j IH]; simpl; [reflexivity | rewrite IH; reflexivity]. Qed.

Lemma to_quantum_add k : forall x y, to_quantum k (tower_add k x y) = Q.add k (to_quantum k x) (to_quantum k y).
Proof. induction k as [|j IH]; intros x y; [reflexivity|]. destruct x, y; simpl. rewrite !IH. reflexivity. Qed.

Lemma to_quantum_scale k : forall r x, to_quantum k (tower_scale k r x) = Q.scale k r (to_quantum k x).
Proof. induction k as [|j IH]; intros r x; [reflexivity|]. destruct x; simpl. rewrite !IH. reflexivity. Qed.

Lemma to_quantum_neg k : forall x, to_quantum k (tower_neg k x) = Q.scale k Q.neg_one (to_quantum k x).
Proof.
  induction k as [|j IH]; intro x.
  - change ((- x)%R = ((- 1) * x)%R). ring.
  - destruct x; simpl. rewrite !IH. reflexivity.
Qed.

Lemma to_quantum_conj k : forall x, to_quantum k (tower_conj k x) = Q.conjugate k (to_quantum k x).
Proof. induction k as [|j IH]; intro x; [reflexivity|]. destruct x; simpl. rewrite IH, to_quantum_neg. reflexivity. Qed.

Theorem to_quantum_mul k : forall x y,
  to_quantum k (tower_mul k x y) = Q.mul k (to_quantum k x) (to_quantum k y).
Proof.
  induction k as [|j IH]; intros x y; [reflexivity|].
  destruct x as [a b], y as [c d]. cbn [tower_mul to_quantum Q.mul fst snd]. unfold tower_sub.
  rewrite !to_quantum_add, to_quantum_neg, !IH, !to_quantum_conj. reflexivity.
Qed.

Lemma to_quantum_real_part k : forall x, tower_real_part k x = Q.re k (to_quantum k x).
Proof. induction k as [|j IH]; intro x; [reflexivity|]. destruct x; simpl. apply IH. Qed.

Lemma to_quantum_norm k : forall x, tower_norm_sq k x = Q.dot k (to_quantum k x) (to_quantum k x).
Proof.
  induction k as [|j IH]; intro x.
  - change ((x ^ 2)%R = (x * x)%R). ring.
  - destruct x; simpl. rewrite !IH. reflexivity.
Qed.

(** Coordinates: the open basis unit of cube_decode a is the quantum vector
    with coordinate 1 at a and 0 at every other index below 2^k. *)

Fixpoint quantum_unit (k a : nat) : Q.cd k :=
  match k as d return Q.cd d with
  | O => 1%R
  | S j => if Nat.ltb a (Nat.pow 2 j) then (quantum_unit j a, Q.zero j)
           else (Q.zero j, quantum_unit j (a - Nat.pow 2 j))
  end.

Theorem to_quantum_basis k : forall a,
  to_quantum k (tower_basis k (cube_decode k a)) = quantum_unit k a.
Proof.
  induction k as [|j IH]; intro a; [reflexivity|].
  cbn [cube_decode]. destruct (Nat.ltb a (Nat.pow 2 j)) eqn:half;
  cbn [tower_basis to_quantum quantum_unit fst snd]; rewrite half, IH, to_quantum_zero; reflexivity.
Qed.

Theorem quantum_unit_coord k : forall a i, (a < Nat.pow 2 k)%nat -> (i < Nat.pow 2 k)%nat ->
  Q.coord k (quantum_unit k a) i = if Nat.eqb i a then 1%R else 0%R.
Proof.
  induction k as [|j IH]; intros a i Ha Hi.
  - simpl in Ha, Hi. assert (a = O) by lia. assert (i = O) by lia. subst. reflexivity.
  - simpl in Ha, Hi. cbn [quantum_unit Q.coord].
    destruct (Nat.ltb_spec a (Nat.pow 2 j)) as [La|La], (Nat.ltb_spec i (Nat.pow 2 j)) as [Li|Li];
      cbn [fst snd].
    + apply IH; assumption.
    + rewrite Q.coord_zero. replace (Nat.eqb i a) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
    + rewrite Q.coord_zero. replace (Nat.eqb i a) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
    + rewrite IH by lia. destruct (Nat.eqb_spec (i - Nat.pow 2 j) (a - Nat.pow 2 j)),
        (Nat.eqb_spec i a); try reflexivity; lia.
Qed.

Lemma to_quantum_signed k negative x :
  to_quantum k (tower_signed k negative x) =
  Q.scale k (if negative then Q.neg_one else 1%R) (to_quantum k x).
Proof.
  destruct negative; simpl; [apply to_quantum_neg|].
  symmetry. apply Q.ext. intros i _. rewrite Q.coord_scale.
  change ((1 * Q.coord k (to_quantum k x) i)%R = Q.coord k (to_quantum k x) i). ring.
Qed.

(** The open basis-product theorem read in the quantum tower. *)
Theorem quantum_basis_product k a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  Q.mul k (quantum_unit k a) (quantum_unit k b) =
  Q.scale k (if sign_exponent k (cube_decode k a) (cube_decode k b) then Q.neg_one else 1%R)
    (quantum_unit k (Nat.lxor a b)).
Proof.
  intros Ha Hb.
  rewrite <- !to_quantum_basis, <- to_quantum_mul, tower_basis_multiplication, to_quantum_signed.
  pose proof (cube_encode_xor k (cube_decode k a) (cube_decode k b)) as encoded_xor.
  rewrite !cube_encode_decode in encoded_xor by assumption.
  rewrite <- encoded_xor, cube_decode_encode. reflexivity.
Qed.

Print Assumptions to_quantum_mul.
Print Assumptions quantum_unit_coord.
Print Assumptions quantum_basis_product.
