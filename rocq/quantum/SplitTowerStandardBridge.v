(** The split tower at the standard signature is the tower of CdTowerDomain.v.

    Convention: SplitDoublingTower.v multiplies (a, b)(c, d) = (a c + gamma_n conj(d) b,
    d a + b conj(c)) and CdTowerDomain.v multiplies (a, b)(c, d) = (a c - conj(d) b,
    d a + b conj(c)), both over the integers with the pair shape of the level. With
    gamma_n = -1 at every level the two products agree on every pair of elements of the levels
    2 and 3, a coordinate identity that the ring tactic closes. *)

From Stdlib Require Import ZArith Ring.
Require Import CdTowerDomain.
Require Import SplitDoublingTower.

Definition standard_signature : nat -> Z := fun _ => (-1)%Z.

Ltac coordinates :=
  cbn [ZT.mul ZT.add ZT.smul ZT.conj ZT.neg ZTower.mul ZTower.add ZTower.scale
       ZTower.conjugate fst snd];
  repeat (match goal with
          | |- (_, _) = (_, _) => apply pair_equal_spec; split
          end);
  cbv [ZTower.neg_one ZT.V ZTower.cd ZRing.t ZDomain.t ZRing.zero ZRing.one ZRing.add ZRing.mul ZRing.sub ZRing.opp
       ZDomain.zero ZDomain.one ZDomain.add ZDomain.mul ZDomain.sub ZDomain.opp];
  try change (ZT.V 0) with Z in *;
  try change (ZTower.cd 0) with Z in *;
  ring.

Theorem split_tower_standard_level2 : forall x y : ZT.V 2,
  ZT.mul 2 standard_signature x y = ZTower.mul 2 x y.
Proof.
  intros [[a0 a1] [a2 a3]] [[b0 b1] [b2 b3]].
  unfold standard_signature, ZTower.neg_one. coordinates.
Qed.
Print Assumptions split_tower_standard_level2.

Theorem split_tower_standard_level3 : forall x y : ZT.V 3,
  ZT.mul 3 standard_signature x y = ZTower.mul 3 x y.
Proof.
  intros [[[a0 a1] [a2 a3]] [[a4 a5] [a6 a7]]]
         [[[b0 b1] [b2 b3]] [[b4 b5] [b6 b7]]].
  unfold standard_signature, ZTower.neg_one. coordinates.
Qed.
Print Assumptions split_tower_standard_level3.
