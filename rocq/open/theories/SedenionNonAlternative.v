(** * SedenionNonAlternative: the sedenions are not left alternative.

    Successor of SedenionAlternativityFails.v, whose bytes stay as retained
    records cite them.  That file declares two sign constants, both +1, for
    e_1 * e_10 and e_1 * e_11 and concludes that left alternativity fails
    on the basis pair (e_1, e_10).  Its constants are not the signs of the
    sedenion product, and its existential statement does not mention the
    product.  This file states the corrected facts on the product itself.

    Convention: [sed_mul] of Sedenion.v, the Cayley-Dickson doubling
    (a,b)(c,d) = (ac - conj(d) b, d a + b conj(c)) over the reals, with
    basis units [sed_e i] for i < 16 and basis signs
    [sed_sign i j = cd_sign_fuel 5 16 i j], so that
    e_i * e_j = sed_sign i j * e_(i xor j)
    (CDFusedBilinear.sed_mul_fused_basis_xor on [sed_mul_fused], carried to
    [sed_mul] by CDFusedBilinear.sed_mul_fused_eq).

    Results:
    - [sed_sign_1_10], [sed_sign_1_11]: the two signs are -1 and +1, and
      their product is -1, the value left alternativity requires.
    - [sed_basis_unit_left_alternative]: for every basis unit e_i and every
      sedenion y, e_i (e_i y) = (e_i e_i) y.  Every repeated basis unit
      satisfies the left alternative law, so a witness of its failure
      repeats a sum of basis units.
    - [sed_left_alternator_witness]: for a = e_1 + e_10 and b = e_4,
      (a a) b - a (a b) = 2 e_15.
    - [sedenion_not_left_alternative]: some a, b have (a a) b <> a (a b). *)

From Stdlib Require Import ZArith Arith Reals Lra Lia.
From OpenGororoba Require Import
  Prelude CayleyDicksonAlgebra Sedenion OctonionNorm CDSignBridge
  CDFusedBilinear.
Open Scope R_scope.

(** ** The signs the predecessor declared. *)

Theorem sed_sign_1_10 : sed_sign 1 10 = (-1)%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem sed_sign_1_11 : sed_sign 1 11 = 1%Z.
Proof. vm_compute. reflexivity. Qed.

(** The product of the two signs is -1, so e_1 (e_1 e_10) = -e_10, which
    is (e_1 e_1) e_10. *)
Theorem sed_sign_1_10_1_11 : (sed_sign 1 10 * sed_sign 1 11)%Z = (-1)%Z.
Proof. vm_compute. reflexivity. Qed.

Theorem sed_e1_e10 : sed_mul (sed_e 1) (sed_e 10) = sed_neg (sed_e 11).
Proof.
  vm_compute.
  apply (f_equal2 mkSed); apply (f_equal2 mkOct); apply (f_equal4 mkQuat);
    ring.
Qed.

Theorem sed_e1_e11 : sed_mul (sed_e 1) (sed_e 11) = sed_e 10.
Proof.
  vm_compute.
  apply (f_equal2 mkSed); apply (f_equal2 mkOct); apply (f_equal4 mkQuat);
    ring.
Qed.

(** ** Left alternativity holds when the repeated operand is a basis unit. *)

Theorem sed_basis_unit_left_alternative : forall (i : nat) (y : CDSed),
  (i < 16)%nat ->
  sed_mul (sed_e i) (sed_mul (sed_e i) y) =
    sed_mul (sed_mul (sed_e i) (sed_e i)) y.
Proof.
  intros i y Hi.
  destruct y as [[[y0 y1 y2 y3] [y4 y5 y6 y7]]
                 [[y8 y9 y10 y11] [y12 y13 y14 y15]]].
  assert (Hcases :
    i = 0%nat \/ i = 1%nat \/ i = 2%nat \/ i = 3%nat \/
    i = 4%nat \/ i = 5%nat \/ i = 6%nat \/ i = 7%nat \/
    i = 8%nat \/ i = 9%nat \/ i = 10%nat \/ i = 11%nat \/
    i = 12%nat \/ i = 13%nat \/ i = 14%nat \/ i = 15%nat)
    by lia.
  destruct_nat_disjunction Hcases.
  all: vm_compute.
  all: apply (f_equal2 mkSed); apply (f_equal2 mkOct);
    apply (f_equal4 mkQuat); ring.
Qed.

(** ** A witness with a two-term first operand. *)

Definition sed_alt_a : CDSed := sed_add (sed_e 1) (sed_e 10).
Definition sed_alt_b : CDSed := sed_e 4.

Theorem sed_left_alternator_witness :
  sed_sub (sed_mul (sed_mul sed_alt_a sed_alt_a) sed_alt_b)
          (sed_mul sed_alt_a (sed_mul sed_alt_a sed_alt_b)) =
    sed_scale 2 (sed_e 15).
Proof.
  vm_compute.
  apply (f_equal2 mkSed); apply (f_equal2 mkOct); apply (f_equal4 mkQuat);
    ring.
Qed.

Theorem sed_left_alternator_witness_neq :
  sed_mul (sed_mul sed_alt_a sed_alt_a) sed_alt_b <>
    sed_mul sed_alt_a (sed_mul sed_alt_a sed_alt_b).
Proof.
  intro H.
  pose proof sed_left_alternator_witness as Hw.
  rewrite H in Hw.
  assert (Hd := f_equal (fun s => qd (oct_hi (sed_hi s))) Hw).
  vm_compute in Hd.
  lra.
Qed.

(** Instance bridge: the Lean theorem
    lean/GororobaMath/CayleyDickson/Alternative.lean,
    [CayleyDickson.Tower.exists_left_alternative_ne], at R = the reals and
    k = 4 (so m = 0 and [lift 4 0] is the identity), states that some x, y
    in [Tower R 4] have x * x * y <> x * (x * y).  Its witness
    x = e 1 + e 10, y = e 4 is [sed_alt_a], [sed_alt_b] here, and its
    alternator 2 e 15 (associator_witness_left) is the one of
    [sed_left_alternator_witness]. *)
Theorem sedenion_not_left_alternative :
  exists a b : CDSed,
    sed_mul (sed_mul a a) b <> sed_mul a (sed_mul a b).
Proof.
  exists sed_alt_a, sed_alt_b.
  exact sed_left_alternator_witness_neq.
Qed.
