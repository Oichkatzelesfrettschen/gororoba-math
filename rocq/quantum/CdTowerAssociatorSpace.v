(** The associator space of two basis vectors: the Rocq bridge of two
    headline theorems of the Lean module
    lean/GororobaMath/CayleyDickson/AssociatorSpace.lean.

    Convention: the tower, product and basis of CdTowerRing.v and
    CdTowerRingBasis.v, read through CdTowerBasisBridge.v and
    CdTowerTwoTermNullity.v: basis k i is Lean's e R k p at the bit vector
    p of value i below 2^k, Nat.lxor is the index of p ^^^ q,
    TowerSign.neg_sign is Lean's Tower.negSign with the same argument
    order, coord k y i is the coordinate (Tower.basis R k).repr y p, and
    the coefficient ring is a commutative ring whose conjugation is the
    identity (Lean's CommRing with TrivialStar). two_regular of
    CdTowerTwoTermNullity.v is Lean's IsLeftRegular (2 : R).

    The associator space of e_a and e_b, Lean's
    Tower.assocSpace R k (e R k a) (e R k b), is the set of y with
    (e_a y) e_b = e_a (y e_b); the statements below write that equation
    for each vector they place in the space. associates k a b c is Lean's
    Tower.associates a b c: true when (e_a e_c) e_b and e_a (e_c e_b) carry
    the same sign, the signs of e_a e_c, e_(a XOR c) e_b, e_c e_b and
    e_a e_(c XOR b) compared through Bool.eqb (Lean's == on Bool).
    ci/compare_aligned_pair_forms.sh evaluates both definitions on every
    triple of indices at the levels up to 5 and rejects a mutated Rocq
    reference.

    The functor AssociatorSpaceBridge restates, at the coefficient ring D,
    for a and b below 2^k:

    - assoc_basis is Tower.free_assocSpace_e with an explicit basis: for
      all a and b, when 2 is a non-zero-divisor, the basis vectors e_x at
      the indices x with associates k a b x lie in the associator space,
      every combination of them does, every vector of the space is the
      combination with its own coordinates at those indices, the
      coordinate of a combination at such an index is its coefficient,
      and a vanishing combination has every coefficient zero.
    - assoc_rank is the reading of Tower.finrank_assocSpace_e: for nonzero
      distinct a and b, the same basis, and the number of indices x below
      2^k with associates k a b x is
      2 * TwoTermRecursion.aligned_pair_count k a b + 4.

    The proof follows the Lean one. On the basis both products are signed
    copies of e_(a XOR x XOR b) (coord_assoc_left, coord_assoc_right, with
    repr_mul_e the right-multiplication partner of repr_e_mul of
    CdTowerModuleBridge.v), so y lies in the space exactly when every
    coordinate at a non-associating index satisfies y x = -y x, hence
    y x = 0 when 2 cancels (assoc_iff). The count is
    AssociatorSign.associates_count: associates_eq (Lean's
    Tower.associates_eq, from neg_sign_xor_right and neg_sign_swap_xor)
    makes an index outside {0, a, b, a XOR b} associate exactly when it is
    aligned under e_a + e_b, the four special indices associate and are
    never aligned (misaligned_special of CdTowerTwoTermRecursion.v), and
    the aligned indices number 2 * aligned_pair_count k a b.

    assoc_basis states as much as Lean's Module.Free and more: an explicit
    basis is a witness of freeness, where Lean asserts that one exists.
    Stdlib holds no submodule of the associator space and no Module.Free,
    so the basis is stated by the properties of its vectors rather than
    packaged as a linear equivalence (Lean's assocSpaceEquivFun).
    assoc_rank is narrower than Lean's finrank: it gives the size of this
    one basis, where finrank is the size of every basis over a nontrivial
    commutative ring, an invariance (invariant basis number) that Stdlib
    does not state. Both Rocq statements take an index as a nat below 2^k,
    where Lean takes a BitVec k, and hold over the zero ring as well,
    which Lean's Nontrivial hypothesis of the finrank theorem excludes.
    IntegerAssociatorSpace instantiates the functor at the integers, and
    integer_assoc_rank_e1_e18 gives the associator space of e_1 and e_18
    at level 5 a basis of 2 * 12 + 4 = 28 vectors, with 12 Lean's
    Tower.alignedPairCount_pathion_1_18. *)

From Stdlib Require Import Bool Ring Lia PeanoNat ZArith List Btauto.
Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange.
Require CdTowerBasisSign.
Require Import CdTowerBasisBridge CdTowerTwoTermBridge CdTowerModuleBridge CdTowerTwoTermRecursion
  CdTowerTwoTermNullity.
Import ListNotations.

Ltac xbits := apply Nat.bits_inj; intro; rewrite ?Nat.lxor_spec, ?Nat.bits_0; btauto.

Ltac decide_eqb :=
  repeat match goal with |- context [Nat.eqb ?x ?y] => destruct (Nat.eqb_spec x y); try (exfalso; congruence) end.

Module AssociatorSign.
Import TowerSign TwoTermRecursion.

(** Tower.associates: true when (e_a e_c) e_b and e_a (e_c e_b) carry the
    same sign. *)
Definition associates (k a b c : nat) : bool :=
  Bool.eqb (xorb (neg_sign k a c) (neg_sign k (Nat.lxor a c) b))
    (xorb (neg_sign k c b) (neg_sign k a (Nat.lxor c b))).

(** Tower.associates_eq: the associativity sign of (e_a, e_c, e_b) is the
    alignment sign of c under e_a + e_b, corrected by four indicator
    terms. *)
Lemma associates_eq k a b c : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat -> (c < Nat.pow 2 k)%nat ->
  associates k a b c =
  negb (xorb (xorb (xorb (xorb (misaligned k a b c) (negb (Nat.eqb a 0))) (tr c b)) (negb (Nat.eqb b 0)))
    (tr (Nat.lxor a c) b)).
Proof.
  intros Ha Hb Hc.
  pose proof (CdTowerBasisSign.lxor_lt k c b Hc Hb) as Hcb.
  pose proof (CdTowerBasisSign.lxor_lt k a c Ha Hc) as Hac.
  unfold associates, misaligned.
  replace (neg_sign k a (IntegerTwoTermBridge.partner a b c))
    with (xorb (negb (Nat.eqb a 0)) (neg_sign k a (Nat.lxor c b))).
  2: { replace (IntegerTwoTermBridge.partner a b c) with (Nat.lxor a (Nat.lxor c b))
         by (unfold IntegerTwoTermBridge.partner; xbits).
       symmetry. apply neg_sign_xor_right; assumption. }
  replace (neg_sign k b (IntegerTwoTermBridge.partner a b c))
    with (xorb (negb (Nat.eqb b 0)) (neg_sign k b (Nat.lxor a c))).
  2: { replace (IntegerTwoTermBridge.partner a b c) with (Nat.lxor b (Nat.lxor a c))
         by (unfold IntegerTwoTermBridge.partner; xbits).
       symmetry. apply neg_sign_xor_right; assumption. }
  rewrite (neg_sign_swap_xor k c b Hc Hb), (neg_sign_swap_xor k (Nat.lxor a c) b Hac Hb).
  destruct (neg_sign k a c), (neg_sign k (Nat.lxor a c) b), (neg_sign k c b), (neg_sign k a (Nat.lxor c b)),
    (Nat.eqb a 0), (Nat.eqb b 0), (tr c b), (tr (Nat.lxor a c) b); reflexivity.
Qed.

Lemma lxor_cancel_l a b : Nat.lxor a (Nat.lxor a b) = b.
Proof. xbits. Qed.

(** Tower.card_associates: for nonzero distinct a and b, the indices that
    associate number 2 * aligned_pair_count k a b + 4. *)
Lemma associates_count k a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  a <> O -> b <> O -> a <> b ->
  length (filter (associates k a b) (seq 0 (Nat.pow 2 k))) = (2 * aligned_pair_count k a b + 4)%nat.
Proof.
  intros Ha Hb Ha0 Hb0 Hab. rewrite length_filter_seq.
  pose proof (CdTowerBasisSign.lxor_lt k a b Ha Hb) as Hc.
  assert (Hx0 : Nat.lxor a b <> O) by (intro E; apply Hab; apply Nat.lxor_eq; exact E).
  assert (Hxa : Nat.lxor a b <> a)
    by (intro E; apply Hb0; replace b with (Nat.lxor a (Nat.lxor a b)) by xbits; rewrite E; apply Nat.lxor_nilpotent).
  assert (Hxb : Nat.lxor a b <> b)
    by (intro E; apply Ha0; replace a with (Nat.lxor (Nat.lxor a b) b) by xbits; rewrite E; apply Nat.lxor_nilpotent).
  rewrite (nsum_ext _ _ (fun y =>
    ind (negb (misaligned k a b y)) + ind (Nat.eqb y 0) + ind (Nat.eqb y a) + ind (Nat.eqb y b) +
    ind (Nat.eqb y (Nat.lxor a b)))%nat).
  - rewrite !nsum_add, !nsum_delta by (assumption || lia).
    pose proof (aligned_count_two_mul k a b Ha Hb Hab) as E. unfold aligned_count in E. lia.
  - intros y Hy. rewrite associates_eq by assumption.
    destruct (Nat.eq_dec y 0) as [E | H0]; [| destruct (Nat.eq_dec y a) as [E | Hya];
      [| destruct (Nat.eq_dec y b) as [E | Hyb]; [| destruct (Nat.eq_dec y (Nat.lxor a b)) as [E | Hyc]]]].
    5: { assert (Hay0 : Nat.lxor a y <> O) by (intro E; apply Hya; symmetry; apply Nat.lxor_eq; exact E).
         assert (Hayb : Nat.lxor a y <> b) by (intro E; apply Hyc; rewrite <- E; symmetry; apply lxor_cancel_l).
         unfold tr. decide_eqb. destruct (misaligned k a b y); reflexivity. }
    all: destruct (misaligned_special k a b y Ha Hb Ha0 Hb0 Hab ltac:(tauto)) as [M _];
      rewrite M; subst y; rewrite ?Nat.lxor_0_r, ?Nat.lxor_nilpotent, ?lxor_cancel_l;
      unfold tr; decide_eqb; reflexivity.
Qed.

End AssociatorSign.

Module AssociatorSpaceBridge (D : CommutativeRing).
Module NB := TwoTermNullityBridge D.
Import NB.MB NB.MB.BB NB.MB.BB.B NB.MB.BB.B.T TowerSign AssociatorSign.
Add Ring associator_space_ring : D.ring_th.

Definition sg (s : bool) (v : D.t) : D.t := if s then D.opp v else v.

(** The right-multiplication partner of Tower.repr_e_mul: right
    multiplication by e_b is a signed permutation of coordinates. *)
Lemma repr_mul_e k b w y : (b < Nat.pow 2 k)%nat -> (w < Nat.pow 2 k)%nat ->
  coord k (mul k y (basis k b)) w = sg (neg_sign k (Nat.lxor w b) b) (coord k y (Nat.lxor w b)).
Proof.
  intros Hb Hw. pose proof (CdTowerBasisSign.lxor_lt k w b Hw Hb) as Hwb.
  assert (Ey : mul k y (basis k b) =
    mul k (tsum k (Nat.pow 2 k) (fun m => scale k (coord k y m) (basis k m))) (basis k b))
    by (f_equal; apply decompose).
  pose proof (linear_tsum k (fun x => mul k x (basis k b)) (Nat.pow 2 k)
    (fun m => scale k (coord k y m) (basis k m)) (proj1 (mul_bilinear k) (basis k b))) as T.
  cbv beta in T. rewrite Ey, T, coord_tsum.
  rewrite (dsum_ext _ _ (fun m => D.mul (D.mul (coord k y m) (ring_sign k m b))
    (if Nat.eqb m (Nat.lxor w b) then D.one else D.zero))).
  - rewrite dsum_delta, (proj2 (Nat.ltb_lt _ _) Hwb). unfold sg, ring_sign, neg_one.
    destruct (neg_sign k (Nat.lxor w b) b); ring.
  - intros m Hm. pose proof (CdTowerBasisSign.lxor_lt k m b Hm Hb) as Hmb.
    rewrite mul_scale_l, coord_scale, basis_mul_ring_sign, coord_scale, coord_basis by assumption.
    rewrite TwoTermRecursion.lxor_eqb_move. ring.
Qed.

(** The coordinate of (e_a y) e_b at a XOR x XOR b. *)
Lemma coord_assoc_left k a b x y : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat -> (x < Nat.pow 2 k)%nat ->
  coord k (mul k (mul k (basis k a) y) (basis k b)) (Nat.lxor (Nat.lxor a x) b) =
  sg (xorb (neg_sign k a x) (neg_sign k (Nat.lxor a x) b)) (coord k y x).
Proof.
  intros Ha Hb Hx. pose proof (CdTowerBasisSign.lxor_lt k a x Ha Hx) as Hax.
  pose proof (CdTowerBasisSign.lxor_lt k _ b Hax Hb) as Haxb.
  rewrite repr_mul_e by assumption.
  replace (Nat.lxor (Nat.lxor (Nat.lxor a x) b) b) with (Nat.lxor a x) by xbits.
  rewrite repr_e_mul by assumption. rewrite lxor_cancel_l.
  unfold sg. destruct (neg_sign k a x), (neg_sign k (Nat.lxor a x) b); cbn [xorb]; ring.
Qed.

(** The coordinate of e_a (y e_b) at a XOR x XOR b. *)
Lemma coord_assoc_right k a b x y : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat -> (x < Nat.pow 2 k)%nat ->
  coord k (mul k (basis k a) (mul k y (basis k b))) (Nat.lxor (Nat.lxor a x) b) =
  sg (xorb (neg_sign k x b) (neg_sign k a (Nat.lxor x b))) (coord k y x).
Proof.
  intros Ha Hb Hx. pose proof (CdTowerBasisSign.lxor_lt k a x Ha Hx) as Hax.
  pose proof (CdTowerBasisSign.lxor_lt k _ b Hax Hb) as Haxb.
  pose proof (CdTowerBasisSign.lxor_lt k x b Hx Hb) as Hxb.
  rewrite repr_e_mul by assumption.
  replace (Nat.lxor a (Nat.lxor (Nat.lxor a x) b)) with (Nat.lxor x b) by xbits.
  rewrite repr_mul_e by assumption.
  replace (Nat.lxor (Nat.lxor x b) b) with x by xbits.
  unfold sg. destruct (neg_sign k a (Nat.lxor x b)), (neg_sign k x b); cbn [xorb]; ring.
Qed.

(** Tower.mem_assocSpace_e_iff: when 2 cancels, y lies in the associator
    space of e_a and e_b exactly when it vanishes at every index that does
    not associate. *)
Lemma assoc_iff (H2 : NB.two_regular) k a b y : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  mul k (mul k (basis k a) y) (basis k b) = mul k (basis k a) (mul k y (basis k b)) <->
  forall x, (x < Nat.pow 2 k)%nat -> associates k a b x = false -> coord k y x = D.zero.
Proof.
  intros Ha Hb. split.
  - intros E x Hx A.
    pose proof (f_equal (fun v => coord k v (Nat.lxor (Nat.lxor a x) b)) E) as C. cbv beta in C.
    rewrite coord_assoc_left, coord_assoc_right in C by assumption.
    unfold associates in A. apply (NB.cancel_two H2). revert C A. unfold sg.
    destruct (xorb (neg_sign k a x) (neg_sign k (Nat.lxor a x) b)),
      (xorb (neg_sign k x b) (neg_sign k a (Nat.lxor x b))); cbn; intros C A;
      [discriminate A | symmetry; exact C | exact C | discriminate A].
  - intros Z. apply ext. intros w Hw.
    pose proof (CdTowerBasisSign.lxor_lt k a w Ha Hw) as Haw.
    pose proof (CdTowerBasisSign.lxor_lt k _ b Haw Hb) as Hx.
    replace w with (Nat.lxor (Nat.lxor a (Nat.lxor (Nat.lxor a w) b)) b) by xbits.
    rewrite coord_assoc_left, coord_assoc_right by assumption.
    destruct (associates k a b (Nat.lxor (Nat.lxor a w) b)) eqn:A.
    + unfold associates in A. apply Bool.eqb_prop in A. rewrite A. reflexivity.
    + rewrite (Z _ Hx A). unfold sg. destruct (xorb _ _), (xorb _ _); ring.
Qed.

(** The combination of the basis vectors e_x at the associating indices x
    with the coefficients c x. *)
Definition assoc_combination k a b (c : nat -> D.t) : cd k :=
  tsum k (Nat.pow 2 k) (fun x => if associates k a b x then scale k (c x) (basis k x) else zero k).

Lemma coord_assoc_combination k a b c w : (w < Nat.pow 2 k)%nat ->
  coord k (assoc_combination k a b c) w = if associates k a b w then c w else D.zero.
Proof.
  intro Hw. unfold assoc_combination. rewrite coord_tsum.
  rewrite (dsum_ext _ _ (fun x => D.mul (if associates k a b x then c x else D.zero)
    (if Nat.eqb x w then D.one else D.zero))).
  - rewrite dsum_delta, (proj2 (Nat.ltb_lt _ _) Hw). reflexivity.
  - intros x Hx. destruct (associates k a b x).
    + rewrite coord_scale, coord_basis by assumption. reflexivity.
    + rewrite coord_zero. ring.
Qed.

(** Tower.free_assocSpace_e: the basis vectors e_x at the associating
    indices x form a basis of the associator space of e_a and e_b. *)
Theorem assoc_basis (H2 : NB.two_regular) k a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  (forall x, (x < Nat.pow 2 k)%nat -> associates k a b x = true ->
     mul k (mul k (basis k a) (basis k x)) (basis k b) = mul k (basis k a) (mul k (basis k x) (basis k b))) /\
  (forall c, mul k (mul k (basis k a) (assoc_combination k a b c)) (basis k b) =
     mul k (basis k a) (mul k (assoc_combination k a b c) (basis k b))) /\
  (forall y, mul k (mul k (basis k a) y) (basis k b) = mul k (basis k a) (mul k y (basis k b)) ->
     y = assoc_combination k a b (coord k y)) /\
  (forall c x, (x < Nat.pow 2 k)%nat -> associates k a b x = true -> coord k (assoc_combination k a b c) x = c x) /\
  (forall c, assoc_combination k a b c = zero k ->
     forall x, (x < Nat.pow 2 k)%nat -> associates k a b x = true -> c x = D.zero).
Proof.
  intros Ha Hb.
  assert (Hcoef : forall c x, (x < Nat.pow 2 k)%nat -> associates k a b x = true ->
    coord k (assoc_combination k a b c) x = c x)
    by (intros c x Hx A; rewrite coord_assoc_combination, A by assumption; reflexivity).
  split; [| split; [| split; [| split; [exact Hcoef |]]]].
  - intros x Hx A. apply (proj2 (assoc_iff H2 k a b _ Ha Hb)). intros z Hz Az.
    rewrite coord_basis by assumption. destruct (Nat.eqb_spec x z) as [<- | _]; [congruence | reflexivity].
  - intro c. apply (proj2 (assoc_iff H2 k a b _ Ha Hb)). intros z Hz Az.
    rewrite coord_assoc_combination, Az by assumption. reflexivity.
  - intros y Hy. pose proof (proj1 (assoc_iff H2 k a b y Ha Hb) Hy) as Z.
    apply ext. intros w Hw. rewrite coord_assoc_combination by assumption.
    destruct (associates k a b w) eqn:A; [reflexivity | exact (Z w Hw A)].
  - intros c E x Hx A. rewrite <- (Hcoef c x Hx A), E. apply coord_zero.
Qed.

(** Tower.finrank_assocSpace_e: for nonzero distinct a and b the
    associator space of e_a and e_b has a basis of
    2 * aligned_pair_count k a b + 4 vectors. *)
Theorem assoc_rank (H2 : NB.two_regular) k a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  a <> O -> b <> O -> a <> b ->
  ((forall x, (x < Nat.pow 2 k)%nat -> associates k a b x = true ->
      mul k (mul k (basis k a) (basis k x)) (basis k b) = mul k (basis k a) (mul k (basis k x) (basis k b))) /\
   (forall c, mul k (mul k (basis k a) (assoc_combination k a b c)) (basis k b) =
      mul k (basis k a) (mul k (assoc_combination k a b c) (basis k b))) /\
   (forall y, mul k (mul k (basis k a) y) (basis k b) = mul k (basis k a) (mul k y (basis k b)) ->
      y = assoc_combination k a b (coord k y)) /\
   (forall c x, (x < Nat.pow 2 k)%nat -> associates k a b x = true -> coord k (assoc_combination k a b c) x = c x) /\
   (forall c, assoc_combination k a b c = zero k ->
      forall x, (x < Nat.pow 2 k)%nat -> associates k a b x = true -> c x = D.zero)) /\
  length (filter (associates k a b) (seq 0 (Nat.pow 2 k))) =
    (2 * TwoTermRecursion.aligned_pair_count k a b + 4)%nat.
Proof.
  intros Ha Hb Ha0 Hb0 Hab. split; [apply assoc_basis; assumption | apply associates_count; assumption].
Qed.

End AssociatorSpaceBridge.

Module IntegerAssociatorSpace := AssociatorSpaceBridge IntegerRing.

(** 2 is a non-zero-divisor of the integers. *)
Lemma integer_assoc_two_regular : IntegerAssociatorSpace.NB.two_regular.
Proof.
  unfold IntegerAssociatorSpace.NB.two_regular, IntegerAssociatorSpace.NB.MB.BB.B.T.two.
  cbv [IntegerRing.mul IntegerRing.add IntegerRing.one]. intros a b E. lia.
Qed.

(** Tower.finrank_assocSpace_e at k = 5, a = 1, b = 18 over the integers:
    the associator space of e_1 and e_18 has a basis of 28 vectors e_x,
    2 * 12 + 4 with 12 = Tower.alignedPairCount_pathion_1_18. *)
Theorem integer_assoc_rank_e1_e18 :
  (forall y, IntegerAssociatorSpace.NB.MB.BB.B.T.mul 5
      (IntegerAssociatorSpace.NB.MB.BB.B.T.mul 5 (IntegerAssociatorSpace.NB.MB.BB.B.basis 5 1) y)
      (IntegerAssociatorSpace.NB.MB.BB.B.basis 5 18) =
    IntegerAssociatorSpace.NB.MB.BB.B.T.mul 5 (IntegerAssociatorSpace.NB.MB.BB.B.basis 5 1)
      (IntegerAssociatorSpace.NB.MB.BB.B.T.mul 5 y (IntegerAssociatorSpace.NB.MB.BB.B.basis 5 18)) ->
    y = IntegerAssociatorSpace.assoc_combination 5 1 18 (IntegerAssociatorSpace.NB.MB.BB.B.T.coord 5 y)) /\
  length (filter (AssociatorSign.associates 5 1 18) (seq 0 (Nat.pow 2 5))) = 28%nat.
Proof.
  destruct (IntegerAssociatorSpace.assoc_rank integer_assoc_two_regular 5 1 18
    ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as [[_ [_ [S _]]] N].
  split; [exact S |]. rewrite N. vm_compute. reflexivity.
Qed.

(** The associating indices of e_1 and e_18 at level 5 include the four
    special indices 0, 1, 18 and 19 = 1 XOR 18, and the 24 others are the
    aligned indices of e_1 + e_18. *)
Example integer_associating_indices_e1_e18 :
  map (AssociatorSign.associates 5 1 18) [0; 1; 18; 19]%nat = [true; true; true; true] /\
  length (filter (fun x => andb (AssociatorSign.associates 5 1 18 x)
    (negb (TwoTermRecursion.misaligned 5 1 18 x))) (seq 0 32)) = 24%nat.
Proof. vm_compute. split; reflexivity. Qed.
