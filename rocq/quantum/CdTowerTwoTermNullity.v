(** A basis of the kernel of left multiplication by a two-term operand:
    the Rocq bridge of two headline theorems of the Lean module
    lean/GororobaMath/CayleyDickson/TwoTermNullity.lean.

    Convention: the tower, product and basis of CdTowerRing.v and
    CdTowerRingBasis.v, (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)),
    with basis k i the basis vector of index i below 2^k, whose top index
    bit selects the second half of the pair; CdTowerBasisBridge.v ties
    basis k i to Lean's e R k p at the bit vector p of value i, makes
    Nat.lxor the index of p ^^^ q, and makes TowerSign.neg_sign Lean's
    Tower.negSign with the same argument order. The coordinate
    (Tower.basis R k).repr y p of Lean is coord k y i at the value i of p,
    the Lean negation -x is scale k neg_one x, Lean's 2 is two =
    D.add D.one D.one, and the left multiplication mulLeft R k a of Lean
    is mul k a. The alignment test and the count are those of
    CdTowerTwoTermBridge.v and CdTowerTwoTermRecursion.v: partner,
    aligned_add and aligned_sub of IntegerTwoTermBridge, which do not
    depend on the coefficient ring, and TwoTermRecursion.aligned_pair_count,
    Lean's Tower.alignedPairCount (ci/compare_aligned_pair_count.sh
    compares the two counts).

    The functor TwoTermNullityBridge fixes, for the operand e_i + e_j, the
    representatives x of the aligned pairs, x < partner i j x
    (is_rep), and at each one the vector kernel_vector k i j x, which is
    e_x + e_x' when the pair is aligned with opposite signs (aligned_add)
    and e_x - e_x' otherwise, x' = partner i j x: the zero divisors of
    two_term_mul_add_eq_zero and two_term_mul_sub_eq_zero of
    CdTowerTwoTermBridge.v. kernel_combination k i j c is the combination
    of these vectors with the coefficients c x. It restates the two
    headline theorems at the coefficient ring D, for i and j below 2^k
    (i = j included), when 2 is a non-zero-divisor of D
    (two_regular, Lean's IsLeftRegular (2 : R)):

    - kernel_basis is the reading of Tower.free_ker_mulLeft_e_add_e that
      Stdlib supports: the vectors kernel_vector k i j x at the
      representatives x lie in the kernel of left multiplication by
      e_i + e_j, every combination of them does, every vector of the
      kernel is the combination with its own coordinates at the
      representatives, the coordinate of a combination at a
      representative is its coefficient, and a vanishing combination has
      every coefficient zero. They form a basis of the kernel, so the
      kernel is free.
    - kernel_rank is the reading of Tower.finrank_ker_mulLeft_e_add_e:
      the same basis, and the number of representatives below 2^k is
      TwoTermRecursion.aligned_pair_count k i j.

    The proof follows the Lean one. The coordinate of (e_i + e_j) y at
    i XOR x is the signed sum of the coordinates of y at x and at x'
    (repr_e_mul of CdTowerModuleBridge.v), so a kernel vector satisfies
    y x = y x' when the signs of e_i e_x and e_j e_x' differ and
    y x = -y x' when they agree (kernel_coord_relation). An aligned pair
    has the same relation at both ends and one free coordinate, its
    representative; a pair whose two relations disagree, or the fixed
    point x = x' that i = j gives, forces y x = -y x, hence y x = 0 when 2
    cancels.

    The Rocq statements are narrower than the Lean ones: an index is a
    nat below 2^k, where Lean takes a BitVec k; kernel_basis states one
    basis of the kernel indexed by the representatives, where Lean's
    Module.Free asserts that some basis exists, and kernel_rank states
    the size of that basis, where Lean's finrank is the size of every
    basis over a nontrivial commutative ring, an invariance (invariant
    basis number) that Stdlib does not state; the Rocq statements also
    hold over the zero ring, which Lean's Nontrivial hypothesis excludes.
    The coefficient ring is the same, a commutative ring whose
    conjugation is the identity in which 2 is a non-zero-divisor.
    IntegerTwoTermNullityBridge instantiates the functor at the integers,
    where 2 is a non-zero-divisor and no unit, and
    integer_kernel_rank_e1_e18 is Lean's
    Tower.finrank_ker_pathion_1_18_int: the kernel of e_1 + e_18 at
    level 5 has a basis of twelve vectors. *)

From Stdlib Require Import Bool Ring Lia PeanoNat ZArith List Btauto.
Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange.
Require CdTowerBasisSign.
Require Import CdTowerBasisBridge CdTowerTwoTermBridge CdTowerModuleBridge CdTowerTwoTermRecursion.
Import ListNotations.

Module TwoTermNullityBridge (D : CommutativeRing).
Module MB := TowerModuleBridge D.
Module TT := TwoTermBridge D.
Import MB MB.BB MB.BB.B MB.BB.B.T TowerSign.
Add Ring two_term_nullity_ring : D.ring_th.

Abbreviation partner := IntegerTwoTermBridge.partner.
Abbreviation aligned_add := IntegerTwoTermBridge.aligned_add.
Abbreviation aligned_sub := IntegerTwoTermBridge.aligned_sub.

Ltac bits := apply Nat.bits_inj; intro; rewrite ?Nat.lxor_spec, ?Nat.bits_0; btauto.

(** Lean's IsLeftRegular (2 : R). *)
Definition two_regular : Prop := forall a b, D.mul two a = D.mul two b -> a = b.

(** The representative of an aligned pair: its smaller index. *)
Definition is_rep (k i j x : nat) : bool :=
  andb (orb (aligned_add k i j x) (aligned_sub k i j x)) (Nat.ltb x (partner i j x)).

(** e_x + e_x' for a pair aligned with opposite signs, e_x - e_x'
    otherwise. *)
Definition kernel_vector (k i j x : nat) : cd k :=
  if aligned_add k i j x then add k (basis k x) (basis k (partner i j x))
  else add k (basis k x) (scale k neg_one (basis k (partner i j x))).

Definition kernel_combination (k i j : nat) (c : nat -> D.t) : cd k :=
  tsum k (Nat.pow 2 k) (fun x => if is_rep k i j x then scale k (c x) (kernel_vector k i j x) else zero k).

(** The coefficient of e_x' in kernel_vector k i j x. *)
Definition pair_coefficient (k i j x : nat) : D.t := if aligned_add k i j x then D.one else neg_one.

(** The coordinate relation at x is y x = y x' when pair_relation holds
    and y x = -y x' otherwise. *)
Definition pair_relation (k i j x : nat) : bool := xorb (neg_sign k i x) (neg_sign k j (partner i j x)).

Lemma dsum_add n g h : dsum n (fun m => D.add (g m) (h m)) = D.add (dsum n g) (dsum n h).
Proof. induction n as [|m IH]; cbn [dsum]; [ring | rewrite IH; ring]. Qed.

Lemma tsum_zero k n : tsum k n (fun _ => zero k) = zero k.
Proof.
  apply ext. intros w _. rewrite coord_tsum, coord_zero. apply dsum_zero.
Qed.

Lemma partner_eqb_swap i j x w : Nat.eqb (partner i j x) w = Nat.eqb x (partner i j w).
Proof.
  rewrite !TwoTermRecursion.partner_xor. apply TwoTermRecursion.lxor_eqb_move.
Qed.

Lemma partner_lt' k i j x : (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat -> (x < Nat.pow 2 k)%nat ->
  (partner i j x < Nat.pow 2 k)%nat.
Proof. apply IntegerTwoTermBridge.partner_lt. Qed.

Lemma coord_kernel_vector k i j x w :
  (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat -> (x < Nat.pow 2 k)%nat -> (w < Nat.pow 2 k)%nat ->
  coord k (kernel_vector k i j x) w =
  D.add (if Nat.eqb x w then D.one else D.zero)
    (D.mul (pair_coefficient k i j x) (if Nat.eqb (partner i j x) w then D.one else D.zero)).
Proof.
  intros Hi Hj Hx Hw. pose proof (partner_lt' k i j x Hi Hj Hx) as Hp.
  unfold kernel_vector, pair_coefficient. destruct (aligned_add k i j x);
    rewrite coord_add, ?coord_scale, !coord_basis by assumption; unfold neg_one; ring.
Qed.

Lemma coord_kernel_combination k i j c w :
  (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat -> (w < Nat.pow 2 k)%nat ->
  coord k (kernel_combination k i j c) w =
  D.add (if is_rep k i j w then c w else D.zero)
    (if is_rep k i j (partner i j w) then D.mul (c (partner i j w)) (pair_coefficient k i j (partner i j w))
     else D.zero).
Proof.
  intros Hi Hj Hw. pose proof (partner_lt' k i j w Hi Hj Hw) as Hp.
  unfold kernel_combination. rewrite coord_tsum.
  rewrite (dsum_ext _ _ (fun x =>
    D.add (D.mul (if is_rep k i j x then c x else D.zero) (if Nat.eqb x w then D.one else D.zero))
      (D.mul (if is_rep k i j x then D.mul (c x) (pair_coefficient k i j x) else D.zero)
        (if Nat.eqb x (partner i j w) then D.one else D.zero)))).
  - rewrite dsum_add, !dsum_delta, (proj2 (Nat.ltb_lt _ _) Hw), (proj2 (Nat.ltb_lt _ _) Hp). reflexivity.
  - intros x Hx. destruct (is_rep k i j x).
    + rewrite coord_scale, coord_kernel_vector, partner_eqb_swap by assumption. ring.
    + rewrite coord_zero. ring.
Qed.

Lemma rep_partner k i j x : is_rep k i j x = true -> is_rep k i j (partner i j x) = false.
Proof.
  unfold is_rep. rewrite TwoTermRecursion.partner_partner. intro H.
  apply andb_prop in H. destruct H as [_ H]. apply Nat.ltb_lt in H.
  destruct (Nat.ltb_spec (partner i j x) x); [lia |]. apply andb_false_r.
Qed.

(** The coordinate relation of a kernel vector at x. *)
Lemma kernel_coord_relation k i j y x :
  (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat -> (x < Nat.pow 2 k)%nat ->
  mul k (add k (basis k i) (basis k j)) y = zero k ->
  coord k y x = if pair_relation k i j x then coord k y (partner i j x) else D.opp (coord k y (partner i j x)).
Proof.
  intros Hi Hj Hx H. pose proof (CdTowerBasisSign.lxor_lt k i x Hi Hx) as Hix.
  pose proof (f_equal (fun v => coord k v (Nat.lxor i x)) H) as E. cbv beta in E.
  rewrite coord_zero, mul_add_l, coord_add, !repr_e_mul in E by assumption.
  replace (Nat.lxor i (Nat.lxor i x)) with x in E by bits.
  replace (Nat.lxor j (Nat.lxor i x)) with (partner i j x) in E by (unfold IntegerTwoTermBridge.partner; bits).
  unfold pair_relation. revert E.
  generalize (coord k y x) (coord k y (partner i j x)). intros a b E.
  destruct (neg_sign k i x), (neg_sign k j (partner i j x)); cbn [xorb].
  - transitivity (D.add (D.opp (D.add (D.opp a) (D.opp b))) (D.opp b)); [ring | rewrite E; ring].
  - transitivity (D.add (D.opp (D.add (D.opp a) b)) b); [ring | rewrite E; ring].
  - transitivity (D.add (D.add a (D.opp b)) b); [ring | rewrite E; ring].
  - transitivity (D.add (D.add a b) (D.opp b)); [ring | rewrite E; ring].
Qed.

Lemma aligned_relation k i j x :
  orb (aligned_add k i j x) (aligned_sub k i j x) =
  Bool.eqb (pair_relation k i j x) (pair_relation k i j (partner i j x)).
Proof.
  unfold IntegerTwoTermBridge.aligned_add, IntegerTwoTermBridge.aligned_sub, pair_relation.
  rewrite TwoTermRecursion.partner_partner.
  destruct (neg_sign k i x), (neg_sign k j (partner i j x)), (neg_sign k j x),
    (neg_sign k i (partner i j x)); reflexivity.
Qed.

Lemma aligned_add_relation k i j x : orb (aligned_add k i j x) (aligned_sub k i j x) = true ->
  aligned_add k i j x = pair_relation k i j x.
Proof.
  unfold IntegerTwoTermBridge.aligned_add, IntegerTwoTermBridge.aligned_sub, pair_relation.
  destruct (neg_sign k i x), (neg_sign k j (partner i j x)), (neg_sign k j x),
    (neg_sign k i (partner i j x)); cbn; congruence.
Qed.

Lemma cancel_two (H2 : two_regular) a : a = D.opp a -> a = D.zero.
Proof.
  intro E. assert (Haa : D.add a a = D.zero) by (transitivity (D.add a (D.opp a)); [congruence | ring]).
  apply H2. transitivity (D.add a a); [unfold two; ring | rewrite Haa; unfold two; ring].
Qed.

(** Tower.free_ker_mulLeft_e_add_e: the vectors kernel_vector k i j x at
    the representatives x form a basis of the kernel of left
    multiplication by e_i + e_j. *)
Theorem kernel_basis (H2 : two_regular) k i j : (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat ->
  (forall x, (x < Nat.pow 2 k)%nat -> is_rep k i j x = true ->
     mul k (add k (basis k i) (basis k j)) (kernel_vector k i j x) = zero k) /\
  (forall c, mul k (add k (basis k i) (basis k j)) (kernel_combination k i j c) = zero k) /\
  (forall y, mul k (add k (basis k i) (basis k j)) y = zero k -> y = kernel_combination k i j (coord k y)) /\
  (forall c x, (x < Nat.pow 2 k)%nat -> is_rep k i j x = true -> coord k (kernel_combination k i j c) x = c x) /\
  (forall c, kernel_combination k i j c = zero k ->
     forall x, (x < Nat.pow 2 k)%nat -> is_rep k i j x = true -> c x = D.zero).
Proof.
  intros Hi Hj.
  assert (Hmem : forall x, (x < Nat.pow 2 k)%nat -> is_rep k i j x = true ->
    mul k (add k (basis k i) (basis k j)) (kernel_vector k i j x) = zero k).
  { intros x Hx R. unfold kernel_vector. unfold is_rep in R. apply andb_prop in R. destruct R as [A _].
    destruct (aligned_add k i j x) eqn:Add.
    - exact (TT.two_term_mul_add_eq_zero k i j x Hi Hj Hx Add).
    - cbn [orb] in A. exact (TT.two_term_mul_sub_eq_zero k i j x Hi Hj Hx A). }
  assert (Hcoef : forall c x, (x < Nat.pow 2 k)%nat -> is_rep k i j x = true ->
    coord k (kernel_combination k i j c) x = c x).
  { intros c x Hx R. rewrite coord_kernel_combination, R, rep_partner by assumption. ring. }
  split; [exact Hmem |]. split; [| split; [| split; [exact Hcoef |]]].
  - intro c. unfold kernel_combination.
    rewrite (linear_tsum k _ _ _ (proj2 (mul_bilinear k) (add k (basis k i) (basis k j)))).
    rewrite (tsum_ext k _ _ (fun _ => zero k)); [apply tsum_zero |].
    intros x Hx. destruct (is_rep k i j x) eqn:R.
    + rewrite mul_scale_r, Hmem by assumption. apply scale_zero.
    + apply mul_zero_r.
  - intros y Hy. apply ext. intros w Hw. pose proof (partner_lt' k i j w Hi Hj Hw) as Hp.
    rewrite coord_kernel_combination by assumption.
    destruct (is_rep k i j w) eqn:Rw.
    + rewrite (rep_partner k i j w Rw). ring.
    + destruct (is_rep k i j (partner i j w)) eqn:Rp.
      * pose proof (kernel_coord_relation k i j y (partner i j w) Hi Hj Hp Hy) as E.
        rewrite TwoTermRecursion.partner_partner in E.
        assert (A : orb (aligned_add k i j (partner i j w)) (aligned_sub k i j (partner i j w)) = true)
          by (unfold is_rep in Rp; apply andb_prop in Rp; apply Rp).
        unfold pair_coefficient. rewrite (aligned_add_relation k i j _ A). rewrite E.
        destruct (pair_relation k i j (partner i j w)); unfold neg_one; ring.
      * transitivity D.zero; [| ring]. apply (cancel_two H2).
        pose proof (kernel_coord_relation k i j y w Hi Hj Hw Hy) as Ew.
        destruct (Nat.eq_dec (partner i j w) w) as [Fix | Nfix].
        -- pose proof (TwoTermRecursion.partner_eq_self i j w Fix) as <-.
           unfold pair_relation in Ew. rewrite Fix, Bool.xorb_nilpotent in Ew. exact Ew.
        -- pose proof (kernel_coord_relation k i j y (partner i j w) Hi Hj Hp Hy) as Ep.
           rewrite TwoTermRecursion.partner_partner in Ep.
           assert (N : orb (aligned_add k i j w) (aligned_sub k i j w) = false).
           { unfold is_rep in Rw, Rp.
             rewrite TwoTermRecursion.aligned_misaligned, TwoTermRecursion.misaligned_partner,
               <- TwoTermRecursion.aligned_misaligned, TwoTermRecursion.partner_partner in Rp.
             destruct (orb (aligned_add k i j w) (aligned_sub k i j w)); [| reflexivity].
             cbn [andb] in Rw, Rp. apply Nat.ltb_ge in Rw. apply Nat.ltb_ge in Rp. lia. }
           rewrite aligned_relation in N.
           revert Ew Ep N. generalize (coord k y w) (coord k y (partner i j w)). intros a b Ew Ep N.
           destruct (pair_relation k i j w), (pair_relation k i j (partner i j w)); cbn in N; try discriminate N;
             rewrite Ep in Ew; exact Ew.
  - intros c Z x Hx R. rewrite <- (Hcoef c x Hx R), Z. apply coord_zero.
Qed.

(** The representatives below 2^k number aligned_pair_count k i j. *)
Lemma rep_length k i j : (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat ->
  length (filter (is_rep k i j) (seq 0 (Nat.pow 2 k))) = TwoTermRecursion.aligned_pair_count k i j.
Proof.
  intros Hi Hj. rewrite TwoTermRecursion.length_filter_seq, TwoTermRecursion.aligned_pair_count_reps by assumption.
  unfold TwoTermRecursion.rep_count. apply TwoTermRecursion.nsum_ext. intros x _.
  unfold is_rep. rewrite TwoTermRecursion.aligned_misaligned. reflexivity.
Qed.

(** Tower.finrank_ker_mulLeft_e_add_e: the kernel of left multiplication
    by e_i + e_j has a basis of aligned_pair_count k i j vectors. *)
Theorem kernel_rank (H2 : two_regular) k i j : (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat ->
  ((forall x, (x < Nat.pow 2 k)%nat -> is_rep k i j x = true ->
      mul k (add k (basis k i) (basis k j)) (kernel_vector k i j x) = zero k) /\
   (forall c, mul k (add k (basis k i) (basis k j)) (kernel_combination k i j c) = zero k) /\
   (forall y, mul k (add k (basis k i) (basis k j)) y = zero k -> y = kernel_combination k i j (coord k y)) /\
   (forall c x, (x < Nat.pow 2 k)%nat -> is_rep k i j x = true -> coord k (kernel_combination k i j c) x = c x) /\
   (forall c, kernel_combination k i j c = zero k ->
      forall x, (x < Nat.pow 2 k)%nat -> is_rep k i j x = true -> c x = D.zero)) /\
  length (filter (is_rep k i j) (seq 0 (Nat.pow 2 k))) = TwoTermRecursion.aligned_pair_count k i j.
Proof. intros Hi Hj. split; [apply kernel_basis | apply rep_length]; assumption. Qed.

End TwoTermNullityBridge.

Module IntegerTwoTermNullityBridge := TwoTermNullityBridge IntegerRing.

(** 2 is a non-zero-divisor of the integers. *)
Lemma integer_two_regular : IntegerTwoTermNullityBridge.two_regular.
Proof.
  unfold IntegerTwoTermNullityBridge.two_regular, IntegerTwoTermNullityBridge.MB.BB.B.T.two.
  cbv [IntegerRing.mul IntegerRing.add IntegerRing.one]. intros a b E. lia.
Qed.

(** Tower.finrank_ker_pathion_1_18_int: over the integers the kernel of
    left multiplication by e_1 + e_18 at level 5 has a basis of twelve
    vectors kernel_vector 5 1 18 x. *)
Theorem integer_kernel_rank_e1_e18 :
  let L := IntegerTwoTermNullityBridge.MB.BB.B.T.mul 5
    (IntegerTwoTermNullityBridge.MB.BB.B.T.add 5 (IntegerTwoTermNullityBridge.MB.BB.B.basis 5 1)
      (IntegerTwoTermNullityBridge.MB.BB.B.basis 5 18)) in
  (forall y, L y = IntegerTwoTermNullityBridge.MB.BB.B.T.zero 5 ->
     y = IntegerTwoTermNullityBridge.kernel_combination 5 1 18 (IntegerTwoTermNullityBridge.MB.BB.B.T.coord 5 y)) /\
  (forall c, IntegerTwoTermNullityBridge.kernel_combination 5 1 18 c = IntegerTwoTermNullityBridge.MB.BB.B.T.zero 5 ->
     forall x, (x < Nat.pow 2 5)%nat -> IntegerTwoTermNullityBridge.is_rep 5 1 18 x = true -> c x = 0%Z) /\
  length (filter (IntegerTwoTermNullityBridge.is_rep 5 1 18) (seq 0 (Nat.pow 2 5))) = 12%nat.
Proof.
  destruct (IntegerTwoTermNullityBridge.kernel_rank integer_two_regular 5 1 18
    ltac:(cbn; lia) ltac:(cbn; lia)) as [[_ [_ [S [_ I]]]] N].
  split; [exact S | split; [exact I |]]. rewrite N. vm_compute. reflexivity.
Qed.

(** The twelve representatives of e_1 + e_18 at level 5, and the vector at
    the representative 5, e_5 + e_22: the zero divisor of
    pathion_e1_add_e18_mul_e5_add_e22 of CdTowerTwoTermBridge.v. *)
Example integer_kernel_vectors_e1_e18 :
  filter (IntegerTwoTermNullityBridge.is_rep 5 1 18) (seq 0 32) = [4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15]%nat /\
  IntegerTwoTermNullityBridge.kernel_vector 5 1 18 5 =
    IntegerTwoTermNullityBridge.MB.BB.B.T.add 5 (IntegerTwoTermNullityBridge.MB.BB.B.basis 5 5)
      (IntegerTwoTermNullityBridge.MB.BB.B.basis 5 22).
Proof. vm_compute. split; reflexivity. Qed.
