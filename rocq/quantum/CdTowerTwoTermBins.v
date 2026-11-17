(** The exact nullity of a two-term kernel map and the aligned-pair count:
    the Rocq bridge of two headline theorems of the Lean module
    lean/GororobaMath/KernelMap/TwoTermBins.lean.

    Convention: the bins of the kernel map of the operand e_i + e_j at
    level k are the 2^k output basis states, indexed by the nats below 2^k
    (Lean's BitVec k, BitVec.toNat; the index order of
    CdTowerTwoTermRecursion.v, top bit outermost). The block of all bins is
    the list seq 0 (2^k), which holds each index once, where Lean takes
    Finset.univ. A labelling of the bins is pos : nat -> bool, true at a
    bin of ideal contrast +1 (Lean's pos : BitVec k -> Prop with its
    decidability, or BitVec k -> Bool in binContract).
    TwoTermRecursion.misaligned is Lean's Tower.misaligned,
    IntegerTwoTermBridge.partner Lean's Tower.partner (ci/compare_alignment.sh),
    and TwoTermRecursion.aligned_pair_count Lean's Tower.alignedPairCount
    (ci/compare_aligned_pair_count.sh). The nullity is Defs.nullity of
    KernelMapEstimator.v, Lean's KernelMap.nullity B pos =
    (|B+| - |B-|) / 2 over a field of characteristic zero
    (ci/compare_estimator_rocq.sh), with ofnat Lean's Nat.cast.

    bin_contract k i j pos is Lean's KernelMap.binContract k i j pos: every
    bin x below 2^k with misaligned k i j x false is labelled true, and
    every misaligned x carries the label opposite to that of its partner.
    ci/compare_aligned_pair_forms.sh evaluates both definitions on every
    labelling at the levels up to 3, on the contract labelling and its
    one-bin mutations at the levels 4 and 5, and rejects a mutated Rocq
    reference.

    The functor TwoTermBinsBridge restates, at a field F of characteristic
    zero (CharZeroField of KernelMapEstimator.v):

    - nullity_eq_aligned_pair_count is KernelMap.nullity_eq_alignedPairCount:
      for i <> j below 2^k and a labelling that marks every aligned index
      +1 and gives the two indices of each misaligned pair opposite labels,
      the nullity of the block of all bins is aligned_pair_count k i j.
    - nullity_eq_aligned_pair_count_of_bin_contract is
      KernelMap.nullity_eq_alignedPairCount_of_binContract: the same
      conclusion from bin_contract k i j pos = true.

    The proof follows the Lean one through the count identity
    TwoTermBins.pos_count_eq of the bins in nat, |B+| = |B-| +
    2 * aligned_pair_count k i j. An aligned index is a +1 bin; the
    misaligned +1 bins and the misaligned -1 bins are equinumerous through
    x -> partner i j x = x XOR (i XOR j) (nsum_lxor), which keeps
    misalignment (misaligned_partner) and reverses the label; and the
    aligned indices number 2 * aligned_pair_count k i j
    (aligned_count_two_mul). Halving in the field then needs 2 <> 0.

    The Rocq statements are narrower than the Lean ones in one respect: an
    index is a nat below 2^k, where Lean takes a BitVec k. The hypotheses
    quantify over the bins below 2^k, as Lean's quantify over BitVec k.
    RealTwoTermBins instantiates the functor at the real numbers, and
    real_nullity_e1_e18 reads the contract labelling of e_1 + e_18 at
    level 5 (+1 at every aligned index and at the smaller index of each
    misaligned pair): its 28 bins +1 and 4 bins -1 give the nullity 12,
    Lean's Tower.alignedPairCount_pathion_1_18. *)

From Stdlib Require Import Bool Lia PeanoNat List Field Reals.
Require Import CdTowerTwoTermBridge CdTowerTwoTermRecursion KernelMapEstimator.

Module TwoTermBins.
Import TwoTermRecursion.

Abbreviation partner := IntegerTwoTermBridge.partner.

(** KernelMap.binContract: aligned bins are +1 bins, and the two bins of a
    misaligned pair carry different labels. *)
Definition bin_contract (k i j : nat) (pos : nat -> bool) : bool :=
  forallb (fun x => if misaligned k i j x then negb (Bool.eqb (pos (partner i j x)) (pos x)) else pos x)
    (seq 0 (Nat.pow 2 k)).

(** Under the bin contract the +1 bins exceed the -1 bins by twice the
    aligned-pair count. *)
Lemma pos_count_eq k i j (pos : nat -> bool) :
  (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat -> i <> j ->
  (forall x, (x < Nat.pow 2 k)%nat -> misaligned k i j x = false -> pos x = true) ->
  (forall x, (x < Nat.pow 2 k)%nat -> misaligned k i j x = true -> pos (partner i j x) = negb (pos x)) ->
  nsum (Nat.pow 2 k) (fun x => ind (pos x)) =
    (nsum (Nat.pow 2 k) (fun x => ind (negb (pos x))) + 2 * aligned_pair_count k i j)%nat.
Proof.
  intros Hi Hj Hij Hal Hmis.
  pose proof (CdTowerBasisSign.lxor_lt k i j Hi Hj) as Hc.
  rewrite (nsum_ext _ (fun x => ind (pos x))
    (fun x => ind (negb (misaligned k i j x)) + ind (misaligned k i j x && pos x))%nat).
  2: { intros x Hx. destruct (misaligned k i j x) eqn:M; cbn [negb andb ind].
       - destruct (pos x); reflexivity.
       - rewrite (Hal x Hx M). reflexivity. }
  rewrite (nsum_ext _ (fun x => ind (negb (pos x))) (fun x => ind (misaligned k i j x && negb (pos x)))).
  2: { intros x Hx. destruct (misaligned k i j x) eqn:M; cbn [andb]; [reflexivity |].
       rewrite (Hal x Hx M). reflexivity. }
  rewrite nsum_add.
  rewrite <- (nsum_lxor k (Nat.lxor i j) (fun x => ind (misaligned k i j x && pos x)) Hc).
  rewrite (nsum_ext _ (fun x => ind (misaligned k i j (Nat.lxor x (Nat.lxor i j)) && pos (Nat.lxor x (Nat.lxor i j))))
    (fun x => ind (misaligned k i j x && negb (pos x)))).
  2: { intros x Hx. rewrite <- partner_xor, misaligned_partner.
       destruct (misaligned k i j x) eqn:M; cbn [andb]; [| reflexivity].
       rewrite (Hmis x Hx M). reflexivity. }
  pose proof (aligned_count_two_mul k i j Hi Hj Hij) as E. unfold aligned_count in E. lia.
Qed.

Lemma bin_contract_spec k i j (pos : nat -> bool) : bin_contract k i j pos = true ->
  (forall x, (x < Nat.pow 2 k)%nat -> misaligned k i j x = false -> pos x = true) /\
  (forall x, (x < Nat.pow 2 k)%nat -> misaligned k i j x = true -> pos (partner i j x) = negb (pos x)).
Proof.
  intro H. unfold bin_contract in H. rewrite forallb_forall in H.
  assert (C : forall x, (x < Nat.pow 2 k)%nat ->
    (if misaligned k i j x then negb (Bool.eqb (pos (partner i j x)) (pos x)) else pos x) = true).
  { intros x Hx. apply H. apply in_seq. lia. }
  split.
  - intros x Hx M. pose proof (C x Hx) as Cx. rewrite M in Cx. exact Cx.
  - intros x Hx M. pose proof (C x Hx) as Cx. rewrite M in Cx.
    destruct (pos (partner i j x)), (pos x); cbn in Cx |- *; congruence.
Qed.

End TwoTermBins.

Module TwoTermBinsBridge (F : CharZeroField).
Module E := Estimator F.
Import TwoTermRecursion.
Add Field two_term_bins_field : F.field_th.

(** KernelMap.nullity_eq_alignedPairCount: under the bin contract the
    exact nullity of the block of all 2^k bins is the aligned-pair count. *)
Theorem nullity_eq_aligned_pair_count k i j (pos : nat -> bool) :
  (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat -> i <> j ->
  (forall x, (x < Nat.pow 2 k)%nat -> misaligned k i j x = false -> pos x = true) ->
  (forall x, (x < Nat.pow 2 k)%nat -> misaligned k i j x = true ->
     pos (TwoTermBins.partner i j x) = negb (pos x)) ->
  E.D.nullity (seq 0 (Nat.pow 2 k)) pos = E.D.ofnat (aligned_pair_count k i j).
Proof.
  intros Hi Hj Hij Hal Hmis.
  pose proof (TwoTermBins.pos_count_eq k i j pos Hi Hj Hij Hal Hmis) as C.
  unfold E.D.nullity, E.D.posBins, E.D.negBins. rewrite !length_filter_seq. rewrite C.
  replace (2 * aligned_pair_count k i j)%nat with (aligned_pair_count k i j + aligned_pair_count k i j)%nat by lia.
  rewrite !E.ofnat_add. pose proof E.two_nonzero as T. unfold E.D.two in *. field. exact T.
Qed.

(** KernelMap.nullity_eq_alignedPairCount_of_binContract: a labelling for
    which bin_contract evaluates to true has exact nullity
    aligned_pair_count k i j. *)
Theorem nullity_eq_aligned_pair_count_of_bin_contract k i j (pos : nat -> bool) :
  (i < Nat.pow 2 k)%nat -> (j < Nat.pow 2 k)%nat -> i <> j -> TwoTermBins.bin_contract k i j pos = true ->
  E.D.nullity (seq 0 (Nat.pow 2 k)) pos = E.D.ofnat (aligned_pair_count k i j).
Proof.
  intros Hi Hj Hij H. destruct (TwoTermBins.bin_contract_spec k i j pos H) as [Hal Hmis].
  apply nullity_eq_aligned_pair_count; assumption.
Qed.

End TwoTermBinsBridge.

Module RealTwoTermBins := TwoTermBinsBridge RealField.

(** The contract labelling of e_1 + e_18 at level 5: +1 at every aligned
    index and at the smaller index of each misaligned pair. *)
Definition contract_labelling (k i j x : nat) : bool :=
  orb (negb (TwoTermRecursion.misaligned k i j x)) (Nat.ltb x (IntegerTwoTermBridge.partner i j x)).

(** It meets the contract and splits the 32 bins into 28 bins +1 and 4
    bins -1, 28 = 4 + 2 * 12; the labelling with bin 0 moved to -1 breaks
    the contract. *)
Example bin_contract_e1_e18 :
  TwoTermBins.bin_contract 5 1 18 (contract_labelling 5 1 18) = true /\
  TwoTermRecursion.nsum 32 (fun x => TwoTermRecursion.ind (contract_labelling 5 1 18 x)) = 28%nat /\
  TwoTermRecursion.nsum 32 (fun x => TwoTermRecursion.ind (negb (contract_labelling 5 1 18 x))) = 4%nat /\
  TwoTermRecursion.aligned_pair_count 5 1 18 = 12%nat /\
  TwoTermBins.bin_contract 5 1 18 (fun x => negb (Nat.eqb x 0) && contract_labelling 5 1 18 x) = false.
Proof. vm_compute. repeat split. Qed.

(** Over the reals the nullity of that block is 12. *)
Theorem real_nullity_e1_e18 :
  RealTwoTermBins.E.D.nullity (seq 0 32) (contract_labelling 5 1 18) = RealTwoTermBins.E.D.ofnat 12.
Proof.
  replace 12%nat with (TwoTermRecursion.aligned_pair_count 5 1 18) by (vm_compute; reflexivity).
  apply (RealTwoTermBins.nullity_eq_aligned_pair_count_of_bin_contract 5 1 18); [cbn; lia | cbn; lia | lia |].
  vm_compute. reflexivity.
Qed.
