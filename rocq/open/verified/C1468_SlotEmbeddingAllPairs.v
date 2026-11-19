(** * C-1468 successor: zero-divisor 2-blade pairs under 16-element slot shifts.

    Convention.  A level-[n] Cayley-Dickson vector is a nested pair of
    depth [n] (type [tz n], integer coordinates), the same shape as
    [cd_tower n] of [RecursiveCDTower]: the first component of a pair is
    the low half, the second the high half, so a natural-number index
    [i < 2^n] has its highest bit in the outermost pair, as in
    [cube_decode].  The product [tz_mul] is the doubling formula of
    [tower_mul]: (a, b)(c, d) = (a c - conj(d) b, d a + b conj(c)), with
    conjugation conj(a, b) = (conj(a), -b).  [tz_to_R_mul] proves that
    [tz_to_R], the embedding of integer coordinates in the reals, carries
    [tz_mul] to [tower_mul], and [tz_basis_tower] proves that it carries
    the unit vector [tz_basis n i] to [tower_basis n (cube_decode n i)].

    A 2-blade is e_i + s e_j with s = +1 (flag [false]) or s = -1 (flag
    [true]).  An assessor is a pair (i, j) with 1 <= i <= 7, 9 <= j <= 15
    and j <> i + 8 (42 pairs).  A quadruple q = (i, j, k, l) names an
    ordered pair of assessors; [zero_product n q (s, t)] decides whether
    (e_i + s e_j)(e_k + t e_l) is the zero vector of level [n].

    Results.
    - [assessors_count], [quads_count]: 42 assessors, 1764 ordered pairs.
    - [zd_pairs16_count]: 168 of the 1764 ordered assessor pairs have a
      zero product at level 4 for some sign pair (s, t) ([zd_pairs16]).
      [signed_zero_count_16]: 336 sign-resolved ordered products vanish.
      [zero_product_symmetric] and [no_blade_squares_to_zero]: the product
      of two blades vanishes in one order exactly when in the other, and no
      blade has a zero square, so the 336 ordered sign-resolved products are
      168 unordered pairs of blades: 168 counts either the ordered
      assessor pairs with some vanishing sign pair or the unordered
      sign-resolved pairs of blades.
    - [zero_pairs_pp_16], [zero_pairs_pm_16], [sign_patterns_16]: 84
      ordered pairs vanish at (+, +) and 84 at (+, -); a pair vanishing at
      (+, +) vanishes at (-, -), one vanishing at (+, -) vanishes at
      (-, +), and no pair vanishes in both groups, so the four sign
      patterns account for the 336.
      [original_checker_is_plus_plus]: the checker of the original file
      decides the sign pattern (+, +) on every ordered assessor pair, so
      its count 84 is the (+, +) group and not a sign-level undercount of
      the 168.
    - [all_blade_zero_products_are_assessor_pairs]: among all 240
      sign-resolved 2-blades e_i +- e_j (0 <= i < j <= 15) of level 4, the
      ordered pairs with zero product number 336 and every such pair is of
      assessor form, so assessors exhaust the 2-blade zero divisors.
    - [slot_embedding_dim32]: for each offset o in {0, 16}, every ordered
      assessor pair shifted by o has a zero product at level 5 for the
      sign pair st exactly when the unshifted pair has one at level 4.
      [slot_count_dim32]: 336 sign-resolved zero products at each offset.
    - [slot_embedding_dim64]: for each o in {0, 16, 32, 48}, each of the
      168 pairs shifted by o keeps its zero product at level 6 for every
      sign pair that vanishes at level 4.  The converse (no new zero
      product at level 6) is not decided here: the decision on all 1764
      pairs at four offsets is 28224 products of 64-dimensional vectors,
      and a version of this file that decided it measured 1 min 54 s to
      compile and 3 min 20 s for the kernel check (Rocq 9.3.0, one
      host).
    - [slot_embedding_tower_dim32], [slot_embedding_tower_dim64]: the same
      preservation as a statement about [tower_mul] over the reals.
    The claim of the original header (the 168 pairs keep their zero
    product at every 16-element offset in C_32 and C_64) holds under these
    readings; the original proves three instances and the count 84.

    Scope.  The statements concern assessor 2-blades shifted by a multiple
    of 16 inside C_32 and C_64.  They prove nothing about other zero
    divisors, other offsets, levels above 6, or the zero-divisor graph.
    Each result is a decision by evaluation ([vm_compute]) on the
    integer tower plus the structural lemmas that carry it to the reals. *)

From Stdlib Require Import Arith PeanoNat Bool List ZArith Reals.
From OpenGororoba Require Import RecursiveCDTower SchreierSignCode
  CDSignNumericCorrespondence CDTowerSignCorrespondence.
From OpenGororobaVerified Require C1468_SlotShiftEquivariance.
Import ListNotations.

Fixpoint tz (order : nat) : Type :=
  match order with O => Z | S lower => (tz lower * tz lower)%type end.

Fixpoint tz_zero (order : nat) : tz order :=
  match order as o return tz o with
  | O => 0%Z
  | S lower => (tz_zero lower, tz_zero lower)
  end.

Fixpoint tz_add (order : nat) : tz order -> tz order -> tz order :=
  match order as o return tz o -> tz o -> tz o with
  | O => Z.add
  | S lower => fun a b =>
      (tz_add lower (fst a) (fst b), tz_add lower (snd a) (snd b))
  end.

Fixpoint tz_neg (order : nat) : tz order -> tz order :=
  match order as o return tz o -> tz o with
  | O => Z.opp
  | S lower => fun a => (tz_neg lower (fst a), tz_neg lower (snd a))
  end.

Definition tz_sub order a b := tz_add order a (tz_neg order b).

Fixpoint tz_conj (order : nat) : tz order -> tz order :=
  match order as o return tz o -> tz o with
  | O => fun a => a
  | S lower => fun a => (tz_conj lower (fst a), tz_neg lower (snd a))
  end.

Fixpoint tz_mul (order : nat) : tz order -> tz order -> tz order :=
  match order as o return tz o -> tz o -> tz o with
  | O => Z.mul
  | S lower => fun a b =>
      (tz_sub lower (tz_mul lower (fst a) (fst b))
         (tz_mul lower (tz_conj lower (snd b)) (snd a)),
       tz_add lower (tz_mul lower (snd b) (fst a))
         (tz_mul lower (snd a) (tz_conj lower (fst b))))
  end.

Fixpoint tz_eqb (order : nat) : tz order -> tz order -> bool :=
  match order as o return tz o -> tz o -> bool with
  | O => Z.eqb
  | S lower => fun a b =>
      (tz_eqb lower (fst a) (fst b) && tz_eqb lower (snd a) (snd b))%bool
  end.

(** The unit vector of index [i]: the highest bit of [i] selects the
    half, as in [cube_decode]. *)
Fixpoint tz_basis (order : nat) : nat -> tz order :=
  match order as o return nat -> tz o with
  | O => fun _ => 1%Z
  | S lower => fun i =>
      if Nat.ltb i (Nat.pow 2 lower)
      then (tz_basis lower i, tz_zero lower)
      else (tz_zero lower, tz_basis lower (i - Nat.pow 2 lower))
  end.

Fixpoint tz_to_R (order : nat) : tz order -> cd_tower order :=
  match order as o return tz o -> cd_tower o with
  | O => IZR
  | S lower => fun a => (tz_to_R lower (fst a), tz_to_R lower (snd a))
  end.

Lemma tz_to_R_zero order : tz_to_R order (tz_zero order) = tower_zero order.
Proof.
  induction order as [|order IH]; [apply (eq_refl 0%R)|].
  cbn [tz_zero tower_zero tz_to_R fst snd]. rewrite IH. reflexivity.
Qed.

Lemma tz_to_R_add order : forall a b,
  tz_to_R order (tz_add order a b)
  = tower_add order (tz_to_R order a) (tz_to_R order b).
Proof.
  induction order as [|order IH]; intros a b.
  - cbn [tz_add tz_to_R tower_add]. apply plus_IZR.
  - destruct a as [a1 a2], b as [b1 b2].
    cbn [tz_add tz_to_R tower_add fst snd]. rewrite !IH. reflexivity.
Qed.

Lemma tz_to_R_neg order : forall a,
  tz_to_R order (tz_neg order a) = tower_neg order (tz_to_R order a).
Proof.
  induction order as [|order IH]; intros a.
  - cbn [tz_neg tz_to_R tower_neg]. apply opp_IZR.
  - destruct a as [a1 a2].
    cbn [tz_neg tz_to_R tower_neg fst snd]. rewrite !IH. reflexivity.
Qed.

Lemma tz_to_R_conj order : forall a,
  tz_to_R order (tz_conj order a) = tower_conj order (tz_to_R order a).
Proof.
  induction order as [|order IH]; intros a.
  - reflexivity.
  - destruct a as [a1 a2].
    cbn [tz_conj tz_to_R tower_conj fst snd]. rewrite IH, tz_to_R_neg.
    reflexivity.
Qed.

Lemma tz_to_R_mul order : forall a b,
  tz_to_R order (tz_mul order a b)
  = tower_mul order (tz_to_R order a) (tz_to_R order b).
Proof.
  induction order as [|order IH]; intros a b.
  - cbn [tz_mul tz_to_R tower_mul]. apply mult_IZR.
  - destruct a as [a1 a2], b as [b1 b2].
    cbn [tz_mul tz_to_R tower_mul fst snd].
    unfold tz_sub, tower_sub.
    rewrite !tz_to_R_add, !tz_to_R_neg, !IH, !tz_to_R_conj. reflexivity.
Qed.

Lemma tz_eqb_true order : forall a b, tz_eqb order a b = true -> a = b.
Proof.
  induction order as [|order IH]; intros a b H.
  - cbn [tz_eqb] in H. apply Z.eqb_eq. exact H.
  - destruct a as [a1 a2], b as [b1 b2].
    cbn [tz_eqb fst snd] in H. apply andb_true_iff in H as [H1 H2].
    f_equal; [apply IH | apply IH]; assumption.
Qed.

Lemma tz_basis_tower order : forall i,
  tz_to_R order (tz_basis order i)
  = tower_basis order (cube_decode order i).
Proof.
  induction order as [|order IH]; intros i.
  - reflexivity.
  - cbn [tz_basis cube_decode tower_basis].
    destruct (Nat.ltb i (Nat.pow 2 order)) eqn:E.
    + cbn [tz_to_R fst snd]. rewrite IH, tz_to_R_zero. reflexivity.
    + cbn [tz_to_R fst snd]. rewrite IH, tz_to_R_zero. reflexivity.
Qed.

(** Sign-resolved 2-blades and their products. *)
Definition blade order (i j : nat) (neg : bool) : tz order :=
  tz_add order (tz_basis order i)
    (if neg then tz_neg order (tz_basis order j) else tz_basis order j).

Definition tower_blade order (i j : nat) (neg : bool) : cd_tower order :=
  tower_add order (tower_basis order (cube_decode order i))
    (tower_signed order neg (tower_basis order (cube_decode order j))).

Lemma blade_tower order i j neg :
  tz_to_R order (blade order i j neg) = tower_blade order i j neg.
Proof.
  unfold blade, tower_blade, tower_signed.
  rewrite tz_to_R_add, !tz_basis_tower.
  destruct neg; [rewrite tz_to_R_neg, tz_basis_tower|rewrite tz_basis_tower];
    reflexivity.
Qed.

Definition quad : Type := (nat * nat * nat * nat)%type.

Definition zero_product order (q : quad) (st : bool * bool) : bool :=
  match q with
  | (i, j, k, l) =>
      tz_eqb order
        (tz_mul order (blade order i j (fst st)) (blade order k l (snd st)))
        (tz_zero order)
  end.

Definition zd_in_tower order (q : quad) (st : bool * bool) : Prop :=
  match q with
  | (i, j, k, l) =>
      tower_mul order (tower_blade order i j (fst st))
        (tower_blade order k l (snd st)) = tower_zero order
  end.

Lemma zero_product_sound order q st :
  zero_product order q st = true -> zd_in_tower order q st.
Proof.
  destruct q as [[[i j] k] l]. cbn [zero_product zd_in_tower]. intros H.
  apply tz_eqb_true in H.
  apply (f_equal (tz_to_R order)) in H.
  rewrite tz_to_R_mul, !blade_tower, tz_to_R_zero in H. exact H.
Qed.

Definition signs : list (bool * bool) :=
  [(false, false); (false, true); (true, false); (true, true)].

Definition assessors : list (nat * nat) :=
  filter (fun p => negb (Nat.eqb (snd p) (fst p + 8)))
    (list_prod (seq 1 7) (seq 9 7)).

Definition quads : list quad :=
  flat_map (fun a => map (fun b => (fst a, snd a, fst b, snd b)) assessors)
    assessors.

Definition shift (o : nat) (q : quad) : quad :=
  match q with (i, j, k, l) => (i + o, j + o, k + o, l + o) end.

Definition flags order (q : quad) : list bool :=
  map (zero_product order q) signs.

Definition is_zd_pair (q : quad) : bool := existsb (fun b => b) (flags 4 q).

Definition zd_pairs16 : list quad := filter is_zd_pair quads.

Definition count_true (l : list bool) : nat :=
  length (filter (fun b => b) l).

(** Number of sign-resolved ordered products with zero value at level
    [order] among the assessor quadruples shifted by [o]. *)
Definition signed_zero_count order o : nat :=
  fold_right Nat.add 0
    (map (fun q => count_true (flags order (shift o q))) quads).

Definition pattern_count order (st : bool * bool) : nat :=
  length (filter (fun q => zero_product order q st) quads).

Theorem assessors_count : length assessors = 42.
Proof. vm_compute. reflexivity. Qed.

Theorem quads_count : length quads = 1764.
Proof. vm_compute. reflexivity. Qed.

Theorem zd_pairs16_count : length zd_pairs16 = 168.
Proof. vm_compute. reflexivity. Qed.

Theorem signed_zero_count_16 : signed_zero_count 4 0 = 336.
Proof. vm_compute. reflexivity. Qed.

Theorem zero_pairs_pp_16 : pattern_count 4 (false, false) = 84.
Proof. vm_compute. reflexivity. Qed.

Theorem zero_pairs_pm_16 : pattern_count 4 (false, true) = 84.
Proof. vm_compute. reflexivity. Qed.

(** The checker of the original file ([zd_product_zero] on its [sign16])
    decides the sign pattern (+, +) on each of the 1764 ordered pairs. *)
Theorem original_checker_is_plus_plus :
  forallb (fun q => match q with
    | (i, j, k, l) =>
        Bool.eqb
          (C1468_SlotShiftEquivariance.zd_product_zero
             C1468_SlotShiftEquivariance.sign16 i j k l)
          (zero_product 4 q (false, false))
    end) quads = true.
Proof. vm_compute. reflexivity. Qed.

(** Every 2-blade e_i +- e_j with 0 <= i < j <= 15, assessor or not. *)
Definition blades16 : list (nat * nat * bool) :=
  flat_map (fun i =>
    flat_map (fun j => [(i, j, false); (i, j, true)]) (seq (S i) (15 - i)))
    (seq 0 15).

Definition is_assessor (b : nat * nat * bool) : bool :=
  match b with
  | (i, j, _) =>
      (Nat.leb 1 i && Nat.leb i 7 && Nat.leb 9 j && Nat.leb j 15
       && negb (Nat.eqb j (i + 8)))%bool
  end.

Definition blade_product_zero (a b : nat * nat * bool) : bool :=
  match a, b with
  | (i, j, s), (k, l, t) =>
      tz_eqb 4 (tz_mul 4 (blade 4 i j s) (blade 4 k l t)) (tz_zero 4)
  end.

Theorem blades16_count : length blades16 = 240.
Proof. vm_compute. reflexivity. Qed.

(** Among all 240 sign-resolved 2-blades of level 4, exactly 336 ordered
    pairs have a zero product, and both blades of each such pair are of
    assessor form. *)
Theorem all_blade_zero_products_are_assessor_pairs :
  length (filter (fun p => blade_product_zero (fst p) (snd p))
            (list_prod blades16 blades16)) = 336
  /\ forallb (fun a => forallb (fun b =>
        implb (blade_product_zero a b) (is_assessor a && is_assessor b))
        blades16) blades16 = true.
Proof. split; vm_compute; reflexivity. Qed.

Theorem zero_product_symmetric :
  forallb (fun q => forallb (fun st =>
    match q with
    | (i, j, k, l) =>
        Bool.eqb (zero_product 4 q st)
          (zero_product 4 (k, l, i, j) (snd st, fst st))
    end) signs) quads = true.
Proof. vm_compute. reflexivity. Qed.

Theorem no_blade_squares_to_zero :
  forallb (fun a => negb (blade_product_zero a a)) blades16 = true.
Proof. vm_compute. reflexivity. Qed.

(** At (+, +) a zero product forces one at (-, -), and at (+, -) one at
    (-, +); no other sign pattern carries a zero product. *)
Theorem sign_patterns_16 :
  forallb (fun q =>
    Bool.eqb (zero_product 4 q (false, false)) (zero_product 4 q (true, true))
    && Bool.eqb (zero_product 4 q (false, true))
         (zero_product 4 q (true, false))
    && negb (zero_product 4 q (false, false) && zero_product 4 q (false, true)))
    quads = true.
Proof. vm_compute. reflexivity. Qed.

Theorem zd_pairs16_in_tower : forall q st,
  In q zd_pairs16 -> zero_product 4 q st = true -> zd_in_tower 4 q st.
Proof. intros q st _ H. exact (zero_product_sound 4 q st H). Qed.

(** The slot check compares the four zero-product flags of every assessor
    quadruple at level 4 with those of the quadruple shifted by [o]. *)
Definition flags_eqb (a b : list bool) : bool :=
  if list_eq_dec Bool.bool_dec a b then true else false.

Definition slot_check order o : bool :=
  forallb (fun q => flags_eqb (flags order (shift o q)) (flags 4 q)) quads.

Lemma slot_check_flags order o : slot_check order o = true ->
  forall q, In q quads -> flags order (shift o q) = flags 4 q.
Proof.
  intros H q Hq. unfold slot_check in H.
  rewrite forallb_forall in H. specialize (H q Hq).
  unfold flags_eqb in H.
  destruct (list_eq_dec Bool.bool_dec (flags order (shift o q)) (flags 4 q));
    [assumption | discriminate].
Qed.

Lemma slot_check_equiv order o : slot_check order o = true ->
  forall q st, In q quads ->
    zero_product order (shift o q) st = zero_product 4 q st.
Proof.
  intros H q st Hq. pose proof (slot_check_flags order o H q Hq) as F.
  unfold flags in F.
  destruct st as [[|] [|]]; cbn [signs];
    [ apply (f_equal (fun l => nth 3 l false)) in F
    | apply (f_equal (fun l => nth 2 l false)) in F
    | apply (f_equal (fun l => nth 1 l false)) in F
    | apply (f_equal (fun l => nth 0 l false)) in F ];
    exact F.
Qed.

Lemma slot_check_count order o : slot_check order o = true ->
  signed_zero_count order o = signed_zero_count 4 0.
Proof.
  intros H. unfold signed_zero_count. f_equal.
  - apply map_ext_in. intros q Hq.
    rewrite (slot_check_flags order o H q Hq).
    cbn [shift]. destruct q as [[[i j] k] l]. cbn [shift].
    rewrite !Nat.add_0_r. reflexivity.
Qed.

Theorem slot_check_dim32_0 : slot_check 5 0 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem slot_check_dim32_16 : slot_check 5 16 = true.
Proof. vm_compute. reflexivity. Qed.

(** Every ordered assessor pair shifted by an offset of 16 has a zero
    product at level 5 for the sign pair [st] exactly when the unshifted
    pair has one at level 4. *)
Theorem slot_embedding_dim32 : forall o, In o [0; 16] ->
  forall q st, In q quads ->
    zero_product 5 (shift o q) st = zero_product 4 q st.
Proof.
  intros o Ho. destruct Ho as [<-|[<-|[]]];
    apply slot_check_equiv; [exact slot_check_dim32_0 | exact slot_check_dim32_16].
Qed.

Theorem slot_count_dim32 : forall o, In o [0; 16] ->
  signed_zero_count 5 o = 336.
Proof.
  intros o Ho. rewrite <- signed_zero_count_16.
  destruct Ho as [<-|[<-|[]]];
    apply slot_check_count; [exact slot_check_dim32_0 | exact slot_check_dim32_16].
Qed.

(** The 168 pairs of level 4 keep their zero product at each offset, as
    a statement about [tower_mul] over the reals. *)
Theorem slot_embedding_tower_dim32 : forall o, In o [0; 16] ->
  forall q st, In q zd_pairs16 -> zero_product 4 q st = true ->
    zd_in_tower 5 (shift o q) st.
Proof.
  intros o Ho q st Hq H. apply zero_product_sound.
  rewrite (slot_embedding_dim32 o Ho q st); [exact H|].
  unfold zd_pairs16 in Hq. apply filter_In in Hq as [Hq _]. exact Hq.
Qed.

(** Level 6 is checked on the 168 pairs and their zero sign pairs only:
    the decision on all 1764 pairs at four offsets costs about 28000
    products of 64-dimensional vectors. *)
Definition slot_preserved order o : bool :=
  forallb (fun q =>
    forallb (fun st =>
      implb (zero_product 4 q st) (zero_product order (shift o q) st)) signs)
    zd_pairs16.

Lemma slot_preserved_sound order o : slot_preserved order o = true ->
  forall q st, In q zd_pairs16 -> zero_product 4 q st = true ->
    zero_product order (shift o q) st = true.
Proof.
  intros H q st Hq Hz. unfold slot_preserved in H.
  rewrite forallb_forall in H. specialize (H q Hq).
  rewrite forallb_forall in H.
  assert (Hs : In st signs).
  { destruct st as [[|] [|]]; unfold signs; cbn [In];
      [ right; right; right; left | right; right; left | right; left | left ];
      reflexivity. }
  specialize (H st Hs). rewrite Hz in H. exact H.
Qed.

Theorem slot_preserved_dim64_0 : slot_preserved 6 0 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem slot_preserved_dim64_16 : slot_preserved 6 16 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem slot_preserved_dim64_32 : slot_preserved 6 32 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem slot_preserved_dim64_48 : slot_preserved 6 48 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem slot_embedding_dim64 : forall o, In o [0; 16; 32; 48] ->
  forall q st, In q zd_pairs16 -> zero_product 4 q st = true ->
    zero_product 6 (shift o q) st = true.
Proof.
  intros o Ho. destruct Ho as [<-|[<-|[<-|[<-|[]]]]];
    apply slot_preserved_sound;
    [ exact slot_preserved_dim64_0 | exact slot_preserved_dim64_16
    | exact slot_preserved_dim64_32 | exact slot_preserved_dim64_48 ].
Qed.

Theorem slot_embedding_tower_dim64 : forall o, In o [0; 16; 32; 48] ->
  forall q st, In q zd_pairs16 -> zero_product 4 q st = true ->
    zd_in_tower 6 (shift o q) st.
Proof.
  intros o Ho q st Hq H. apply zero_product_sound.
  exact (slot_embedding_dim64 o Ho q st Hq H).
Qed.
