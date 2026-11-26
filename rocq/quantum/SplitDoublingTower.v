(** The Cayley-Dickson pair tower with a signature gamma, over a commutative
    ring, and the split algebras it builds.

    Convention. An element of level n + 1 is a pair (a, b) of level-n
    elements, level 0 is the coefficient ring, and the product is
    (a, b)(c, d) = (a c + gamma_n conj(d) b, d a + b conj(c)), with
    conj(a, b) = (conj a, -b) and the unit (1, 0). The index n of gamma_n is
    the level of the factors, so gamma_0 acts on the pairs of coefficients
    and gamma_(n-1) on the top doubling of level n. The product is the one of
    cd_multiply_split of gororoba-open (crates/cd_kernel/src/cayley_dickson/
    signature.rs) with gammas[n] read as gamma_n; gamma_n = -1 at every level
    is the tower of CdTowerDomain.v. A basis vector e_p of level n has index
    p < 2^n, with e_p in the left half when p < 2^(n-1).

    Main results. Over every commutative ring with 1 <> 0, the level-2 tower
    with gamma_0 = 1 or gamma_1 = 1 and the level-3 tower with gamma_j = 1 for
    some j < 3 have nonzero a, b with a b = 0 and b a = 0, so left and right
    multiplication by a fixed nonzero element are not injective and the
    algebra is not a division algebra. The level-3 tower is left and right
    alternative for every signature, and the level-2 tower is associative for
    every signature. Over the integer dual numbers and the Gaussian integers
    the quaternion signature gamma = -1 has nonzero factors with product zero.
    Over the integers the all-plus level-3 tower has the diagonal of basis
    squares [1,1,1,-1,1,-1,-1,1], and each of its 64 basis products is one
    basis vector with coefficient 1 or -1, 24 of them with coefficient -1
    (the fraction 3/8). Over the 56 two-term blades e_i +- e_j (i < j) the
    order-independent counts are 128 ordered pairs (x, y) with x y = 0, of
    which 24 have x = y, and 76 unordered pairs {x, y}, x <> y, with x y = 0
    or y x = 0 (4 with neither blade squaring to zero, 48 with exactly one,
    24 with both); the standard signature has none. The count 52 of pairs
    with i < j and x y = 0 (48 with a blade that squares to zero, 4 without)
    tests one product direction in the generation order of the list and is
    not invariant under reordering it; 128 = 52 + 52 + 24 relates it to the
    ordered count. *)

From Stdlib Require Import Ring ZArith List Lia.
Import ListNotations.

(** The Axiom fields of CommRingNZ are parameters of the module type, not
    assumptions of the development: a module that has this type must prove
    them, as ZRing, ZEps and ZGauss below do, and each theorem of a
    SplitTower instance rests on the proofs of that instance only. *)
Module Type CommRingNZ.
  Parameter t : Type.
  Parameter zero one : t.
  Parameter add mul sub : t -> t -> t.
  Parameter opp : t -> t.
  Axiom ring_th : ring_theory zero one add mul sub opp (@eq t).
  Axiom one_neq_zero : one <> zero.
End CommRingNZ.

Module SplitTower (D : CommRingNZ).

Add Ring split_ring : D.ring_th.

Fixpoint V (n : nat) : Type :=
  match n with O => D.t | S k => (V k * V k)%type end.

Fixpoint zero (n : nat) : V n :=
  match n return V n with O => D.zero | S k => (zero k, zero k) end.

Fixpoint one (n : nat) : V n :=
  match n return V n with O => D.one | S k => (one k, zero k) end.

Fixpoint add (n : nat) : V n -> V n -> V n :=
  match n return V n -> V n -> V n with
  | O => D.add
  | S k => fun x y => (add k (fst x) (fst y), add k (snd x) (snd y))
  end.

Fixpoint neg (n : nat) : V n -> V n :=
  match n return V n -> V n with
  | O => D.opp
  | S k => fun x => (neg k (fst x), neg k (snd x))
  end.

Fixpoint smul (n : nat) (s : D.t) : V n -> V n :=
  match n return V n -> V n with
  | O => D.mul s
  | S k => fun x => (smul k s (fst x), smul k s (snd x))
  end.

Fixpoint conj (n : nat) : V n -> V n :=
  match n return V n -> V n with
  | O => fun x => x
  | S k => fun x => (conj k (fst x), neg k (snd x))
  end.

Fixpoint mul (n : nat) (g : nat -> D.t) : V n -> V n -> V n :=
  match n return V n -> V n -> V n with
  | O => D.mul
  | S k => fun x y =>
      (add k (mul k g (fst x) (fst y))
             (smul k (g k) (mul k g (conj k (snd y)) (snd x))),
       add k (mul k g (snd y) (fst x))
             (mul k g (snd x) (conj k (fst y))))
  end.

Ltac split_pairs :=
  repeat (match goal with
          | |- (_, _) = (_, _) => apply pair_equal_spec; split
          end).

Lemma one_ne_zero : forall n, one n <> zero n.
Proof.
  induction n as [|k IH]; simpl.
  - exact D.one_neq_zero.
  - intro H. injection H as H1. exact (IH H1).
Qed.

(** With gamma_1 = 1, (1, 1)(1, -1) = (1 - gamma_1, 0) = 0 at level 2. *)
Theorem level2_zero_divisor : forall g : nat -> D.t, g 1 = D.one ->
  exists a b : V 2, a <> zero 2 /\ b <> zero 2 /\ mul 2 g a b = zero 2.
Proof.
  intros g Hg.
  exists (one 1, one 1), (one 1, neg 1 (one 1)). repeat split.
  - intro H. exact (one_ne_zero 1 (f_equal fst H)).
  - intro H. exact (one_ne_zero 1 (f_equal fst H)).
  - cbn [mul one neg conj smul add zero fst snd]. rewrite Hg.
    split_pairs. all: (change (V 0) with D.t in *; ring).
Qed.

(** With gamma_2 = 1, (1, 1)(1, -1) = (1 - gamma_2, 0) = 0 at level 3. *)
Theorem level3_zero_divisor : forall g : nat -> D.t, g 2 = D.one ->
  exists a b : V 3, a <> zero 3 /\ b <> zero 3 /\ mul 3 g a b = zero 3.
Proof.
  intros g Hg.
  exists (one 2, one 2), (one 2, neg 2 (one 2)). repeat split.
  - intro H. exact (one_ne_zero 2 (f_equal fst H)).
  - intro H. exact (one_ne_zero 2 (f_equal fst H)).
  - cbn [mul one neg conj smul add zero fst snd]. rewrite Hg.
    split_pairs. all: (change (V 0) with D.t in *; ring).
Qed.

Theorem level3_left_alternative : forall (g : nat -> D.t) (a b : V 3),
  mul 3 g a (mul 3 g a b) = mul 3 g (mul 3 g a a) b.
Proof.
  intros g [[[a0 a1] [a2 a3]] [[a4 a5] [a6 a7]]]
           [[[b0 b1] [b2 b3]] [[b4 b5] [b6 b7]]].
  cbn. split_pairs.
  all: (change (V 0) with D.t in *; ring).
Qed.

Theorem level3_right_alternative : forall (g : nat -> D.t) (a b : V 3),
  mul 3 g (mul 3 g b a) a = mul 3 g b (mul 3 g a a).
Proof.
  intros g [[[a0 a1] [a2 a3]] [[a4 a5] [a6 a7]]]
           [[[b0 b1] [b2 b3]] [[b4 b5] [b6 b7]]].
  cbn. split_pairs.
  all: (change (V 0) with D.t in *; ring).
Qed.

Theorem level2_associative : forall (g : nat -> D.t) (a b c : V 2),
  mul 2 g (mul 2 g a b) c = mul 2 g a (mul 2 g b c).
Proof.
  intros g [[a0 a1] [a2 a3]] [[b0 b1] [b2 b3]] [[c0 c1] [c2 c3]].
  cbn. split_pairs.
  all: (change (V 0) with D.t in *; ring).
Qed.

Ltac ring_entries :=
  split_pairs; (change (V 0) with D.t in *; ring).

Theorem level2_split_zero_divisor : forall g : nat -> D.t,
  (g 0 = D.one \/ g 1 = D.one) ->
  exists a b : V 2, a <> zero 2 /\ b <> zero 2
    /\ mul 2 g a b = zero 2 /\ mul 2 g b a = zero 2.
Proof.
  intros g [Hg|Hg].
  - exists ((D.one, D.one), zero 1), ((D.one, D.opp D.one), zero 1).
    repeat split.
    + intro H. exact (D.one_neq_zero (f_equal fst (f_equal fst H))).
    + intro H. exact (D.one_neq_zero (f_equal fst (f_equal fst H))).
    + cbn [mul one neg conj smul add zero fst snd]. rewrite Hg. ring_entries.
    + cbn [mul one neg conj smul add zero fst snd]. rewrite Hg. ring_entries.
  - exists (one 1, one 1), (one 1, neg 1 (one 1)).
    repeat split.
    + intro H. exact (one_ne_zero 1 (f_equal fst H)).
    + intro H. exact (one_ne_zero 1 (f_equal fst H)).
    + cbn [mul one neg conj smul add zero fst snd]. rewrite Hg. ring_entries.
    + cbn [mul one neg conj smul add zero fst snd]. rewrite Hg. ring_entries.
Qed.

Theorem level3_split_zero_divisor : forall g : nat -> D.t,
  (g 0 = D.one \/ g 1 = D.one \/ g 2 = D.one) ->
  exists a b : V 3, a <> zero 3 /\ b <> zero 3
    /\ mul 3 g a b = zero 3 /\ mul 3 g b a = zero 3.
Proof.
  intros g [Hg|[Hg|Hg]].
  - exists (((D.one, D.one), zero 1), zero 2),
           (((D.one, D.opp D.one), zero 1), zero 2).
    repeat split.
    + intro H. exact (D.one_neq_zero (f_equal fst (f_equal fst (f_equal fst H)))).
    + intro H. exact (D.one_neq_zero (f_equal fst (f_equal fst (f_equal fst H)))).
    + cbn [mul one neg conj smul add zero fst snd]. rewrite Hg. ring_entries.
    + cbn [mul one neg conj smul add zero fst snd]. rewrite Hg. ring_entries.
  - exists ((one 1, one 1), zero 2), ((one 1, neg 1 (one 1)), zero 2).
    repeat split.
    + intro H. exact (one_ne_zero 1 (f_equal fst (f_equal fst H))).
    + intro H. exact (one_ne_zero 1 (f_equal fst (f_equal fst H))).
    + cbn [mul one neg conj smul add zero fst snd]. rewrite Hg. ring_entries.
    + cbn [mul one neg conj smul add zero fst snd]. rewrite Hg. ring_entries.
  - exists (one 2, one 2), (one 2, neg 2 (one 2)).
    repeat split.
    + intro H. exact (one_ne_zero 2 (f_equal fst H)).
    + intro H. exact (one_ne_zero 2 (f_equal fst H)).
    + cbn [mul one neg conj smul add zero fst snd]. rewrite Hg. ring_entries.
    + cbn [mul one neg conj smul add zero fst snd]. rewrite Hg. ring_entries.
Qed.

Lemma level2_mul_zero_right : forall (g : nat -> D.t) (a : V 2),
  mul 2 g a (zero 2) = zero 2.
Proof.
  intros g [[a0 a1] [a2 a3]]. cbn. ring_entries.
Qed.

Lemma level2_mul_zero_left : forall (g : nat -> D.t) (a : V 2),
  mul 2 g (zero 2) a = zero 2.
Proof.
  intros g [[a0 a1] [a2 a3]]. cbn. ring_entries.
Qed.

Lemma level3_mul_zero_right : forall (g : nat -> D.t) (a : V 3),
  mul 3 g a (zero 3) = zero 3.
Proof.
  intros g [[[a0 a1] [a2 a3]] [[a4 a5] [a6 a7]]]. cbn. ring_entries.
Qed.

Lemma level3_mul_zero_left : forall (g : nat -> D.t) (a : V 3),
  mul 3 g (zero 3) a = zero 3.
Proof.
  intros g [[[a0 a1] [a2 a3]] [[a4 a5] [a6 a7]]]. cbn. ring_entries.
Qed.

(** A nonzero zero divisor makes left and right multiplication by it
    non-injective, so the level-2 tower is not a division algebra. *)
Theorem level2_not_division : forall g : nat -> D.t,
  (g 0 = D.one \/ g 1 = D.one) ->
  ~ (forall a : V 2, a <> zero 2 -> forall x y : V 2,
       mul 2 g a x = mul 2 g a y -> x = y)
  /\ ~ (forall a : V 2, a <> zero 2 -> forall x y : V 2,
       mul 2 g x a = mul 2 g y a -> x = y).
Proof.
  intros g H.
  destruct (level2_split_zero_divisor g H) as [a [b [Ha [Hb [Hab Hba]]]]].
  split; intro Hinj; apply Hb; apply (Hinj a Ha b (zero 2)).
  - now rewrite Hab, level2_mul_zero_right.
  - now rewrite Hba, level2_mul_zero_left.
Qed.

(** The same for the level-3 tower, for each of its seven signatures with a
    positive entry. *)
Theorem level3_not_division : forall g : nat -> D.t,
  (g 0 = D.one \/ g 1 = D.one \/ g 2 = D.one) ->
  ~ (forall a : V 3, a <> zero 3 -> forall x y : V 3,
       mul 3 g a x = mul 3 g a y -> x = y)
  /\ ~ (forall a : V 3, a <> zero 3 -> forall x y : V 3,
       mul 3 g x a = mul 3 g y a -> x = y).
Proof.
  intros g H.
  destruct (level3_split_zero_divisor g H) as [a [b [Ha [Hb [Hab Hba]]]]].
  split; intro Hinj; apply Hb; apply (Hinj a Ha b (zero 3)).
  - now rewrite Hab, level3_mul_zero_right.
  - now rewrite Hba, level3_mul_zero_left.
Qed.

End SplitTower.

Module ZRing <: CommRingNZ.
  Definition t := Z.
  Definition zero := 0%Z.
  Definition one := 1%Z.
  Definition add := Z.add.
  Definition mul := Z.mul.
  Definition sub := Z.sub.
  Definition opp := Z.opp.
  Lemma ring_th : ring_theory zero one add mul sub opp (@eq t).
  Proof. exact Zth. Qed.
  Lemma one_neq_zero : one <> zero.
  Proof. discriminate. Qed.
End ZRing.

Module ZT := SplitTower ZRing.

(** Dual numbers a + b eps with eps^2 = 0 over the integers. *)
Module ZEps <: CommRingNZ.
  Open Scope Z_scope.
  Definition t : Type := (Z * Z)%type.
  Definition zero : t := (0, 0).
  Definition one : t := (1, 0).
  Definition add (x y : t) : t := (fst x + fst y, snd x + snd y).
  Definition mul (x y : t) : t := (fst x * fst y, fst x * snd y + snd x * fst y).
  Definition sub (x y : t) : t := (fst x - fst y, snd x - snd y).
  Definition opp (x : t) : t := (- fst x, - snd x).
  Lemma ring_th : ring_theory zero one add mul sub opp (@eq t).
  Proof.
    constructor; intros [a b]; try intros [c d]; try intros [e f];
      unfold zero, one, add, mul, sub, opp; cbn [fst snd];
      apply pair_equal_spec; split; ring.
  Qed.
  Lemma one_neq_zero : one <> zero.
  Proof. discriminate. Qed.
End ZEps.

(** Gaussian integers a + b i with i^2 = -1. *)
Module ZGauss <: CommRingNZ.
  Open Scope Z_scope.
  Definition t : Type := (Z * Z)%type.
  Definition zero : t := (0, 0).
  Definition one : t := (1, 0).
  Definition add (x y : t) : t := (fst x + fst y, snd x + snd y).
  Definition mul (x y : t) : t :=
    (fst x * fst y - snd x * snd y, fst x * snd y + snd x * fst y).
  Definition sub (x y : t) : t := (fst x - fst y, snd x - snd y).
  Definition opp (x : t) : t := (- fst x, - snd x).
  Lemma ring_th : ring_theory zero one add mul sub opp (@eq t).
  Proof.
    constructor; intros [a b]; try intros [c d]; try intros [e f];
      unfold zero, one, add, mul, sub, opp; cbn [fst snd];
      apply pair_equal_spec; split; ring.
  Qed.
  Lemma one_neq_zero : one <> zero.
  Proof. discriminate. Qed.
End ZGauss.

Module DualT := SplitTower ZEps.
Module GaussT := SplitTower ZGauss.

(** eps times eps vanishes, so the dual quaternions have zero divisors. *)
Theorem dual_quaternion_zero_divisor :
  exists a b : DualT.V 2, a <> DualT.zero 2 /\ b <> DualT.zero 2
    /\ DualT.mul 2 (fun _ => (-1, 0)%Z) a b = DualT.zero 2.
Proof.
  exists (((0, 1)%Z, (0, 0)%Z), ((0, 0)%Z, (0, 0)%Z)),
         (((0, 1)%Z, (0, 0)%Z), ((0, 0)%Z, (0, 0)%Z)).
  refine (conj _ (conj _ _)); [discriminate | discriminate | vm_compute; reflexivity].
Qed.

(** (1 + i e_1)(1 - i e_1) = 1 - i^2 e_1^2 = 0 over the Gaussian integers. *)
Theorem biquaternion_zero_divisor :
  exists a b : GaussT.V 2, a <> GaussT.zero 2 /\ b <> GaussT.zero 2
    /\ GaussT.mul 2 (fun _ => (-1, 0)%Z) a b = GaussT.zero 2.
Proof.
  exists ((((1, 0)%Z, (0, 1)%Z), ((0, 0)%Z, (0, 0)%Z))),
         ((((1, 0)%Z, (0, -1)%Z), ((0, 0)%Z, (0, 0)%Z))).
  refine (conj _ (conj _ _)); [discriminate | discriminate | vm_compute; reflexivity].
Qed.

Section IntegerTables.

Open Scope Z_scope.

Definition gs : nat -> Z := fun _ => 1.

(** The basis vector e_p of level n for p < 2^n. An index p >= 2^n lies outside
    the domain and gives the zero vector (basis_out_of_range). *)
Fixpoint basis (n p : nat) : ZT.V n :=
  match n return ZT.V n with
  | O => if Nat.eqb p 0 then 1 else 0
  | S k => if Nat.ltb p (Nat.pow 2 k)
           then (basis k p, ZT.zero k)
           else (ZT.zero k, basis k (p - Nat.pow 2 k))
  end.

Lemma basis_out_of_range : forall n p, (Nat.pow 2 n <= p)%nat -> basis n p = ZT.zero n.
Proof.
  induction n as [|k IH]; intros p H.
  - destruct p as [|p]; [simpl in H; lia|reflexivity].
  - cbn [basis ZT.zero].
    destruct (Nat.ltb p (Nat.pow 2 k)) eqn:E.
    + apply Nat.ltb_lt in E. simpl in H. lia.
    + rewrite (IH (p - Nat.pow 2 k)%nat); [reflexivity|simpl in H; lia].
Qed.

Fixpoint flat (n : nat) : ZT.V n -> list Z :=
  match n return ZT.V n -> list Z with
  | O => fun x => [x]
  | S k => fun x => flat k (fst x) ++ flat k (snd x)
  end.

Definition product (p q : nat) : list Z :=
  flat 3 (ZT.mul 3 gs (basis 3 p) (basis 3 q)).

Definition square_coeff (p : nat) : Z := hd 0 (product p p).

Theorem split_octonion_basis_squares :
  map square_coeff (seq 0 8) = [1; 1; 1; -1; 1; -1; -1; 1].
Proof. vm_compute. reflexivity. Qed.

Definition has_negative (l : list Z) : bool := existsb (fun z => Z.ltb z 0) l.

Definition negative_entries : nat :=
  length (filter (fun pq => has_negative (product (fst pq) (snd pq)))
                 (list_prod (seq 0 8) (seq 0 8))).

Theorem split_octonion_negative_entries : negative_entries = 24%nat.
Proof. vm_compute. reflexivity. Qed.

Definition blade (i j : nat) (s : Z) : ZT.V 3 :=
  ZT.add 3 (basis 3 i) (ZT.smul 3 s (basis 3 j)).

Definition blades : list (ZT.V 3) :=
  flat_map (fun i => flat_map (fun j =>
    if Nat.ltb i j then [blade i j 1; blade i j (-1)] else [])
    (seq 0 8)) (seq 0 8).

Definition is_zero (v : ZT.V 3) : bool :=
  forallb (fun z => Z.eqb z 0) (flat 3 v).

Definition zero_pairs : list (ZT.V 3 * ZT.V 3) :=
  filter (fun xy => is_zero (ZT.mul 3 gs (fst xy) (snd xy)))
    (flat_map (fun i => flat_map (fun j =>
       if Nat.ltb i j then [(nth i blades (ZT.zero 3), nth j blades (ZT.zero 3))]
       else []) (seq 0 (length blades))) (seq 0 (length blades))).

Definition null_square (v : ZT.V 3) : bool := is_zero (ZT.mul 3 gs v v).

Theorem split_octonion_blade_count : length blades = 56%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem split_octonion_zero_product_pairs : length zero_pairs = 52%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem split_octonion_null_null_pairs :
  length (filter (fun xy => andb (null_square (fst xy)) (null_square (snd xy)))
                 zero_pairs) = 24%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem split_octonion_null_involving_pairs :
  length (filter (fun xy => orb (null_square (fst xy)) (null_square (snd xy)))
                 zero_pairs) = 48%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem split_octonion_proper_pairs :
  length (filter (fun xy => negb (orb (null_square (fst xy)) (null_square (snd xy))))
                 zero_pairs) = 4%nat.
Proof. vm_compute. reflexivity. Qed.

(** Each basis product of the all-plus level-3 tower is one basis vector with
    coefficient 1 or -1. *)
Definition single_signed_unit (l : list Z) : bool :=
  andb (Nat.eqb (length (filter (fun z => negb (Z.eqb z 0)) l)) 1%nat)
       (forallb (fun z => orb (Z.eqb z 0) (orb (Z.eqb z 1) (Z.eqb z (-1)))) l).

Theorem split_octonion_products_signed_units :
  forallb (fun pq => single_signed_unit (product (fst pq) (snd pq)))
          (list_prod (seq 0 8) (seq 0 8)) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem split_octonion_table_size :
  length (list_prod (seq 0 8) (seq 0 8)) = 64%nat.
Proof. vm_compute. reflexivity. Qed.

(** 24 of 64 is 3/8: 8 * 24 = 3 * 64. *)
Theorem split_octonion_negative_fraction :
  Nat.mul 8 negative_entries
  = Nat.mul 3 (length (list_prod (seq 0 8) (seq 0 8))).
Proof. vm_compute. reflexivity. Qed.

(** Order-independent census of the 56 blades: the pairs are indexed by
    positions of the list, and each count below is a sum over all positions,
    or over unordered position pairs with a symmetric test. *)
Definition blade_at (i : nat) : ZT.V 3 := nth i blades (ZT.zero 3).

Definition blade_indices : list nat := seq 0 (length blades).

Definition annihilates (g : nat -> Z) (i j : nat) : bool :=
  is_zero (ZT.mul 3 g (blade_at i) (blade_at j)).

Definition ordered_zero_count (g : nat -> Z) : nat :=
  length (filter (fun ij => annihilates g (fst ij) (snd ij))
                 (list_prod blade_indices blade_indices)).

Definition diagonal_zero_count (g : nat -> Z) : nat :=
  length (filter (fun i => annihilates g i i) blade_indices).

Definition forward_zero_count (g : nat -> Z) : nat :=
  length (filter (fun ij => andb (Nat.ltb (fst ij) (snd ij))
                                 (annihilates g (fst ij) (snd ij)))
                 (list_prod blade_indices blade_indices)).

Definition reverse_zero_count (g : nat -> Z) : nat :=
  length (filter (fun ij => andb (Nat.ltb (snd ij) (fst ij))
                                 (annihilates g (fst ij) (snd ij)))
                 (list_prod blade_indices blade_indices)).

Definition unordered_zero_pairs (g : nat -> Z) : list (nat * nat) :=
  filter (fun ij => andb (Nat.ltb (fst ij) (snd ij))
                         (orb (annihilates g (fst ij) (snd ij))
                              (annihilates g (snd ij) (fst ij))))
         (list_prod blade_indices blade_indices).

Definition squares_to_zero (g : nat -> Z) (i : nat) : bool := annihilates g i i.

Theorem split_octonion_ordered_zero_pairs : ordered_zero_count gs = 128%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem split_octonion_diagonal_zero_pairs : diagonal_zero_count gs = 24%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem split_octonion_forward_zero_pairs : forward_zero_count gs = 52%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem split_octonion_reverse_zero_pairs : reverse_zero_count gs = 52%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem split_octonion_unordered_zero_pairs :
  length (unordered_zero_pairs gs) = 76%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem split_octonion_unordered_null_null_pairs :
  length (filter (fun ij => andb (squares_to_zero gs (fst ij))
                                 (squares_to_zero gs (snd ij)))
                 (unordered_zero_pairs gs)) = 24%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem split_octonion_unordered_mixed_pairs :
  length (filter (fun ij => xorb (squares_to_zero gs (fst ij))
                                 (squares_to_zero gs (snd ij)))
                 (unordered_zero_pairs gs)) = 48%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem split_octonion_unordered_proper_pairs :
  length (filter (fun ij => negb (orb (squares_to_zero gs (fst ij))
                                      (squares_to_zero gs (snd ij))))
                 (unordered_zero_pairs gs)) = 4%nat.
Proof. vm_compute. reflexivity. Qed.

(** The standard octonions (every gamma = -1) have no ordered pair of blades
    with product zero. *)
Theorem standard_octonion_ordered_zero_pairs :
  ordered_zero_count (fun _ => -1) = 0%nat.
Proof. vm_compute. reflexivity. Qed.

End IntegerTables.
