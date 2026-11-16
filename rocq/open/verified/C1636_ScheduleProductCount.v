(** * C-1636: the products of the Cariow 2013 sedenion schedule.

    Convention: [R16], [r16_sparse_correction], [r16_pointwise_mul],
    [r16_hadamard_forward], [r16_hadamard_reverse], [r16_scale] and
    [r16_cariow2013_sedenion_mul] are those of
    C1636_Cariow2013SedenionSchedule, whose
    [C1636_cariow2013_sedenion_mul_eq] proves the schedule equal to the
    Cayley-Dickson product.  [r16_nth x i] is coordinate i of x for
    i < 16.  An entry (i, j) of [sparse_terms] stands for the product
    b_i * a_j of a coordinate of the right factor b with one of the left
    factor a.

    The module proves:
    - [schedule_factors]: the schedule is the coordinatewise combination
      (first coordinate negated) of the Hadamard part
      [r16_hadamard_reverse (r16_pointwise_mul (H a) (r16_scale (1/16) (H b)))]
      and the sparse correction, with H = [r16_hadamard_forward];
    - [pointwise_products]: coordinate i of [r16_pointwise_mul x y] is the
      single product x_i * y_i, so the Hadamard part forms 16 products;
    - [sparse_correction_table]: coordinate i of the sparse correction is 2
      times the sum of the products listed in row i of [sparse_terms];
    - [sparse_terms_count], [sparse_terms_distinct]: the table holds 1 + 15 * 7
      = 106 products, no two with the same pair of coordinates.
    [C1636_schedule_product_count] collects them: 16 + 106 = 122 products of
    two variable quantities, against the 16 * 16 = 256 products b_i * a_j of
    the coordinate expansion.

    Scope.  That the Hadamard stages, [r16_scale] and the final combination
    form no product of two variable quantities is read from their
    definitions (sums, differences, and scaling by the constants 1/16, 2 and
    -1); that [r16_sparse_correction] forms exactly the products of its
    table is read from its definition, which writes each as b_i * a_j, while
    [sparse_correction_table] proves only that the values agree.  No theorem
    here counts the operations of a definition.  The count
    is that of this schedule; it bounds no other schedule and claims no
    minimality. *)

From Stdlib Require Import List Reals Lia Bool Arith.
From OpenGororobaVerified Require Import C1636_Cariow2013SedenionSchedule.
Import ListNotations.

Local Open Scope nat_scope.

Definition r16_nth (x : R16) (i : nat) : R :=
  match i with
  | 0 => r16_0 x | 1 => r16_1 x | 2 => r16_2 x | 3 => r16_3 x
  | 4 => r16_4 x | 5 => r16_5 x | 6 => r16_6 x | 7 => r16_7 x
  | 8 => r16_8 x | 9 => r16_9 x | 10 => r16_10 x | 11 => r16_11 x
  | 12 => r16_12 x | 13 => r16_13 x | 14 => r16_14 x | 15 => r16_15 x
  | _ => 0%R
  end.

(** Row i lists the pairs (index into b, index into a) of the products that
    coordinate i of [r16_sparse_correction a b] sums. *)
Definition sparse_terms : list (list (nat * nat)) :=
  [ [(0, 0)]
  ; [(2, 3); (4, 5); (7, 6); (8, 9); (11, 10); (13, 12); (14, 15)]
  ; [(3, 1); (4, 6); (5, 7); (8, 10); (9, 11); (14, 12); (15, 13)]
  ; [(1, 2); (6, 5); (4, 7); (10, 9); (8, 11); (15, 12); (13, 14)]
  ; [(5, 1); (6, 2); (7, 3); (8, 12); (9, 13); (10, 14); (11, 15)]
  ; [(7, 2); (1, 4); (3, 6); (12, 9); (14, 11); (8, 13); (10, 15)]
  ; [(5, 3); (2, 4); (1, 7); (15, 9); (12, 10); (11, 13); (8, 14)]
  ; [(6, 1); (3, 4); (2, 5); (13, 10); (12, 11); (9, 14); (8, 15)]
  ; [(9, 1); (10, 2); (11, 3); (12, 4); (13, 5); (14, 6); (15, 7)]
  ; [(11, 2); (13, 4); (14, 7); (1, 8); (3, 10); (5, 12); (6, 15)]
  ; [(9, 3); (14, 4); (15, 5); (2, 8); (1, 11); (6, 12); (7, 13)]
  ; [(10, 1); (15, 4); (13, 6); (3, 8); (2, 9); (7, 12); (5, 14)]
  ; [(9, 5); (10, 6); (11, 7); (4, 8); (1, 13); (2, 14); (3, 15)]
  ; [(12, 1); (14, 3); (10, 7); (5, 8); (4, 9); (6, 11); (2, 15)]
  ; [(15, 1); (12, 2); (11, 5); (6, 8); (7, 9); (4, 10); (3, 13)]
  ; [(13, 2); (12, 3); (9, 6); (7, 8); (5, 10); (4, 11); (1, 14)] ].

Definition eval_row (a b : R16) (row : list (nat * nat)) : R :=
  fold_right (fun p acc => (r16_nth b (fst p) * r16_nth a (snd p) + acc)%R)
    0%R row.

Definition pair_eqb (p q : nat * nat) : bool :=
  Nat.eqb (fst p) (fst q) && Nat.eqb (snd p) (snd q).

Fixpoint nodupb (l : list (nat * nat)) : bool :=
  match l with
  | [] => true
  | x :: r => negb (existsb (pair_eqb x) r) && nodupb r
  end.

Lemma nodupb_NoDup : forall l, nodupb l = true -> NoDup l.
Proof.
  induction l as [|x r IH]; simpl; intros H.
  - constructor.
  - apply andb_prop in H as [H1 H2]. constructor.
    + intros Hin. apply negb_true_iff in H1.
      assert (Hx : existsb (pair_eqb x) r = true).
      { apply existsb_exists. exists x. split; [exact Hin |].
        unfold pair_eqb. rewrite !Nat.eqb_refl. reflexivity. }
      rewrite Hx in H1. discriminate.
    + apply IH. exact H2.
Qed.

Definition r16_combine (t s : R16) : R16 :=
  match t, s with
  | mkR16 t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 t14 t15,
    mkR16 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 =>
      mkR16
        (-(t0 - s0))%R
        (t1 - s1)%R (t2 - s2)%R (t3 - s3)%R (t4 - s4)%R (t5 - s5)%R
        (t6 - s6)%R (t7 - s7)%R (t8 - s8)%R (t9 - s9)%R (t10 - s10)%R
        (t11 - s11)%R (t12 - s12)%R (t13 - s13)%R (t14 - s14)%R
        (t15 - s15)%R
  end.

Theorem schedule_factors :
  forall a b : R16,
    r16_cariow2013_sedenion_mul a b =
    r16_combine
      (r16_hadamard_reverse
        (r16_pointwise_mul (r16_hadamard_forward a)
          (r16_scale (/ 16) (r16_hadamard_forward b))))
      (r16_sparse_correction a b).
Proof. intros a b. reflexivity. Qed.

Theorem pointwise_products :
  forall (x y : R16) (i : nat), i < 16 ->
    r16_nth (r16_pointwise_mul x y) i = (r16_nth x i * r16_nth y i)%R.
Proof.
  intros [x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15]
         [y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15] i Hi.
  do 16 (destruct i as [|i]; [reflexivity |]).
  lia.
Qed.

Theorem sparse_correction_table :
  forall (a b : R16) (i : nat), i < 16 ->
    r16_nth (r16_sparse_correction a b) i =
    (2 * eval_row a b (nth i sparse_terms []))%R.
Proof.
  intros [a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15]
         [b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15] i Hi.
  do 16 (destruct i as [|i];
         [cbv beta iota zeta delta [r16_nth r16_sparse_correction eval_row
            sparse_terms nth fold_right fst snd
            r16_0 r16_1 r16_2 r16_3 r16_4 r16_5 r16_6 r16_7
            r16_8 r16_9 r16_10 r16_11 r16_12 r16_13 r16_14 r16_15];
          ring |]).
  lia.
Qed.

Theorem sparse_terms_count :
  map (@length (nat * nat)) sparse_terms = 1 :: repeat 7 15 /\
  length (concat sparse_terms) = 106.
Proof. split; reflexivity. Qed.

Theorem sparse_terms_distinct : NoDup (concat sparse_terms).
Proof. apply nodupb_NoDup. vm_compute. reflexivity. Qed.

Theorem C1636_schedule_product_count :
  (forall a b : R16,
     r16_cariow2013_sedenion_mul a b =
     r16_combine
       (r16_hadamard_reverse
         (r16_pointwise_mul (r16_hadamard_forward a)
           (r16_scale (/ 16) (r16_hadamard_forward b))))
       (r16_sparse_correction a b)) /\
  (forall (x y : R16) (i : nat), i < 16 ->
     r16_nth (r16_pointwise_mul x y) i = (r16_nth x i * r16_nth y i)%R) /\
  (forall (a b : R16) (i : nat), i < 16 ->
     r16_nth (r16_sparse_correction a b) i =
     (2 * eval_row a b (nth i sparse_terms []))%R) /\
  NoDup (concat sparse_terms) /\
  16 + length (concat sparse_terms) = 122 /\
  122 < 16 * 16.
Proof.
  split; [exact schedule_factors |].
  split; [exact pointwise_products |].
  split; [exact sparse_correction_table |].
  split; [exact sparse_terms_distinct |].
  split; [reflexivity | lia].
Qed.
