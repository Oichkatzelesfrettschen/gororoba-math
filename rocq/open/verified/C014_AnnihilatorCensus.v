(** * C-014, C-015 and the box-kite annihilators: kernel bases of the 2-blade multiplication matrices.

    Convention.  The algebra is level 4 of the integer Cayley-Dickson tower
    [tz] of [C1468_SlotEmbeddingAllPairs], with the product [tz_mul]:
    (a, b)(c, d) = (a c - conj(d) b, d a + b conj(c)).  The unit e_i is
    [tz_basis 4 i] for an index [i < 16], and the coordinate list of a
    vector, [tz_flat], is ordered by index (the first component of a pair
    is the low half).  A 2-blade is e_i + e_j or e_i - e_j with i < j
    ([blades16]).  For a blade u the matrices [lmat u] and [rmat u] have
    column k equal to the coordinates of u e_k and of e_k u; by bilinearity
    of the product they are the matrices of x |-> u x and x |-> x u.  The
    diagonal-form zero divisors of C-014 are the 84 blades of assessor form
    ([diag84]): e_i +- e_j with 1 <= i <= 7, 9 <= j <= 15, j <> i + 8.

    Statement.  [kernel_basis M P] says, over the reals, that the vectors
    P_0, ..., P_(np-1) (integer coordinate lists) lie in the kernel of M,
    are linearly independent, and span it: every real x with M x = 0
    equals a real combination of the P_k.  So the kernel has dimension
    np.  The proof carries no search: [cert_ok] checks an integer
    certificate (C, G, d) with d > 0, M P = 0, C M + P G = d I and
    G P = d I, and [cert_ok_sound] derives the three properties from the
    identity d x = C (M x) + P (G x).  [build_cert] computes the
    certificate by Gauss-Jordan elimination over Q; the checker accepts or
    rejects whatever it returns, so no property of the search enters the
    theorems.

    Results, each a decision by evaluation on [tz_mul] plus [cert_ok_sound].
    - [boxkite_annihilator_census]: for each of the 240 blades u, ker L_u is
      spanned by the blades v with u v = 0 and ker R_u by those with v u =
      0; there are 4 of each for the 84 blades of [diag84] and none for
      the 156 others, whose kernels are {0} (nullity 0).
    - [C014_annihilator_dimension_four]: each of the 84 diagonals has left
      and right annihilator of dimension 4.
    - [C015_four_diagonal_partners]: for each diagonal u there are exactly
      4 diagonals v with u v = 0, exactly 4 with v u = 0, none is u, and
      each set spans its kernel.
    - [cert_ok_rejects_mutants]: the checker accepts the certificate of one
      diagonal and rejects it with d, C, G or a kernel vector perturbed.
    These answer C-014 and C-015 of registry/claims.toml in gororoba-open
    and the annihilator row of docs/evidence/box_kite_census/README.md in
    gororoba-quantum, over the reals.

    Scope.  The sphere statement of C-014 (the unit sphere of the
    annihilator is S^3 ~ SU(2)) is a topological statement that this file
    leaves open.  The two-blades here include e_0 +- e_j, which the 210
    two-blades of the box-kite census exclude; their kernels are {0}.  The
    kernel is that of the multiplication matrix over the real coordinates
    (the bilinearity that identifies it with {x | u x = 0} for every real
    x is not proved here),
    and the integer matrix has the same rank over Q and R. *)

From Stdlib Require Import Arith PeanoNat Bool List ZArith QArith Reals Lia Lra.
From OpenGororobaVerified Require Import C1468_SlotEmbeddingAllPairs.
Import ListNotations.

Local Abbreviation blade_t := (nat * nat * bool)%type.

Local Open Scope R_scope.

Fixpoint rsum (f : nat -> R) (n : nat) : R :=
  match n with O => 0 | S m => rsum f m + f m end.

Fixpoint zsum (f : nat -> Z) (n : nat) : Z :=
  match n with O => 0%Z | S m => (zsum f m + f m)%Z end.

Lemma IZR_zsum f n : IZR (zsum f n) = rsum (fun j => IZR (f j)) n.
Proof.
  induction n as [|n IH]; cbn [zsum rsum]; [reflexivity|].
  rewrite plus_IZR, IH. reflexivity.
Qed.

Lemma rsum_ext f g n :
  (forall i, (i < n)%nat -> f i = g i) -> rsum f n = rsum g n.
Proof.
  induction n as [|n IH]; intros H; cbn [rsum]; [reflexivity|].
  rewrite IH; [rewrite H; [reflexivity | lia] | intros i Hi; apply H; lia].
Qed.

Lemma rsum_add f g n : rsum (fun i => f i + g i) n = rsum f n + rsum g n.
Proof. induction n as [|n IH]; cbn [rsum]; [ring | rewrite IH; ring]. Qed.

Lemma rsum_scale c f n : rsum (fun i => c * f i) n = c * rsum f n.
Proof. induction n as [|n IH]; cbn [rsum]; [ring | rewrite IH; ring]. Qed.

Lemma rsum_mul_r f x n : rsum f n * x = rsum (fun i => f i * x) n.
Proof. induction n as [|n IH]; cbn [rsum]; [ring | rewrite <- IH; ring]. Qed.

Lemma rsum_zero_fun m : rsum (fun _ => 0) m = 0.
Proof. induction m as [|m IH]; cbn [rsum]; [reflexivity | rewrite IH; ring]. Qed.

Lemma rsum_swap (h : nat -> nat -> R) n m :
  rsum (fun i => rsum (fun j => h i j) m) n
  = rsum (fun j => rsum (fun i => h i j) n) m.
Proof.
  induction n as [|n IH]; cbn [rsum].
  - symmetry. apply rsum_zero_fun.
  - rewrite IH. rewrite <- rsum_add. apply rsum_ext. intros j _. reflexivity.
Qed.

Lemma rsum_delta (g : nat -> R) i n :
  (i < n)%nat -> rsum (fun j => if Nat.eqb i j then g j else 0) n = g i.
Proof.
  induction n as [|n IH]; intros H; [lia|]. cbn [rsum].
  destruct (Nat.eqb i n) eqn:E.
  - apply Nat.eqb_eq in E. subst i.
    assert (rsum (fun j => if Nat.eqb n j then g j else 0) n = 0) as ->.
    { transitivity (rsum (fun _ => 0) n); [|apply rsum_zero_fun].
      apply rsum_ext. intros j Hj.
      destruct (Nat.eqb n j) eqn:E2; [apply Nat.eqb_eq in E2; lia | reflexivity]. }
    ring.
  - apply Nat.eqb_neq in E. rewrite IH by lia. ring.
Qed.

Lemma rsum_sandwich (a : nat -> R) (b : nat -> nat -> R) (x : nat -> R) n m :
  rsum (fun j => rsum (fun k => a k * b k j) n * x j) m
  = rsum (fun k => a k * rsum (fun j => b k j * x j) m) n.
Proof.
  transitivity (rsum (fun j => rsum (fun k => a k * (b k j * x j)) n) m).
  - apply rsum_ext. intros j _. rewrite rsum_mul_r. apply rsum_ext.
    intros k _. ring.
  - rewrite rsum_swap. apply rsum_ext. intros k _. rewrite <- rsum_scale.
    reflexivity.
Qed.

(** * Kernel basis from an integer certificate. *)

Section Sound.
Variables (L C G P : nat -> nat -> Z) (d : Z) (np : nat).
Hypothesis Hd : (0 < d)%Z.
Hypothesis Hker : forall k i, (k < np)%nat -> (i < 16)%nat ->
  zsum (fun j => (L i j * P k j)%Z) 16 = 0%Z.
Hypothesis Hid : forall i j, (i < 16)%nat -> (j < 16)%nat ->
  (zsum (fun k => (C i k * L k j)%Z) 16 + zsum (fun k => (P k i * G k j)%Z) np)%Z
  = (if Nat.eqb i j then d else 0%Z).
Hypothesis Hind : forall a b, (a < np)%nat -> (b < np)%nat ->
  zsum (fun j => (G a j * P b j)%Z) 16 = (if Nat.eqb a b then d else 0%Z).

Lemma Rd_pos : 0 < IZR d.
Proof. apply (IZR_lt 0). exact Hd. Qed.

Lemma IZR_if (c : bool) : IZR (if c then d else 0%Z) = if c then IZR d else 0.
Proof. destruct c; reflexivity. Qed.

Theorem kernel_basis_sound :
  (forall k, (k < np)%nat -> forall i, (i < 16)%nat ->
     rsum (fun j => IZR (L i j) * IZR (P k j)) 16 = 0)
  /\ (forall c : nat -> R,
        (forall i, (i < 16)%nat -> rsum (fun k => c k * IZR (P k i)) np = 0) ->
        forall k, (k < np)%nat -> c k = 0)
  /\ (forall x : nat -> R,
        (forall i, (i < 16)%nat -> rsum (fun j => IZR (L i j) * x j) 16 = 0) ->
        exists c : nat -> R, forall i, (i < 16)%nat ->
          x i = rsum (fun k => c k * IZR (P k i)) np).
Proof.
  pose proof Rd_pos as Rdp.
  repeat split.
  - intros k Hk i Hi.
    pose proof (f_equal IZR (Hker k i Hk Hi)) as H. rewrite IZR_zsum in H.
    rewrite <- H. apply rsum_ext. intros j _. rewrite mult_IZR. reflexivity.
  - intros c Hc a Ha.
    assert (H1 : rsum (fun j => IZR (G a j) * rsum (fun k => c k * IZR (P k j)) np) 16 = 0).
    { transitivity (rsum (fun _ => 0) 16); [|apply rsum_zero_fun]. apply rsum_ext. intros j Hj.
      rewrite (Hc j Hj). ring. }
    assert (H2 : rsum (fun j => IZR (G a j) * rsum (fun k => c k * IZR (P k j)) np) 16
                 = IZR d * c a).
    { transitivity (rsum (fun j => rsum (fun k => c k * (IZR (G a j) * IZR (P k j))) np) 16).
      { apply rsum_ext. intros j _. rewrite <- rsum_scale. apply rsum_ext.
        intros k _. ring. }
      rewrite rsum_swap.
      transitivity (rsum (fun k => if Nat.eqb a k then IZR d * c k else 0) np).
      { apply rsum_ext. intros k Hk.
        rewrite (rsum_scale (c k) (fun j => IZR (G a j) * IZR (P k j)) 16).
        assert (E : rsum (fun j => IZR (G a j) * IZR (P k j)) 16
                    = IZR (if Nat.eqb a k then d else 0%Z)).
        { rewrite <- (Hind a k Ha Hk), IZR_zsum. apply rsum_ext.
          intros j _. rewrite mult_IZR. reflexivity. }
        rewrite E, IZR_if. destruct (Nat.eqb a k); ring. }
      apply rsum_delta. exact Ha. }
    rewrite H1 in H2. nra.
  - intros x Hx.
    exists (fun k => rsum (fun j => IZR (G k j) * x j) 16 / IZR d).
    intros i Hi.
    assert (A : rsum (fun j => IZR (zsum (fun k => (C i k * L k j)%Z) 16) * x j) 16 = 0).
    { transitivity (rsum (fun j => rsum (fun k => IZR (C i k) * IZR (L k j)) 16 * x j) 16).
      { apply rsum_ext. intros j _. rewrite IZR_zsum.
        f_equal. apply rsum_ext. intros k _. rewrite mult_IZR. reflexivity. }
      rewrite rsum_sandwich.
      transitivity (rsum (fun _ => 0) 16); [|apply rsum_zero_fun]. apply rsum_ext. intros k Hk.
      rewrite (Hx k Hk). ring. }
    assert (B : rsum (fun j => IZR (zsum (fun k => (P k i * G k j)%Z) np) * x j) 16
                = rsum (fun k => IZR (P k i) * rsum (fun j => IZR (G k j) * x j) 16) np).
    { transitivity (rsum (fun j => rsum (fun k => IZR (P k i) * IZR (G k j)) np * x j) 16).
      { apply rsum_ext. intros j _. rewrite IZR_zsum.
        f_equal. apply rsum_ext. intros k _. rewrite mult_IZR. reflexivity. }
      apply rsum_sandwich. }
    assert (E : IZR d * x i
      = rsum (fun j => IZR (zsum (fun k => (C i k * L k j)%Z) 16) * x j) 16
        + rsum (fun j => IZR (zsum (fun k => (P k i * G k j)%Z) np) * x j) 16).
    { rewrite <- rsum_add.
      transitivity (rsum (fun j => if Nat.eqb i j then IZR d * x j else 0) 16).
      { exact (eq_sym (rsum_delta (fun j => IZR d * x j) i 16 Hi)). }
      apply rsum_ext. intros j Hj.
      pose proof (f_equal IZR (Hid i j Hi Hj)) as H'.
      rewrite plus_IZR, IZR_if in H'.
      rewrite <- Rmult_plus_distr_r, H'. destruct (Nat.eqb i j); ring. }
    rewrite A, B in E.
    set (S := rsum (fun k => IZR (P k i) * rsum (fun j => IZR (G k j) * x j) 16) np) in *.
    assert (F : rsum (fun k => rsum (fun j => IZR (G k j) * x j) 16 / IZR d * IZR (P k i)) np
                = S / IZR d).
    { transitivity (rsum (fun k => (/ IZR d) * (IZR (P k i) * rsum (fun j => IZR (G k j) * x j) 16)) np).
      { apply rsum_ext. intros k _. cbv beta. unfold Rdiv. ring. }
      rewrite rsum_scale. unfold S, Rdiv. ring. }
    assert (E' : S = IZR d * x i) by lra.
    assert (Hdn : IZR d <> 0) by lra.
    cbv beta. rewrite F, E'. field. exact Hdn.
Qed.
End Sound.

Local Close Scope R_scope.

(** * Checker. *)

Definition all_lt (n : nat) (p : nat -> bool) : bool := forallb p (seq 0 n).

Lemma all_lt_spec n p :
  all_lt n p = true -> forall i, (i < n)%nat -> p i = true.
Proof.
  intros H i Hi. unfold all_lt in H. rewrite forallb_forall in H.
  apply H. apply in_seq. lia.
Qed.

Definition mget (M : list (list Z)) (i j : nat) : Z := nth j (nth i M []) 0%Z.

Definition delta_d (d : Z) (i j : nat) : Z := if Nat.eqb i j then d else 0%Z.

Definition cert_ok (M P C G : list (list Z)) (d : Z) : bool :=
  let np := length P in
  (Z.ltb 0 d
   && all_lt np (fun k => all_lt 16 (fun i =>
        Z.eqb (zsum (fun j => (mget M i j * mget P k j)%Z) 16) 0%Z))
   && all_lt 16 (fun i => all_lt 16 (fun j =>
        Z.eqb (zsum (fun k => (mget C i k * mget M k j)%Z) 16
               + zsum (fun k => (mget P k i * mget G k j)%Z) np)%Z
              (delta_d d i j)))
   && all_lt np (fun a => all_lt np (fun b =>
        Z.eqb (zsum (fun j => (mget G a j * mget P b j)%Z) 16) (delta_d d a b))))%bool.

Local Open Scope R_scope.

Definition kernel_basis (M P : list (list Z)) : Prop :=
  (forall k, (k < length P)%nat -> forall i, (i < 16)%nat ->
     rsum (fun j => IZR (mget M i j) * IZR (mget P k j)) 16 = 0%R)
  /\ (forall c : nat -> R,
        (forall i, (i < 16)%nat ->
           rsum (fun k => c k * IZR (mget P k i)) (length P) = 0%R) ->
        forall k, (k < length P)%nat -> c k = 0%R)
  /\ (forall x : nat -> R,
        (forall i, (i < 16)%nat ->
           rsum (fun j => IZR (mget M i j) * x j) 16 = 0%R) ->
        exists c : nat -> R, forall i, (i < 16)%nat ->
          x i = rsum (fun k => c k * IZR (mget P k i)) (length P)).

Theorem cert_ok_sound M P C G d :
  cert_ok M P C G d = true -> kernel_basis M P.
Proof.
  unfold cert_ok. intros H.
  apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [H H3].
  apply andb_true_iff in H as [H1 H2].
  apply (kernel_basis_sound (mget M) (mget C) (mget G) (mget P) d (length P)).
  - apply Z.ltb_lt. exact H1.
  - intros k i Hk Hi.
    pose proof (all_lt_spec _ _ H2 k Hk) as Hk2.
    pose proof (all_lt_spec _ _ Hk2 i Hi) as Hi2.
    apply Z.eqb_eq in Hi2. exact Hi2.
  - intros i j Hi Hj.
    pose proof (all_lt_spec _ _ H3 i Hi) as Hi3.
    pose proof (all_lt_spec _ _ Hi3 j Hj) as Hj3.
    apply Z.eqb_eq in Hj3. exact Hj3.
  - intros a b Ha Hb.
    pose proof (all_lt_spec _ _ H4 a Ha) as Ha4.
    pose proof (all_lt_spec _ _ Ha4 b Hb) as Hb4.
    apply Z.eqb_eq in Hb4. exact Hb4.
Qed.

Local Close Scope R_scope.

(** * Certificate search over Q (untrusted). *)

Definition qrow := list Q.

Definition qnth (r : qrow) (i : nat) : Q := nth i r 0%Q.

Definition row_scale (c : Q) (r : qrow) : qrow :=
  map (fun x => Qred (Qmult c x)) r.

(** [r - c s] entrywise. *)
Definition row_axpy (r s : qrow) (c : Q) : qrow :=
  map (fun p => Qred (Qminus (fst p) (Qmult c (snd p)))) (combine r s).

Definition set_row (rows : list qrow) (i : nat) (r : qrow) : list qrow :=
  firstn i rows ++ [r] ++ skipn (S i) rows.

Definition swap_rows (rows : list qrow) (i j : nat) : list qrow :=
  if Nat.eqb i j then rows
  else set_row (set_row rows i (nth j rows [])) j (nth i rows []).

Definition find_pivot (rows : list qrow) (r c : nat) : option nat :=
  find (fun i => negb (Qeq_bool (qnth (nth i rows []) c) 0%Q))
    (seq r (length rows - r)).

Definition eliminate (rows : list qrow) (r c : nat) (prow : qrow) : list qrow :=
  map (fun ir => if Nat.eqb (fst ir) r then prow
                 else row_axpy (snd ir) prow (qnth (snd ir) c))
    (combine (seq 0 (length rows)) rows).

Fixpoint gj (cols : list nat) (rows : list qrow) (r : nat)
  (piv : list (nat * nat)) : list qrow * list (nat * nat) :=
  match cols with
  | [] => (rows, piv)
  | c :: cs =>
      match find_pivot rows r c with
      | None => gj cs rows r piv
      | Some p =>
          let rows1 := swap_rows rows r p in
          let pr := nth r rows1 [] in
          let prow := row_scale (Qinv (qnth pr c)) pr in
          gj cs (eliminate rows1 r c prow) (S r) ((c, r) :: piv)
      end
  end.

(** A solution X (m rows of k entries) of A X = B, free unknowns zero. *)
Definition solve (m k : nat) (A B : list qrow) : list qrow :=
  let aug := map (fun p => fst p ++ snd p) (combine A B) in
  let res := gj (seq 0 m) aug 0 [] in
  map (fun c =>
    match find (fun p => Nat.eqb (fst p) c) (snd res) with
    | Some p => skipn m (nth (snd p) (fst res) [])
    | None => repeat 0%Q k
    end) (seq 0 m).

Definition transpose (n : nat) (M : list qrow) : list qrow :=
  map (fun j => map (fun r => qnth r j) M) (seq 0 n).

Fixpoint qsum (l : list Q) : Q :=
  match l with [] => 0%Q | x :: t => Qplus x (qsum t) end.

Definition qdot (a b : qrow) : Q :=
  Qred (qsum (map (fun p => Qmult (fst p) (snd p)) (combine a b))).

Definition den_lcm (rows : list qrow) : Z :=
  fold_left (fun acc r =>
    fold_left (fun a q => Z.lcm a (Zpos (Qden q))) r acc) rows 1%Z.

Definition to_Z (D : Z) (q : Q) : Z := (Qnum q * (D / Zpos (Qden q)))%Z.

Definition idx16 : list nat := seq 0 16.

(** C (16 x 16), G (np x 16) and d with C M + P G = d I; P holds the np
    kernel vectors as rows. *)
Definition build_cert (M P : list (list Z))
  : list (list Z) * list (list Z) * Z :=
  let ML : list qrow := map (map inject_Z) M in
  let Pq : list qrow := map (map inject_Z) P in
  let G0 : list qrow :=
    match P with
    | [] => []
    | _ => solve (length P) 16
             (map (fun a => map (fun b => qdot a b) Pq) Pq) Pq
    end in
  let N : list qrow :=
    map (fun i => map (fun j =>
      Qminus (if Nat.eqb i j then 1%Q else 0%Q)
        (qsum (map (fun k => Qmult (qnth (nth k Pq []) i) (qnth (nth k G0 []) j))
                 (seq 0 (length P))))) idx16) idx16 in
  let X := solve 16 16 (transpose 16 ML) (transpose 16 N) in
  let Cq := transpose 16 X in
  let D := Z.lcm (den_lcm Cq) (den_lcm G0) in
  (map (map (to_Z D)) Cq, map (map (to_Z D)) G0, D).

Definition side_ok (M : list (list Z)) (vs : list (list Z)) : bool :=
  match build_cert M vs with
  | (C, G, d) => cert_ok M vs C G d
  end.

Theorem side_ok_sound M P : side_ok M P = true -> kernel_basis M P.
Proof.
  unfold side_ok. destruct (build_cert M P) as [[C G] d].
  apply cert_ok_sound.
Qed.

(** * The blades. *)

Definition blade_vec (b : blade_t) : tz 4 :=
  match b with (i, j, s) => blade 4 i j s end.

Fixpoint tz_flat (order : nat) : tz order -> list Z :=
  match order as o return tz o -> list Z with
  | O => fun a => [a]
  | S lower => fun a => tz_flat lower (fst a) ++ tz_flat lower (snd a)
  end.

Definition mat_of_cols (col : nat -> list Z) : list (list Z) :=
  map (fun i => map (fun j => nth i (col j) 0%Z) idx16) idx16.

Definition lmat (b : blade_t) : list (list Z) :=
  mat_of_cols (fun k => tz_flat 4 (tz_mul 4 (blade_vec b) (tz_basis 4 k))).

Definition rmat (b : blade_t) : list (list Z) :=
  mat_of_cols (fun k => tz_flat 4 (tz_mul 4 (tz_basis 4 k) (blade_vec b))).

Definition left_partners (b : blade_t) : list blade_t :=
  filter (fun v => blade_product_zero b v) blades16.

Definition right_partners (b : blade_t) : list blade_t :=
  filter (fun v => blade_product_zero v b) blades16.

Definition pmat (vs : list blade_t) : list (list Z) :=
  map (fun v => tz_flat 4 (blade_vec v)) vs.

Definition diag84 : list blade_t := filter is_assessor blades16.

Theorem flat_basis_is_unit :
  forallb (fun k =>
    if list_eq_dec Z.eq_dec (tz_flat 4 (tz_basis 4 k))
         (map (fun j => if Nat.eqb j k then 1%Z else 0%Z) idx16)
    then true else false) idx16 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem diag84_count : length diag84 = 84%nat.
Proof. vm_compute. reflexivity. Qed.


Definition blade_eq_dec : forall a b : blade_t, {a = b} + {a <> b}.
Proof. intros a b. repeat decide equality. Defined.

Lemma blades16_nodup : NoDup blades16.
Proof.
  assert (H : nodup blade_eq_dec blades16 = blades16)
    by (vm_compute; reflexivity).
  pose proof (NoDup_nodup blade_eq_dec blades16) as Hn.
  rewrite H in Hn. exact Hn.
Qed.

(** * Decisions. *)

Theorem all_blades_certified :
  forallb (fun b =>
    (side_ok (lmat b) (pmat (left_partners b))
     && side_ok (rmat b) (pmat (right_partners b)))%bool) blades16 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem partner_counts :
  forallb (fun b =>
    (Nat.eqb (length (left_partners b)) (if is_assessor b then 4 else 0)
     && Nat.eqb (length (right_partners b)) (if is_assessor b then 4 else 0))%bool)
    blades16 = true.
Proof. vm_compute. reflexivity. Qed.

Theorem diagonal_partners_are_diagonal :
  forallb (fun b =>
    (Nat.eqb (length (filter (fun v => blade_product_zero b v) diag84)) 4
     && Nat.eqb (length (filter (fun v => blade_product_zero v b) diag84)) 4
     && forallb (fun v => implb (blade_product_zero b v) (is_assessor v)) blades16
     && forallb (fun v => implb (blade_product_zero v b) (is_assessor v)) blades16)%bool)
    diag84 = true.
Proof. vm_compute. reflexivity. Qed.

(** * Results. *)

Theorem boxkite_annihilator_census : forall b, In b blades16 ->
  kernel_basis (lmat b) (pmat (left_partners b))
  /\ kernel_basis (rmat b) (pmat (right_partners b))
  /\ length (left_partners b) = (if is_assessor b then 4 else 0)%nat
  /\ length (right_partners b) = (if is_assessor b then 4 else 0)%nat.
Proof.
  intros b Hb.
  pose proof (proj1 (forallb_forall _ _) all_blades_certified b Hb) as H1.
  pose proof (proj1 (forallb_forall _ _) partner_counts b Hb) as H2.
  apply andb_true_iff in H1 as [H1a H1b].
  apply andb_true_iff in H2 as [H2a H2b].
  apply Nat.eqb_eq in H2a. apply Nat.eqb_eq in H2b.
  exact (conj (side_ok_sound _ _ H1a) (conj (side_ok_sound _ _ H1b) (conj H2a H2b))).
Qed.

Lemma in_diag84 b : In b diag84 -> In b blades16 /\ is_assessor b = true.
Proof. unfold diag84. intros H. apply filter_In in H. exact H. Qed.

Theorem C014_annihilator_dimension_four : forall b, In b diag84 ->
  kernel_basis (lmat b) (pmat (left_partners b))
  /\ kernel_basis (rmat b) (pmat (right_partners b))
  /\ length (left_partners b) = 4%nat
  /\ length (right_partners b) = 4%nat.
Proof.
  intros b Hb. destruct (in_diag84 b Hb) as [Hb1 Hb2].
  destruct (boxkite_annihilator_census b Hb1) as (K1 & K2 & N1 & N2).
  rewrite Hb2 in N1, N2. auto.
Qed.

Theorem C015_four_diagonal_partners : forall b, In b diag84 ->
  length (filter (fun v => blade_product_zero b v) diag84) = 4%nat
  /\ length (filter (fun v => blade_product_zero v b) diag84) = 4%nat
  /\ NoDup (filter (fun v => blade_product_zero b v) diag84)
  /\ NoDup (filter (fun v => blade_product_zero v b) diag84)
  /\ ~ In b (left_partners b) /\ ~ In b (right_partners b)
  /\ (forall v, In v (left_partners b) -> In v diag84)
  /\ (forall v, In v (right_partners b) -> In v diag84)
  /\ kernel_basis (lmat b) (pmat (left_partners b))
  /\ kernel_basis (rmat b) (pmat (right_partners b)).
Proof.
  intros b Hb. destruct (in_diag84 b Hb) as [Hb1 Hb2].
  pose proof (proj1 (forallb_forall _ _) diagonal_partners_are_diagonal b Hb) as H.
  apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [H H3].
  apply andb_true_iff in H as [H1 H2].
  apply Nat.eqb_eq in H1. apply Nat.eqb_eq in H2.
  destruct (boxkite_annihilator_census b Hb1) as (K1 & K2 & _ & _).
  assert (Hnd : NoDup diag84) by (exact (NoDup_filter is_assessor blades16_nodup)).
  assert (Hsq : negb (blade_product_zero b b) = true)
    by (exact (proj1 (forallb_forall _ _) no_blade_squares_to_zero b Hb1)).
  apply negb_true_iff in Hsq.
  refine (conj H1 (conj H2 (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ (conj K1 K2))))))))).
  - exact (NoDup_filter _ Hnd).
  - exact (NoDup_filter _ Hnd).
  - unfold left_partners. intros Hin. apply filter_In in Hin as [_ Hin]. cbv beta in Hin.
    rewrite Hsq in Hin. discriminate Hin.
  - unfold right_partners. intros Hin. apply filter_In in Hin as [_ Hin]. cbv beta in Hin.
    rewrite Hsq in Hin. discriminate Hin.
  - intros v Hv. unfold left_partners in Hv. apply filter_In in Hv as [Hv1 Hv2].
    pose proof (proj1 (forallb_forall _ _) H3 v Hv1) as H5.
    cbv beta in Hv2, H5. rewrite Hv2 in H5. simpl in H5. unfold diag84. apply filter_In. split; assumption.
  - intros v Hv. unfold right_partners in Hv. apply filter_In in Hv as [Hv1 Hv2].
    pose proof (proj1 (forallb_forall _ _) H4 v Hv1) as H5.
    cbv beta in Hv2, H5. rewrite Hv2 in H5. simpl in H5. unfold diag84. apply filter_In. split; assumption.
Qed.

(** Known-bad certificates: the checker rejects a perturbed d, C, G or
    kernel vector of an accepted certificate. *)

Definition bump (M : list (list Z)) : list (list Z) :=
  match M with
  | (x :: xs) :: rs => ((x + 1)%Z :: xs) :: rs
  | _ => M
  end.

Theorem cert_ok_rejects_mutants :
  let b := (1%nat, 10%nat, false) in
  let M := lmat b in
  let P := pmat (left_partners b) in
  match build_cert M P with
  | (C, G, d) =>
      cert_ok M P C G d = true
      /\ cert_ok M P C G (d + 1)%Z = false
      /\ cert_ok M P (bump C) G d = false
      /\ cert_ok M P C (bump G) d = false
      /\ cert_ok M (bump P) C G d = false
  end.
Proof. vm_compute. repeat split; reflexivity. Qed.

Print Assumptions C014_annihilator_dimension_four.
Print Assumptions C015_four_diagonal_partners.
Print Assumptions boxkite_annihilator_census.
