(** * C-010: the seven box-kites are the connected components of the
    zero-divisor graph, and k - 1 bridges join k components.

    Convention: the product is [sed_mul] of theories/Sedenion.v and the
    basis is [sed_e] (index 0 the unit, 1..7 the octonion half, 8..15 the
    second half), the order of C1467_XORSignCocycle.  An assessor is a pair
    (i, j) of [assessors] in theories/BoxKite.v; the vertex u of the graph
    is the u-th entry (0 <= u < 42), [vtx u].  Two assessors a = (i, j) and
    b = (k, l) are adjacent, [zd_adj a b], when
    (e_i + s e_j) (e_k + t e_l) = 0 in the sedenions for some s, t in
    {1, -1}.  A graph is a list of undirected edges on natural-number
    vertices, as in C010_ComponentBridgeBound, whose [Reach] is the
    reachability used throughout.

    Bridge to the product.  [sed_mul_basis] proves, for all 256 pairs of
    basis indices, e_i e_j = sed_sign(i, j) e_(i xor j) with the sign table
    of C1467_XORSignCocycle, by unfolding [sed_mul] to real coordinates.
    [sed_coord_product] then gives each of the 16 coordinates of
    (e_i + s e_j)(e_k + t e_l) as the integer [model], and
    [sed_pair_product_zero_iff] states that the product is zero exactly when
    all 16 integers vanish.  [zd_adj_iff_adjb] identifies [zd_adj] with the
    Boolean [adjb] that evaluates this model, so every adjacency below is
    decided on [sed_mul] through these two theorems and no product is
    asserted on a table alone.

    Graph.  [zd_edges] lists the edges (u, v), u < v < 42, with [adjb]
    true.  [zd_edges_adj_spec] ties the list to [zd_adj] in both
    directions and [zd_adj_symmetric] shows the relation is symmetric on
    the assessors.  [zd_graph_regular] gives every assessor degree 4, so no
    assessor is isolated, and [zd_edge_count] gives 84 edges.

    Components.  [box_comp] sends the vertex u to the index 0..6 of the
    box-kite of [boxkites] that holds the assessor.  [adjacent_same_boxkite]
    states that adjacent assessors lie in the same box-kite, so every edge
    joins two assessors of one box-kite.  [boxkite_connected] states that
    two assessors of one box-kite are joined by a path of edges, and
    [boxkites_are_components] that two assessors are joined by a path
    exactly when they lie in one box-kite.  [zd_graph_needs_six_bridges] is
    [bridge_lower_bound] of C010_ComponentBridgeBound applied to this graph
    and this labeling with no assumed premise.

    Sufficiency.  [bridges_suffice] is general: for internal edges and a
    labeling with labels 0 .. k - 1 whose label classes are nonempty and
    each connected by internal edges, there are k - 1 bridges, each between
    two listed vertices of different labels, after which every listed
    vertex is reachable from one vertex.  The k = 0 and k = 1 cases are
    [bridges_suffice_no_label] and [bridges_suffice_one_label].
    [bridges_necessary_and_sufficient] pairs it with the lower bound, and
    [six_bridges_connect_assessors] and [six_bridges_exactly] are the
    instance k = 7 on the 42 assessors.

    Scope: the adjacency is the existence of signs with a zero ordered
    product; no statement is made about the signs that realize an edge,
    about triples of assessors, or about the zero-divisor graphs of
    algebras of dimension above 16.  Reachability is proved from the
    listed edges only; the sufficiency theorem states existence of the
    bridges and the instance does not name them. *)

From Stdlib Require Import List Arith ZArith Reals Lia Lra Bool.
From OpenGororoba Require Import CayleyDicksonAlgebra Sedenion OctonionNorm BoxKite.
From OpenGororobaVerified Require Import C1467_XORSignCocycle C010_ComponentBridgeBound.
Import ListNotations.

Local Open Scope R_scope.

(** The two-blade (e_i + s e_j) of the sedenions of the tree. *)
Definition sed_pair (a : nat * nat) (s : R) : CDSed :=
  sed_add (sed_e (fst a)) (sed_scale s (sed_e (snd a))).

(** The 16 real coordinates of a sedenion in the order of [sed_e]:
    0..3 and 4..7 are the quaternion halves of [sed_lo], 8..15 those of
    [sed_hi]. *)
Definition sed_coord (n : nat) (x : CDSed) : R :=
  match n with
  | 0%nat => qa (oct_lo (sed_lo x))
  | 1%nat => qb (oct_lo (sed_lo x))
  | 2%nat => qc (oct_lo (sed_lo x))
  | 3%nat => qd (oct_lo (sed_lo x))
  | 4%nat => qa (oct_hi (sed_lo x))
  | 5%nat => qb (oct_hi (sed_lo x))
  | 6%nat => qc (oct_hi (sed_lo x))
  | 7%nat => qd (oct_hi (sed_lo x))
  | 8%nat => qa (oct_lo (sed_hi x))
  | 9%nat => qb (oct_lo (sed_hi x))
  | 10%nat => qc (oct_lo (sed_hi x))
  | 11%nat => qd (oct_lo (sed_hi x))
  | 12%nat => qa (oct_hi (sed_hi x))
  | 13%nat => qb (oct_hi (sed_hi x))
  | 14%nat => qc (oct_hi (sed_hi x))
  | 15%nat => qd (oct_hi (sed_hi x))
  | _ => 0
  end.

Ltac sed_cbv :=
  cbv [sed_mul sed_conj sed_scale sed_add sed_zero oct_mul oct_conj oct_scale oct_add oct_zero quat_mul quat_add quat_neg quat_conj quat_scale quat_zero quat_one sed_lo sed_hi oct_lo oct_hi qa qb qc qd].

Ltac coord_cbv :=
  cbv [sed_coord sed_mul sed_conj sed_scale sed_add sed_zero oct_mul oct_conj oct_scale oct_add oct_zero quat_mul quat_add quat_neg quat_conj quat_scale quat_zero quat_one sed_lo sed_hi oct_lo oct_hi qa qb qc qd ].

Lemma sed_coord_ext :
  forall x y : CDSed,
    (forall n, (n < 16)%nat -> sed_coord n x = sed_coord n y) -> x = y.
Proof.
  intros [[[x0 x1 x2 x3] [x4 x5 x6 x7]] [[x8 x9 x10 x11] [x12 x13 x14 x15]]] [[[y0 y1 y2 y3] [y4 y5 y6 y7]] [[y8 y9 y10 y11] [y12 y13 y14 y15]]] H.
  pose proof (H 0%nat ltac:(lia)) as E0.
  pose proof (H 1%nat ltac:(lia)) as E1.
  pose proof (H 2%nat ltac:(lia)) as E2.
  pose proof (H 3%nat ltac:(lia)) as E3.
  pose proof (H 4%nat ltac:(lia)) as E4.
  pose proof (H 5%nat ltac:(lia)) as E5.
  pose proof (H 6%nat ltac:(lia)) as E6.
  pose proof (H 7%nat ltac:(lia)) as E7.
  pose proof (H 8%nat ltac:(lia)) as E8.
  pose proof (H 9%nat ltac:(lia)) as E9.
  pose proof (H 10%nat ltac:(lia)) as E10.
  pose proof (H 11%nat ltac:(lia)) as E11.
  pose proof (H 12%nat ltac:(lia)) as E12.
  pose proof (H 13%nat ltac:(lia)) as E13.
  pose proof (H 14%nat ltac:(lia)) as E14.
  pose proof (H 15%nat ltac:(lia)) as E15.
  cbn in E0, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15.
  subst. reflexivity.
Qed.

Lemma sed_coord_zero : forall n, sed_coord n sed_zero = 0.
Proof.
  intros n. unfold sed_zero, oct_zero, quat_zero.
  do 16 (destruct n as [|n]; [reflexivity | ]).
  reflexivity.
Qed.

Lemma sed_coord_add :
  forall n x y, sed_coord n (sed_add x y) = sed_coord n x + sed_coord n y.
Proof.
  intros n x y.
  do 16 (destruct n as [|n]; [ coord_cbv; ring | ]).
  coord_cbv. ring.
Qed.

Lemma sed_coord_scale :
  forall n r x, sed_coord n (sed_scale r x) = r * sed_coord n x.
Proof.
  intros n r x.
  do 16 (destruct n as [|n]; [ coord_cbv; ring | ]).
  coord_cbv. ring.
Qed.
Lemma sed_coord_e :
  forall x n, (x < 16)%nat -> (n < 16)%nat ->
    sed_coord n (sed_e x) = if Nat.eqb x n then 1 else 0.
Proof.
  intros x n Hx Hn.
  do 16 (destruct x as [|x];
    [ do 16 (destruct n as [|n]; [ cbv; reflexivity | ]); exfalso; lia | ]).
  exfalso; lia.
Qed.

Lemma sed_mul_add_l :
  forall x y z, sed_mul (sed_add x y) z = sed_add (sed_mul x z) (sed_mul y z).
Proof.
  intros x y z. sed_cbv.
  apply (f_equal2 mkSed); apply (f_equal2 mkOct); apply (f_equal4 mkQuat); ring.
Qed.

Lemma sed_mul_add_r :
  forall x y z, sed_mul z (sed_add x y) = sed_add (sed_mul z x) (sed_mul z y).
Proof.
  intros x y z. sed_cbv.
  apply (f_equal2 mkSed); apply (f_equal2 mkOct); apply (f_equal4 mkQuat); ring.
Qed.

Lemma sed_mul_scale_l :
  forall r x y, sed_mul (sed_scale r x) y = sed_scale r (sed_mul x y).
Proof.
  intros r x y. sed_cbv.
  apply (f_equal2 mkSed); apply (f_equal2 mkOct); apply (f_equal4 mkQuat); ring.
Qed.

Lemma sed_mul_scale_r :
  forall r x y, sed_mul x (sed_scale r y) = sed_scale r (sed_mul x y).
Proof.
  intros r x y. sed_cbv.
  apply (f_equal2 mkSed); apply (f_equal2 mkOct); apply (f_equal4 mkQuat); ring.
Qed.

(** The product of two basis elements is the signed basis element of the
    XOR of the indices, with the sign of the table [sed_sign] of
    C1467_XORSignCocycle (which that file binds to the Cayley-Dickson sign
    recurrence).  All 256 index pairs are checked against [sed_mul]. *)
Theorem sed_mul_basis :
  forall i j, (i < 16)%nat -> (j < 16)%nat ->
    sed_mul (sed_e i) (sed_e j)
    = sed_scale (IZR (sed_sign i j)) (sed_e (Nat.lxor i j)).
Proof.
  intros i j Hi Hj.
  do 16 (destruct i as [|i];
    [ do 16 (destruct j as [|j]; [ cbv; apply (f_equal2 mkSed); apply (f_equal2 mkOct); apply (f_equal4 mkQuat); ring | ]); exfalso; lia | ]).
  exfalso; lia.
Qed.

Local Close Scope R_scope.

(** The integer model of the product of two blades.  [ind n x c] is c at
    coordinate x and 0 elsewhere; [model n i j k l zs zt] is the integer
    coordinate n of (e_i + zs e_j)(e_k + zt e_l) by the sign table. *)
Definition ind (n x : nat) (c : Z) : Z :=
  if Nat.eqb x n then c else 0%Z.

Definition model (n i j k l : nat) (zs zt : Z) : Z :=
  ((ind n (Nat.lxor i k) (sed_sign i k)
    + ind n (Nat.lxor i l) (zt * sed_sign i l))
   + (ind n (Nat.lxor j k) (zs * sed_sign j k)
      + ind n (Nat.lxor j l) (zs * (zt * sed_sign j l))))%Z.

Local Open Scope R_scope.

Lemma IZR_ind :
  forall n x c, IZR (ind n x c) = IZR c * (if Nat.eqb x n then 1 else 0).
Proof.
  intros n x c. unfold ind. destruct (Nat.eqb x n); simpl; ring.
Qed.

Lemma xor_lt_16 :
  forall i j, (i < 16)%nat -> (j < 16)%nat -> (Nat.lxor i j < 16)%nat.
Proof.
  intros i j Hi Hj.
  do 16 (destruct i as [|i];
    [ do 16 (destruct j as [|j]; [ cbv; lia | ]); exfalso; lia | ]).
  exfalso; lia.
Qed.

Theorem sed_coord_product :
  forall i j k l (zs zt : Z) n,
    (i < 16)%nat -> (j < 16)%nat -> (k < 16)%nat -> (l < 16)%nat ->
    (n < 16)%nat ->
    sed_coord n (sed_mul (sed_pair (i, j) (IZR zs)) (sed_pair (k, l) (IZR zt)))
    = IZR (model n i j k l zs zt).
Proof.
  intros i j k l zs zt n Hi Hj Hk Hl Hn.
  unfold sed_pair. cbn [fst snd].
  rewrite !sed_mul_add_l, !sed_mul_add_r, !sed_mul_scale_l, !sed_mul_scale_r.
  rewrite !sed_coord_add, !sed_coord_scale.
  rewrite (sed_mul_basis i k Hi Hk), (sed_mul_basis i l Hi Hl),
          (sed_mul_basis j k Hj Hk), (sed_mul_basis j l Hj Hl).
  rewrite !sed_coord_scale.
  rewrite (sed_coord_e _ n (xor_lt_16 i k Hi Hk) Hn),
          (sed_coord_e _ n (xor_lt_16 i l Hi Hl) Hn),
          (sed_coord_e _ n (xor_lt_16 j k Hj Hk) Hn),
          (sed_coord_e _ n (xor_lt_16 j l Hj Hl) Hn).
  unfold model.
  rewrite !plus_IZR, !IZR_ind, !mult_IZR.
  ring.
Qed.

Definition model_zero (i j k l : nat) (zs zt : Z) : bool :=
  forallb (fun n => Z.eqb (model n i j k l zs zt) 0%Z) (seq 0 16).

Theorem sed_pair_product_zero_iff :
  forall i j k l (zs zt : Z),
    (i < 16)%nat -> (j < 16)%nat -> (k < 16)%nat -> (l < 16)%nat ->
    sed_mul (sed_pair (i, j) (IZR zs)) (sed_pair (k, l) (IZR zt)) = sed_zero
    <-> model_zero i j k l zs zt = true.
Proof.
  intros i j k l zs zt Hi Hj Hk Hl. unfold model_zero.
  rewrite forallb_forall. split.
  - intros H n Hn. apply in_seq in Hn.
    apply Z.eqb_eq. apply eq_IZR.
    rewrite <- (sed_coord_product i j k l zs zt n Hi Hj Hk Hl) by lia.
    rewrite H. rewrite sed_coord_zero. reflexivity.
  - intros H. apply sed_coord_ext. intros n Hn.
    rewrite sed_coord_zero.
    rewrite (sed_coord_product i j k l zs zt n Hi Hj Hk Hl Hn).
    pose proof (H n ltac:(apply in_seq; lia)) as Hz.
    apply Z.eqb_eq in Hz. rewrite Hz. reflexivity.
Qed.

Local Open Scope R_scope.

(** Adjacency of two assessors: some signed pair of the two-blades
    multiplies to zero in the sedenions of the tree. *)
Definition zd_adj (a b : nat * nat) : Prop :=
  exists s t : R, (s = 1 \/ s = -1) /\ (t = 1 \/ t = -1) /\
    sed_mul (sed_pair a s) (sed_pair b t) = sed_zero.

Local Close Scope R_scope.

Definition signs : list Z := [1%Z; (-1)%Z].

Definition adjb (a b : nat * nat) : bool :=
  existsb (fun zs =>
    existsb (fun zt => model_zero (fst a) (snd a) (fst b) (snd b) zs zt) signs)
    signs.

Lemma sign_real :
  forall s : R, (s = 1%R \/ s = (-1)%R) ->
    exists zs, In zs signs /\ s = IZR zs.
Proof.
  intros s [H | H]; subst.
  - exists 1%Z. split; [simpl; auto | reflexivity].
  - exists (-1)%Z. split; [simpl; auto | reflexivity].
Qed.

Lemma real_sign :
  forall zs, In zs signs -> IZR zs = 1%R \/ IZR zs = (-1)%R.
Proof.
  intros zs [H | [H | []]]; subst; [left | right]; reflexivity.
Qed.

(** [zd_adj], stated with [sed_mul], is the Boolean [adjb] on the integer
    model. *)
Theorem zd_adj_iff_adjb :
  forall a b : nat * nat,
    (fst a < 16)%nat -> (snd a < 16)%nat -> (fst b < 16)%nat -> (snd b < 16)%nat ->
    zd_adj a b <-> adjb a b = true.
Proof.
  intros [i j] [k l] Hi Hj Hk Hl. cbn [fst snd] in *. unfold zd_adj, adjb. cbn [fst snd].
  split.
  - intros [s [t [Hs [Ht H]]]].
    destruct (sign_real s Hs) as [zs [Hzs Es]].
    destruct (sign_real t Ht) as [zt [Hzt Et]].
    subst s t.
    apply (proj1 (sed_pair_product_zero_iff i j k l zs zt Hi Hj Hk Hl)) in H.
    apply existsb_exists. exists zs. split; [exact Hzs |].
    apply existsb_exists. exists zt. split; [exact Hzt | exact H].
  - intros H. apply existsb_exists in H as [zs [Hzs H]].
    apply existsb_exists in H as [zt [Hzt H]].
    exists (IZR zs), (IZR zt).
    split; [exact (real_sign zs Hzs) |].
    split; [exact (real_sign zt Hzt) |].
    apply (proj2 (sed_pair_product_zero_iff i j k l zs zt Hi Hj Hk Hl)).
    exact H.
Qed.

(** The graph on the vertices 0 .. 41: vertex u is the assessor [vtx u]. *)
Definition vtx (u : nat) : nat * nat := nth u assessors (0%nat, 0%nat).

Definition adj_idx (u v : nat) : bool := adjb (vtx u) (vtx v).

Definition zd_edges : list edge :=
  flat_map
    (fun u =>
       map (fun v => (u, v))
         (filter (fun v => adj_idx u v) (seq (S u) (41 - u))))
    (seq 0 42).

Lemma zd_edges_iff :
  forall u v, In (u, v) zd_edges <->
    (u < v)%nat /\ (v < 42)%nat /\ adj_idx u v = true.
Proof.
  intros u v. unfold zd_edges. rewrite in_flat_map. split.
  - intros [u' [Hu' H]]. apply in_map_iff in H as [v' [E Hv']].
    injection E as E1 E2. subst u' v'.
    apply filter_In in Hv' as [Hv Ha]. apply in_seq in Hv. apply in_seq in Hu'.
    repeat split; [lia | lia | exact Ha].
  - intros [Huv [Hv Ha]]. exists u. split; [apply in_seq; lia |].
    apply in_map_iff. exists v. split; [reflexivity |].
    apply filter_In. split; [apply in_seq; lia | exact Ha].
Qed.

Lemma forall_lt :
  forall (n : nat) (P : nat -> bool),
    forallb P (seq 0 n) = true -> forall x, (x < n)%nat -> P x = true.
Proof.
  intros n P H x Hx. rewrite forallb_forall in H. apply H. apply in_seq. lia.
Qed.

Lemma vtx_lt_16 :
  forall u, (u < 42)%nat -> (fst (vtx u) < 16)%nat /\ (snd (vtx u) < 16)%nat.
Proof.
  assert (H : forallb (fun u => (fst (vtx u) <? 16)%nat && (snd (vtx u) <? 16)%nat)
                (seq 0 42) = true) by (vm_compute; reflexivity).
  intros u Hu. pose proof (forall_lt _ _ H u Hu) as E.
  apply andb_true_iff in E as [E1 E2].
  apply Nat.ltb_lt in E1. apply Nat.ltb_lt in E2. split; assumption.
Qed.

Theorem zd_adj_vtx_iff :
  forall u v, (u < 42)%nat -> (v < 42)%nat ->
    zd_adj (vtx u) (vtx v) <-> adj_idx u v = true.
Proof.
  intros u v Hu Hv.
  destruct (vtx_lt_16 u Hu) as [H1 H2]. destruct (vtx_lt_16 v Hv) as [H3 H4].
  exact (zd_adj_iff_adjb (vtx u) (vtx v) H1 H2 H3 H4).
Qed.

Theorem adj_idx_symmetric :
  forall u v, (u < 42)%nat -> (v < 42)%nat -> adj_idx u v = adj_idx v u.
Proof.
  assert (H : forallb (fun u => forallb (fun v =>
                Bool.eqb (adj_idx u v) (adj_idx v u)) (seq 0 42)) (seq 0 42) = true)
    by (vm_compute; reflexivity).
  intros u v Hu Hv.
  pose proof (forall_lt _ _ H u Hu) as E1. cbv beta in E1.
  pose proof (forall_lt _ _ E1 v Hv) as E2. cbv beta in E2.
  exact (proj1 (Bool.eqb_true_iff _ _) E2).
Qed.

(** The labeling: the index in [boxkites] of the box-kite that holds the
    assessor of vertex u. *)
Definition pair_eq_dec : forall a b : nat * nat, {a = b} + {a <> b}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Fixpoint bk_index (p : nat * nat) (bs : list (list (nat * nat))) : nat :=
  match bs with
  | [] => 0%nat
  | b :: r => if in_dec pair_eq_dec p b then 0%nat else S (bk_index p r)
  end.

Definition box_comp (u : nat) : nat := bk_index (vtx u) boxkites.

Theorem box_comp_spec :
  forall u, (u < 42)%nat ->
    (box_comp u < 7)%nat /\ In (vtx u) (nth (box_comp u) boxkites []).
Proof.
  assert (H : forallb (fun u =>
      (box_comp u <? 7)%nat &&
      (if in_dec pair_eq_dec (vtx u) (nth (box_comp u) boxkites []) then true
       else false)) (seq 0 42) = true) by (vm_compute; reflexivity).
  intros u Hu. pose proof (forall_lt _ _ H u Hu) as E. cbv beta in E.
  apply andb_true_iff in E as [E1 E2]. apply Nat.ltb_lt in E1.
  split; [exact E1 |].
  destruct (in_dec pair_eq_dec (vtx u) (nth (box_comp u) boxkites [])) as [Hin | Hin];
    [exact Hin | discriminate E2].
Qed.

Theorem box_comp_class_size :
  forall c, (c < 7)%nat ->
    length (filter (fun u => Nat.eqb (box_comp u) c) (seq 0 42)) = 6%nat.
Proof.
  assert (H : forallb (fun c =>
      Nat.eqb (length (filter (fun u => Nat.eqb (box_comp u) c) (seq 0 42))) 6)
      (seq 0 7) = true) by (vm_compute; reflexivity).
  intros c Hc. pose proof (forall_lt _ _ H c Hc) as E. cbv beta in E.
  apply Nat.eqb_eq in E. exact E.
Qed.

Theorem zd_edge_count : length zd_edges = 84%nat.
Proof. vm_compute. reflexivity. Qed.

(** Neighbors of a vertex along either direction of an edge. *)
Definition nbrs (es : list edge) (y : nat) : list nat :=
  map snd (filter (fun e => Nat.eqb (fst e) y) es)
  ++ map fst (filter (fun e => Nat.eqb (snd e) y) es).

Theorem zd_graph_regular :
  forall u, (u < 42)%nat -> length (nbrs zd_edges u) = 4%nat.
Proof.
  assert (H : forallb (fun u => Nat.eqb (length (nbrs zd_edges u)) 4)
                (seq 0 42) = true) by (vm_compute; reflexivity).
  intros u Hu. pose proof (forall_lt _ _ H u Hu) as E. cbv beta in E.
  apply Nat.eqb_eq in E. exact E.
Qed.

(** The edge list is the adjacency of the sedenion product, in both
    directions of the pair. *)
Theorem zd_edges_adj_spec :
  forall u v, (u < 42)%nat -> (v < 42)%nat -> u <> v ->
    (In (u, v) zd_edges \/ In (v, u) zd_edges) <-> zd_adj (vtx u) (vtx v).
Proof.
  intros u v Hu Hv Hne. rewrite (zd_adj_vtx_iff u v Hu Hv).
  rewrite !zd_edges_iff. split.
  - intros [[_ [_ H]] | [_ [_ H]]].
    + exact H.
    + rewrite adj_idx_symmetric by assumption. exact H.
  - intros H. destruct (Nat.lt_ge_cases u v) as [Hlt | Hge].
    + left. repeat split; [exact Hlt | exact Hv | exact H].
    + right. repeat split; [lia | exact Hu |].
      rewrite adj_idx_symmetric by assumption. exact H.
Qed.

Theorem zd_adj_symmetric :
  forall u v, (u < 42)%nat -> (v < 42)%nat ->
    zd_adj (vtx u) (vtx v) <-> zd_adj (vtx v) (vtx u).
Proof.
  intros u v Hu Hv.
  rewrite (zd_adj_vtx_iff u v Hu Hv), (zd_adj_vtx_iff v u Hv Hu).
  rewrite adj_idx_symmetric by assumption. reflexivity.
Qed.

(** (a) Adjacent assessors, and the two ends of every edge, lie in one
    box-kite. *)
Theorem adjacent_same_boxkite :
  forall u v, (u < 42)%nat -> (v < 42)%nat -> zd_adj (vtx u) (vtx v) ->
    box_comp u = box_comp v /\
    In (vtx u) (nth (box_comp u) boxkites []) /\
    In (vtx v) (nth (box_comp u) boxkites []).
Proof.
  assert (H : forallb (fun u => forallb (fun v =>
      implb (adj_idx u v) (Nat.eqb (box_comp u) (box_comp v))) (seq 0 42))
      (seq 0 42) = true) by (vm_compute; reflexivity).
  intros u v Hu Hv Hadj.
  apply (zd_adj_vtx_iff u v Hu Hv) in Hadj.
  pose proof (forall_lt _ _ H u Hu) as E1. cbv beta in E1.
  pose proof (forall_lt _ _ E1 v Hv) as E2. cbv beta in E2.
  rewrite Hadj in E2. cbn [implb] in E2. apply Nat.eqb_eq in E2.
  destruct (box_comp_spec u Hu) as [_ Hmu]. destruct (box_comp_spec v Hv) as [_ Hmv].
  rewrite <- E2 in Hmv. repeat split; assumption.
Qed.

Theorem zd_edge_same_boxkite :
  forall u v, In (u, v) zd_edges ->
    (u < 42)%nat /\ (v < 42)%nat /\ box_comp u = box_comp v.
Proof.
  intros u v H. destruct (proj1 (zd_edges_iff u v) H) as [Huv [Hv Ha]].
  assert (Hu : (u < 42)%nat) by lia.
  repeat split; try assumption.
  apply (adjacent_same_boxkite u v Hu Hv).
  apply (zd_adj_vtx_iff u v Hu Hv). exact Ha.
Qed.

(** Reachability, computed by saturation of a vertex list and certified
    sound for [Reach]. *)
Definition expand (es : list edge) (ws : list nat) : list nat :=
  nodup Nat.eq_dec (ws ++ flat_map (nbrs es) ws).

Fixpoint saturate (fuel : nat) (es : list edge) (ws : list nat) : list nat :=
  match fuel with
  | 0%nat => ws
  | S f => saturate f es (expand es ws)
  end.

Lemma nbrs_edge :
  forall es y z, In z (nbrs es y) -> In (y, z) es \/ In (z, y) es.
Proof.
  intros es y z H. unfold nbrs in H. apply in_app_or in H as [H | H].
  - apply in_map_iff in H as [[a b] [E Hab]]. simpl in E. subst b.
    apply filter_In in Hab as [Hin Hf]. simpl in Hf. apply Nat.eqb_eq in Hf.
    subst a. left. exact Hin.
  - apply in_map_iff in H as [[a b] [E Hab]]. simpl in E. subst a.
    apply filter_In in Hab as [Hin Hf]. simpl in Hf. apply Nat.eqb_eq in Hf.
    subst b. right. exact Hin.
Qed.

Lemma expand_reach :
  forall es ws x, In x (expand es ws) -> Reach es ws x.
Proof.
  intros es ws x H. unfold expand in H. apply nodup_In in H.
  apply in_app_or in H as [H | H].
  - apply reach_start. exact H.
  - apply in_flat_map in H as [y [Hy Hx]].
    apply (reach_step es ws y x); [apply reach_start; exact Hy |].
    apply nbrs_edge. exact Hx.
Qed.

Lemma saturate_sound :
  forall fuel es ws x, In x (saturate fuel es ws) -> Reach es ws x.
Proof.
  induction fuel as [|f IH]; intros es ws x H; simpl in H.
  - apply reach_start. exact H.
  - apply (reach_through es ws (expand es ws) x);
      [intros y Hy; apply expand_reach; exact Hy | exact (IH _ _ _ H)].
Qed.

(** (b) Two assessors of one box-kite are joined by a path of edges. *)
Lemma implb_elim : forall a b : bool, implb a b = true -> a = true -> b = true.
Proof. intros [|] [|]; simpl; congruence. Qed.

(** The kernel checks this equation by its virtual machine ([<:]), the same
    kernel and the same trust as conversion by reduction.  The statement
    is written out, not named by a definition: a named statement makes the
    kernel unfold it while it checks a later use. *)
Lemma boxkite_conn_check_true :
  forallb (fun u => forallb (fun v =>
      implb (Nat.eqb (box_comp u) (box_comp v))
            (existsb (Nat.eqb v) (saturate 3 zd_edges [u]))) (seq 0 42))
    (seq 0 42) = true.
Proof. exact (eq_refl true <: (forallb (fun u => forallb (fun v =>
      implb (Nat.eqb (box_comp u) (box_comp v))
            (existsb (Nat.eqb v) (saturate 3 zd_edges [u]))) (seq 0 42))
    (seq 0 42) = true)). Qed.

Theorem boxkite_connected :
  forall u v, (u < 42)%nat -> (v < 42)%nat -> box_comp u = box_comp v ->
    Reach zd_edges [u] v.
Proof.
  intros u v Hu Hv Hc.
  pose proof (forall_lt _ _ boxkite_conn_check_true u Hu) as E1. cbv beta in E1.
  pose proof (forall_lt _ _ E1 v Hv) as E2. cbv beta in E2.
  pose proof (implb_elim _ _ E2 (proj2 (Nat.eqb_eq _ _) Hc)) as E3.
  apply existsb_exists in E3 as [x [Hx Ex]]. apply Nat.eqb_eq in Ex. subst x.
  exact (saturate_sound _ _ _ _ Hx).
Qed.

Theorem boxkite_in_closure :
  forall u v, (u < 42)%nat -> (v < 42)%nat -> box_comp u = box_comp v ->
    In v (closure zd_edges [u]).
Proof.
  intros u v Hu Hv Hc. apply closure_complete. exact (boxkite_connected u v Hu Hv Hc).
Qed.

Lemma reach_same_boxkite :
  forall u v, Reach zd_edges [u] v -> box_comp v = box_comp u.
Proof.
  intros u v H. induction H as [x Hx | y z Hy IHy Hyz].
  - destruct Hx as [E | []]. subst x. reflexivity.
  - destruct Hyz as [Hyz | Hyz];
      destruct (zd_edge_same_boxkite _ _ Hyz) as [_ [_ E]]; congruence.
Qed.

Theorem boxkites_are_components :
  forall u v, (u < 42)%nat -> (v < 42)%nat ->
    box_comp u = box_comp v <-> Reach zd_edges [u] v.
Proof.
  intros u v Hu Hv. split.
  - exact (boxkite_connected u v Hu Hv).
  - intros H. symmetry. exact (reach_same_boxkite u v H).
Qed.

(** The labeling meets the hypotheses of [bridge_lower_bound]. *)
Lemma box_comp_internal :
  forall e, In e zd_edges -> box_comp (fst e) = box_comp (snd e).
Proof.
  intros [u v] H. cbn [fst snd]. destruct (zd_edge_same_boxkite u v H) as [_ [_ E]]. exact E.
Qed.

Lemma box_comp_cover :
  forall c, (c < 7)%nat ->
    exists x, In x (seq 0 42) /\ box_comp x = c.
Proof.
  assert (H : forallb (fun c => existsb (fun x => Nat.eqb (box_comp x) c)
                (seq 0 42)) (seq 0 7) = true) by (vm_compute; reflexivity).
  intros c Hc. pose proof (forall_lt _ _ H c Hc) as E. cbv beta in E.
  apply existsb_exists in E as [x [Hx Ex]]. apply Nat.eqb_eq in Ex.
  exists x. split; assumption.
Qed.

Theorem zd_graph_needs_six_bridges :
  forall (v0 : nat) (bridges : list edge),
    (forall x, (x < 42)%nat -> Reach (zd_edges ++ bridges) [v0] x) ->
    (6 <= length bridges)%nat.
Proof.
  intros v0 bridges H.
  exact (bridge_lower_bound 7 box_comp (seq 0 42) v0 zd_edges bridges
           box_comp_internal
           (fun x Hx => H x ltac:(apply in_seq in Hx; lia))
           box_comp_cover).
Qed.

(** * Sufficiency on a graph given by edges and a labeling. *)

Definition bridge_ok (comp : nat -> nat) (vs : list nat) (e : edge) : Prop :=
  In (fst e) vs /\ In (snd e) vs /\ comp (fst e) <> comp (snd e).

(** The vertices of [vs] labeled c form a nonempty class whose vertices
    are all reachable from one of them along the internal edges alone. *)
Definition label_class_connected
  (comp : nat -> nat) (vs : list nat) (internal : list edge) (c : nat) : Prop :=
  exists r, In r vs /\ comp r = c /\
    forall x, In x vs -> comp x = c -> Reach internal [r] x.

Lemma bridges_up_to :
  forall (comp : nat -> nat) (vs : list nat) (internal : list edge)
         (k r0 : nat),
    (forall c, (c < k)%nat -> label_class_connected comp vs internal c) ->
    In r0 vs -> comp r0 = 0%nat ->
    (forall x, In x vs -> comp x = 0%nat -> Reach internal [r0] x) ->
    forall m, (1 <= m)%nat -> (m <= k)%nat ->
      exists B : list edge,
        length B = (m - 1)%nat /\
        (forall e, In e B -> bridge_ok comp vs e) /\
        (forall x, In x vs -> (comp x < m)%nat -> Reach (internal ++ B) [r0] x).
Proof.
  intros comp vs internal k r0 Hcls Hr0 Hc0 Hconn0 m.
  induction m as [|m IH]; intros Hm1 Hmk.
  - lia.
  - destruct m as [|m'].
    + exists []. split; [reflexivity |]. split; [intros e [] |].
      intros x Hx Hxm. assert (E : comp x = 0%nat) by lia.
      apply (reach_more_edges internal);
        [intros e He; apply in_or_app; left; exact He | exact (Hconn0 x Hx E)].
    + destruct (IH ltac:(lia) ltac:(lia)) as [B [HlenB [HokB HreachB]]].
      destruct (Hcls (S m') ltac:(lia)) as [r [Hr [Hcr Hconn]]].
      exists (B ++ [(r0, r)]).
      assert (Hincl : forall e, In e (internal ++ B) ->
                In e (internal ++ (B ++ [(r0, r)]))).
      { intros e He. apply in_or_app. apply in_app_or in He as [He | He];
          [left; exact He | right; apply in_or_app; left; exact He]. }
      split; [| split].
      * rewrite length_app, HlenB. simpl. lia.
      * intros e He. apply in_app_or in He as [He | [He | []]].
        -- exact (HokB e He).
        -- subst e. unfold bridge_ok. simpl. split; [exact Hr0 |].
           split; [exact Hr |]. rewrite Hc0, Hcr. discriminate.
      * intros x Hx Hxm.
        destruct (Nat.lt_ge_cases (comp x) (S m')) as [Hlt | Hge].
        -- exact (reach_more_edges _ _ _ _ Hincl (HreachB x Hx Hlt)).
        -- assert (E : comp x = S m') by lia.
           assert (Hedge : In (r0, r) (internal ++ (B ++ [(r0, r)]))).
           { apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
           assert (Hrr : Reach (internal ++ (B ++ [(r0, r)])) [r0] r).
           { apply (reach_step _ _ r0 r); [apply reach_start; left; reflexivity |].
             left. exact Hedge. }
           apply (reach_through _ [r0] [r] x).
           ++ intros y [Hy | []]. subst y. exact Hrr.
           ++ apply (reach_more_edges internal).
              ** intros e He. apply in_or_app. left. exact He.
              ** exact (Hconn x Hx E).
Qed.

(** k - 1 bridges join k connected label classes. *)
Theorem bridges_suffice :
  forall (k : nat) (comp : nat -> nat) (vs : list nat) (internal : list edge),
    (forall x, In x vs -> (comp x < k)%nat) ->
    (forall c, (c < k)%nat -> label_class_connected comp vs internal c) ->
    exists (v0 : nat) (B : list edge),
      length B = (k - 1)%nat /\
      (forall e, In e B -> bridge_ok comp vs e) /\
      (forall x, In x vs -> Reach (internal ++ B) [v0] x).
Proof.
  intros k comp vs internal Hlab Hcls.
  destruct k as [|k'].
  - exists 0%nat, []. split; [reflexivity |]. split; [intros e [] |].
    intros x Hx. pose proof (Hlab x Hx). lia.
  - destruct (Hcls 0%nat ltac:(lia)) as [r0 [Hr0 [Hc0 Hconn0]]].
    destruct (bridges_up_to comp vs internal (S k') r0 Hcls Hr0 Hc0 Hconn0
                (S k') ltac:(lia) ltac:(lia)) as [B [Hlen [Hok Hreach]]].
    exists r0, B. split; [exact Hlen | split; [exact Hok |]].
    intros x Hx. exact (Hreach x Hx (Hlab x Hx)).
Qed.

(** No label: no vertex is listed and the empty list of bridges suffices. *)
Theorem bridges_suffice_no_label :
  forall (comp : nat -> nat) (vs : list nat) (internal : list edge),
    (forall x, In x vs -> (comp x < 0)%nat) ->
    vs = [] /\
    exists v0 : nat, forall x, In x vs -> Reach (internal ++ []) [v0] x.
Proof.
  intros comp vs internal H. split.
  - destruct vs as [|x r]; [reflexivity |].
    pose proof (H x (or_introl eq_refl)). lia.
  - exists 0%nat. intros x Hx. pose proof (H x Hx). lia.
Qed.

(** One label: the internal edges alone connect the listed vertices. *)
Theorem bridges_suffice_one_label :
  forall (comp : nat -> nat) (vs : list nat) (internal : list edge),
    (forall x, In x vs -> (comp x < 1)%nat) ->
    label_class_connected comp vs internal 0%nat ->
    exists v0 : nat, forall x, In x vs -> Reach internal [v0] x.
Proof.
  intros comp vs internal Hlab Hcls.
  destruct (bridges_suffice 1 comp vs internal Hlab
              (fun c Hc => match c return (c < 1)%nat -> _ with
                           | 0%nat => fun _ => Hcls
                           | S _ => fun H => ltac:(exfalso; lia)
                           end Hc))
    as [v0 [B [Hlen [_ Hreach]]]].
  assert (HB : B = []) by (destruct B; [reflexivity | simpl in Hlen; discriminate]).
  subst B. exists v0. intros x Hx. rewrite app_nil_r in Hreach. exact (Hreach x Hx).
Qed.

(** k - 1 bridges are necessary and sufficient. *)
Theorem bridges_necessary_and_sufficient :
  forall (k : nat) (comp : nat -> nat) (vs : list nat) (internal : list edge),
    (forall e, In e internal -> comp (fst e) = comp (snd e)) ->
    (forall x, In x vs -> (comp x < k)%nat) ->
    (forall c, (c < k)%nat -> label_class_connected comp vs internal c) ->
    (exists (v0 : nat) (B : list edge),
       length B = (k - 1)%nat /\
       (forall e, In e B -> bridge_ok comp vs e) /\
       (forall x, In x vs -> Reach (internal ++ B) [v0] x)) /\
    (forall (v0 : nat) (B : list edge),
       (forall x, In x vs -> Reach (internal ++ B) [v0] x) ->
       (k - 1 <= length B)%nat).
Proof.
  intros k comp vs internal Hint Hlab Hcls. split.
  - exact (bridges_suffice k comp vs internal Hlab Hcls).
  - intros v0 B Hconn.
    apply (bridge_lower_bound k comp vs v0 internal B Hint Hconn).
    intros c Hc. destruct (Hcls c Hc) as [r [Hr [Hcr _]]].
    exists r. split; assumption.
Qed.

(** The instance: the 42 assessors, the box-kite labeling, the edges of
    the zero-divisor graph. *)
Lemma box_comp_class_connected :
  forall c, (c < 7)%nat ->
    label_class_connected box_comp (seq 0 42) zd_edges c.
Proof.
  intros c Hc. destruct (box_comp_cover c Hc) as [r [Hr Hcr]].
  exists r. split; [exact Hr | split; [exact Hcr |]].
  intros x Hx Hxc. apply in_seq in Hr. apply in_seq in Hx.
  apply boxkite_connected; [lia | lia | congruence].
Qed.

Theorem six_bridges_connect_assessors :
  exists (v0 : nat) (B : list edge),
    length B = 6%nat /\
    (forall e, In e B ->
       (fst e < 42)%nat /\ (snd e < 42)%nat /\
       box_comp (fst e) <> box_comp (snd e)) /\
    (forall x, (x < 42)%nat -> Reach (zd_edges ++ B) [v0] x).
Proof.
  destruct (bridges_suffice 7 box_comp (seq 0 42) zd_edges)
    as [v0 [B [Hlen [Hok Hreach]]]].
  - intros x Hx. apply in_seq in Hx. exact (proj1 (box_comp_spec x ltac:(lia))).
  - exact box_comp_class_connected.
  - exists v0, B. split; [exact Hlen | split].
    + intros e He. destruct (Hok e He) as [H1 [H2 H3]].
      apply in_seq in H1. apply in_seq in H2. repeat split; try lia; exact H3.
    + intros x Hx. apply Hreach. apply in_seq. lia.
Qed.

(** Six bridges connect the 42 assessors, and no list of fewer does. *)
Theorem six_bridges_exactly :
  (exists (v0 : nat) (B : list edge),
     length B = 6%nat /\
     forall x, (x < 42)%nat -> Reach (zd_edges ++ B) [v0] x) /\
  (forall (v0 : nat) (B : list edge),
     (forall x, (x < 42)%nat -> Reach (zd_edges ++ B) [v0] x) ->
     (6 <= length B)%nat).
Proof.
  split.
  - destruct six_bridges_connect_assessors as [v0 [B [Hlen [_ H]]]].
    exists v0, B. split; assumption.
  - exact zd_graph_needs_six_bridges.
Qed.

Print Assumptions sed_mul_basis.
Print Assumptions sed_coord_product.
Print Assumptions sed_pair_product_zero_iff.
Print Assumptions zd_adj_iff_adjb.
Print Assumptions zd_edges_adj_spec.
Print Assumptions zd_adj_symmetric.
Print Assumptions zd_graph_regular.
Print Assumptions zd_edge_count.
Print Assumptions adjacent_same_boxkite.
Print Assumptions zd_edge_same_boxkite.
Print Assumptions boxkite_connected.
Print Assumptions boxkites_are_components.
Print Assumptions zd_graph_needs_six_bridges.
Print Assumptions bridges_suffice.
Print Assumptions bridges_suffice_no_label.
Print Assumptions bridges_suffice_one_label.
Print Assumptions bridges_necessary_and_sufficient.
Print Assumptions six_bridges_connect_assessors.
Print Assumptions six_bridges_exactly.
