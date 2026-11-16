(** * C-1141: counting identities of the zero-divisor graph at even dimension.

    Convention: dim = 2 * h is the dimension of a Cayley-Dickson algebra.
    The graph on the basis indices 0 .. dim-1 has a giant component of
    dim - 2 vertices and the two singleton components {0} and {dim / 2}.
    Inside the giant component the missing edges are the involution pairs
    (i, i xor dim/2) for i in 1 .. dim/2 - 1, and the edge count is that of
    the complete graph on dim - 2 vertices minus the missing edges.  The
    module defines these counts as functions of dim and proves their
    identities for every even dim >= 4.  It defines no graph on the basis
    indices and proves no statement about a zero-divisor product, so the
    reading of these counts as properties of the zero-divisor graph is not
    formalized.  The axiom zd_graph_three_components of
    C958_ZDGraphTopology.v does not formalize it either: it equates the
    count definitions of that file with constants and names no graph,
    adjacency or edge.

    The module proves:
    - the involution pairs of half = 2^k are the pairs (i, i + half) for
      i in 1 .. half - 1, and there are half - 1 of them;
    - dim = (dim - 2) + 2: the giant component and the two singletons hold
      every basis index;
    - the edge count (dim - 2)(dim - 4)/2 equals the complete graph on
      dim - 2 vertices minus the dim/2 - 1 missing edges, and equals
      (dim^2 - 6 dim + 8)/2 for dim >= 6;
    - the density of the giant component, 2 * edges / ((dim - 2)(dim - 3)),
      is (dim - 4)/(dim - 3): strictly increasing in dim, with complement
      1/(dim - 3);
    - the dim/2 - 1 missing involution pairs inside the giant component,
      divided by the (dim - 1)(dim - 2)/2 pairs of the dim - 1 nonzero
      indices, give 1/(dim - 1): strictly decreasing in dim.  The numerator
      counts only those involution pairs; under the graph convention above
      the singleton dim/2 lacks its dim - 2 pairs with the giant component
      as well, so the missing pairs among the nonzero indices number
      dim/2 - 1 + (dim - 2) (21 of 105 at dim = 16).

    The density ratio 3720/3906 at dim = 64 in C1141_ZDGraphGeneralStructure
    divides by (dim - 2)(dim - 1) = 62 * 63, while dim = 16 and dim = 32 divide
    by (dim - 2)(dim - 3); the giant-component density at dim = 64 is
    3720/3782. *)

From Stdlib Require Import List Arith PeanoNat Lia Bool.
Import ListNotations.

(** * Involution pairs. *)

Lemma testbit_below_pow2 : forall i k : nat,
  i < 2 ^ k -> Nat.testbit i k = false.
Proof.
  intros i k Hi.
  apply (Nat.testbit_unique i k false i 0).
  - exact Hi.
  - simpl. lia.
Qed.

Lemma land_below_pow2 : forall i k : nat,
  i < 2 ^ k -> Nat.land i (2 ^ k) = 0.
Proof.
  intros i k Hi. apply Nat.bits_inj. unfold Nat.eqf. intro n.
  rewrite Nat.land_spec, Nat.bits_0, Nat.pow2_bits_eqb.
  destruct (k =? n) eqn:E.
  - apply Nat.eqb_eq in E. subst n.
    rewrite (testbit_below_pow2 i k Hi). reflexivity.
  - apply andb_false_r.
Qed.

Lemma lxor_pow2_above : forall i k : nat,
  i < 2 ^ k -> Nat.lxor i (2 ^ k) = i + 2 ^ k.
Proof.
  intros i k Hi. symmetry. apply Nat.add_nocarry_lxor.
  apply land_below_pow2. exact Hi.
Qed.

Definition involution_pairs (half : nat) : list (nat * nat) :=
  map (fun i => (i, Nat.lxor i half)) (seq 1 (half - 1)).

Theorem involution_pair_count : forall half : nat,
  length (involution_pairs half) = half - 1.
Proof.
  intro half. unfold involution_pairs.
  rewrite length_map, length_seq. reflexivity.
Qed.

Theorem involution_pair_partner : forall k : nat, forall p : nat * nat,
  In p (involution_pairs (2 ^ k)) ->
  1 <= fst p /\ fst p < 2 ^ k /\ snd p = fst p + 2 ^ k.
Proof.
  intros k p Hin. unfold involution_pairs in Hin.
  apply in_map_iff in Hin. destruct Hin as [i [Hp Hi]].
  apply in_seq in Hi. subst p. simpl.
  assert (Hlt : i < 2 ^ k) by lia.
  split; [lia |]. split; [exact Hlt |].
  apply lxor_pow2_above. exact Hlt.
Qed.

(** * Counts as functions of the dimension. *)

Definition zd_giant_vertices (dim : nat) : nat := dim - 2.
Definition zd_singleton_vertices : nat := 2.
Definition zd_complete_edges (n : nat) : nat := n * (n - 1) / 2.
Definition zd_missing_edges (dim : nat) : nat := dim / 2 - 1.
Definition zd_edges (dim : nat) : nat := (dim - 2) * (dim - 4) / 2.

Theorem zd_vertices_partition : forall dim : nat,
  2 <= dim -> zd_giant_vertices dim + zd_singleton_vertices = dim.
Proof. intros dim H. unfold zd_giant_vertices, zd_singleton_vertices. lia. Qed.

Lemma div2_of_double : forall x : nat, 2 * x / 2 = x.
Proof. intro x. rewrite Nat.mul_comm. apply Nat.div_mul. discriminate. Qed.

Theorem zd_edges_complete_minus_missing : forall h : nat,
  2 <= h ->
  zd_edges (2 * h) =
  zd_complete_edges (zd_giant_vertices (2 * h)) - zd_missing_edges (2 * h).
Proof.
  intros h Hh.
  assert (Hm : exists m, h = m + 2) by (exists (h - 2); lia).
  destruct Hm as [m ->].
  unfold zd_edges, zd_complete_edges, zd_giant_vertices, zd_missing_edges.
  replace (2 * (m + 2) - 2) with (2 * (m + 1)) by lia.
  replace (2 * (m + 2) - 4) with (2 * m) by lia.
  replace (2 * (m + 1) - 1) with (2 * m + 1) by lia.
  replace (2 * (m + 2) / 2 - 1) with (m + 1) by (rewrite div2_of_double; lia).
  replace (2 * (m + 1) * (2 * m + 1)) with (2 * ((m + 1) * (2 * m + 1))) by ring.
  replace (2 * (m + 1) * (2 * m)) with (2 * ((m + 1) * (2 * m))) by ring.
  rewrite !div2_of_double.
  replace ((m + 1) * (2 * m + 1)) with ((m + 1) * (2 * m) + (m + 1)) by ring.
  lia.
Qed.

Theorem zd_edges_expanded : forall dim : nat,
  6 <= dim -> zd_edges dim = (dim * dim - 6 * dim + 8) / 2.
Proof.
  intros dim H. unfold zd_edges.
  assert (Hd : exists e, dim = e + 6) by (exists (dim - 6); lia).
  destruct Hd as [e ->].
  replace (e + 6 - 2) with (e + 4) by lia.
  replace (e + 6 - 4) with (e + 2) by lia.
  replace ((e + 6) * (e + 6) - 6 * (e + 6) + 8) with ((e + 4) * (e + 2)).
  - reflexivity.
  - replace ((e + 6) * (e + 6)) with (6 * (e + 6) + e * (e + 6)) by ring.
    replace (6 * (e + 6) + e * (e + 6) - 6 * (e + 6)) with (e * (e + 6)) by lia.
    ring.
Qed.

(** * Density of the giant component. *)

Definition zd_giant_pairs (dim : nat) : nat :=
  (dim - 2) * (dim - 3).

Lemma zd_edges_even : forall h : nat,
  2 <= h -> zd_edges (2 * h) = 2 * ((h - 1) * (h - 2)).
Proof.
  intros h Hh.
  assert (Hm : exists m, h = m + 2) by (exists (h - 2); lia).
  destruct Hm as [m ->].
  unfold zd_edges.
  replace (2 * (m + 2) - 2) with (2 * (m + 1)) by lia.
  replace (2 * (m + 2) - 4) with (2 * m) by lia.
  replace (m + 2 - 1) with (m + 1) by lia.
  replace (m + 2 - 2) with m by lia.
  replace (2 * (m + 1) * (2 * m)) with (2 * (2 * ((m + 1) * m))) by ring.
  rewrite div2_of_double. reflexivity.
Qed.

(** The density of the giant component is (dim - 4)/(dim - 3), and its
    complement is 1/(dim - 3). *)
Theorem zd_giant_density_closed_form : forall h : nat,
  2 <= h ->
  2 * zd_edges (2 * h) * (2 * h - 3) = (2 * h - 4) * zd_giant_pairs (2 * h) /\
  (2 * h - 3) - (2 * h - 4) = 1.
Proof.
  intros h Hh. split.
  - rewrite zd_edges_even by exact Hh. unfold zd_giant_pairs.
    assert (Hm : exists m, h = m + 2) by (exists (h - 2); lia).
    destruct Hm as [m ->].
    replace (2 * (m + 2) - 2) with (2 * (m + 1)) by lia.
    replace (2 * (m + 2) - 3) with (2 * m + 1) by lia.
    replace (2 * (m + 2) - 4) with (2 * m) by lia.
    replace (m + 2 - 1) with (m + 1) by lia.
    replace (m + 2 - 2) with m by lia.
    ring.
  - lia.
Qed.

Theorem zd_giant_density_strictly_increasing : forall h1 h2 : nat,
  2 <= h1 -> h1 < h2 ->
  (2 * h1 - 4) * (2 * h2 - 3) < (2 * h2 - 4) * (2 * h1 - 3).
Proof.
  intros h1 h2 H1 H12.
  assert (Ha : exists a b, h1 = a + 2 /\ h2 = a + b + 3)
    by (exists (h1 - 2), (h2 - h1 - 1); lia).
  destruct Ha as [a [b [-> ->]]].
  replace (2 * (a + 2) - 4) with (2 * a) by lia.
  replace (2 * (a + 2) - 3) with (2 * a + 1) by lia.
  replace (2 * (a + b + 3) - 4) with (2 * a + 2 * b + 2) by lia.
  replace (2 * (a + b + 3) - 3) with (2 * a + 2 * b + 3) by lia.
  nia.
Qed.

(** * Fraction of missing edges. *)

Theorem zd_missing_fraction_closed_form : forall h : nat,
  2 <= h ->
  zd_missing_edges (2 * h) * (2 * h - 1) = zd_complete_edges (2 * h - 1).
Proof.
  intros h Hh.
  assert (Hm : exists m, h = m + 2) by (exists (h - 2); lia).
  destruct Hm as [m ->].
  unfold zd_missing_edges, zd_complete_edges.
  replace (2 * (m + 2) / 2 - 1) with (m + 1) by (rewrite div2_of_double; lia).
  replace (2 * (m + 2) - 1) with (2 * m + 3) by lia.
  replace (2 * m + 3 - 1) with (2 * (m + 1)) by lia.
  replace ((2 * m + 3) * (2 * (m + 1))) with (2 * ((m + 1) * (2 * m + 3))) by ring.
  rewrite div2_of_double. ring.
Qed.

Theorem zd_missing_fraction_strictly_decreasing : forall h1 h2 : nat,
  2 <= h1 -> h1 < h2 ->
  zd_missing_edges (2 * h2) * zd_complete_edges (2 * h1 - 1) <
  zd_missing_edges (2 * h1) * zd_complete_edges (2 * h2 - 1).
Proof.
  intros h1 h2 H1 H12.
  pose proof (zd_missing_fraction_closed_form h1 H1) as E1.
  pose proof (zd_missing_fraction_closed_form h2 ltac:(lia)) as E2.
  rewrite <- E1, <- E2.
  unfold zd_missing_edges.
  assert (Ha : exists a b, h1 = a + 2 /\ h2 = a + b + 3)
    by (exists (h1 - 2), (h2 - h1 - 1); lia).
  destruct Ha as [a [b [-> ->]]].
  replace (2 * (a + 2) / 2 - 1) with (a + 1) by (rewrite div2_of_double; lia).
  replace (2 * (a + b + 3) / 2 - 1) with (a + b + 2) by (rewrite div2_of_double; lia).
  replace (2 * (a + 2) - 1) with (2 * a + 3) by lia.
  replace (2 * (a + b + 3) - 1) with (2 * a + 2 * b + 5) by lia.
  nia.
Qed.
