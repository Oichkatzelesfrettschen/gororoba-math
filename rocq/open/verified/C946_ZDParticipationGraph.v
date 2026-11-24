(** * C-946: the zero-divisor participation graph of the sedenions.

    Convention.  The algebra is level 4 of the integer Cayley-Dickson tower
    [tz] of [C1468_SlotEmbeddingAllPairs], with the product [tz_mul]:
    (a, b)(c, d) = (a c - conj(d) b, d a + b conj(c)).  The unit e_i is
    [tz_basis 4 i] for an index [i < 16], and e_i e_j = +- e_(i xor j).  A
    2-blade is e_i + e_j or e_i - e_j with i < j ([blades16], 240 of them).

    The graph.  The vertices are the 16 indices.  This file reads the
    graph as the enumeration of cd_kernel's [find_zero_divisors_parallel]
    followed by [zd_graph_topology_sign_table] of
    crates/materials_core/src/e8_crystal_bridge.rs in gororoba-open, which
    answers claim C-946 of registry/claims.toml there: every quadruple
    (i, j, k, l) with i < j and k < l such that (e_i + e_j)(e_k + s e_l) = 0
    for s = +1 or s = -1 contributes the six index pairs
    (i, j), (k, l), (i, k), (i, l), (j, k), (j, l); an edge is such a pair
    of distinct indices.  The first blade carries the sign +, as in that
    enumeration; [adjacency_all_signs] proves that letting both blades
    take both signs gives the same adjacency.

    Results, each a decision by evaluation ([vm_compute]) on [tz_mul] at
    level 4, independent of the axiom [zd_graph_three_components] of
    C958_ZDGraphTopology.
    - [participation_edge_count]: 84 edges.
    - [participation_adjacency_closed_form]: two indices are adjacent
      exactly when they are distinct, neither is 0 or 8, and their xor is
      not 8; the 7 missing pairs among the 14 remaining indices are
      (i, i xor 8) for i in 1..7.
    - [participation_components]: two indices lie in one connected
      component (the reflexive symmetric transitive closure of the edge
      relation) exactly when [cls] agrees; [cls] has three values, with
      class sizes [14; 1; 1] for the giant component, {0} and {8}.
    The status note of C-946 names the singletons e_0 and e_1; the
    enumeration decides {e_0} and {e_8} (index 8 is the unit of the last
    doubling), and the edges at index 1 are present.

    Scope.  The statements concern the basis-index graph of the 2-blade
    zero products at level 4.  They prove nothing about zero divisors with
    more than two terms or about the levels above 4. *)

From Stdlib Require Import Arith PeanoNat Bool List Relations Lia.
From OpenGororobaVerified Require Import C1468_SlotEmbeddingAllPairs.
Import ListNotations.

Definition blade_t : Type := (nat * nat * bool)%type.

(** Ordered pairs of 2-blades with a zero product, the first blade drawn
    from [firsts]. *)
Definition zero_blade_pairs (firsts : list blade_t) : list (blade_t * blade_t) :=
  filter (fun p => blade_product_zero (fst p) (snd p))
    (list_prod firsts blades16).

Definition participation (p : blade_t * blade_t) : list (nat * nat) :=
  match p with
  | ((i, j, _), (k, l, _)) => [(i, j); (k, l); (i, k); (i, l); (j, k); (j, l)]
  end.

Definition pair_eqb (a b : nat * nat) : bool :=
  (Nat.eqb (fst a) (fst b) && Nat.eqb (snd a) (snd b))%bool.

Definition adjacent_in (es : list (nat * nat)) (p q : nat) : bool :=
  (negb (Nat.eqb p q)
   && existsb (fun e => pair_eqb e (p, q) || pair_eqb e (q, p)) es)%bool.

(** The enumeration of the Rust graph: first blade e_i + e_j. *)
Definition plus_blades : list blade_t :=
  filter (fun b => negb (snd b)) blades16.

Definition edge_pairs (firsts : list blade_t) : list (nat * nat) :=
  flat_map participation (zero_blade_pairs firsts).

Definition edges_plus : list (nat * nat) := edge_pairs plus_blades.
Definition edges_all : list (nat * nat) := edge_pairs blades16.

Definition adj (p q : nat) : bool := adjacent_in edges_plus p q.
Definition adj_all (p q : nat) : bool := adjacent_in edges_all p q.

Definition idx : list nat := seq 0 16.

Definition vertex_pairs : list (nat * nat) :=
  flat_map (fun p => map (fun q => (p, q)) (seq (S p) (15 - p))) (seq 0 15).

(** Class of an index: the three components. *)
Definition cls (p : nat) : nat :=
  if Nat.eqb p 0 then 0 else if Nat.eqb p 8 then 1 else 2.

Definition closed_form (p q : nat) : bool :=
  (negb (Nat.eqb p q)
   && negb (Nat.eqb p 0) && negb (Nat.eqb p 8)
   && negb (Nat.eqb q 0) && negb (Nat.eqb q 8)
   && negb (Nat.eqb (Nat.lxor p q) 8))%bool.

Definition edge_rel (p q : nat) : Prop := p < 16 /\ q < 16 /\ adj p q = true.

Definition connected : nat -> nat -> Prop :=
  clos_refl_sym_trans nat edge_rel.

(** * Decisions. *)

Theorem zero_blade_pairs_counts :
  length (zero_blade_pairs blades16) = 336
  /\ length (zero_blade_pairs plus_blades) = 168.
Proof. split; vm_compute; reflexivity. Qed.

Theorem participation_edge_count :
  length (filter (fun e => adj (fst e) (snd e)) vertex_pairs) = 84.
Proof. vm_compute. reflexivity. Qed.

Theorem adjacency_all_signs :
  forallb (fun p => forallb (fun q => Bool.eqb (adj p q) (adj_all p q)) idx)
    idx = true.
Proof. vm_compute. reflexivity. Qed.

Theorem participation_adjacency_closed_form :
  forallb (fun p => forallb (fun q => Bool.eqb (adj p q) (closed_form p q)) idx)
    idx = true.
Proof. vm_compute. reflexivity. Qed.

Lemma adj_respects_cls :
  forallb (fun p => forallb (fun q =>
    implb (adj p q) (Nat.eqb (cls p) (cls q))) idx) idx = true.
Proof. vm_compute. reflexivity. Qed.

Definition within2 (p q : nat) : bool :=
  (Nat.eqb p q || adj p q
   || existsb (fun z => adj p z && adj z q)%bool idx)%bool.

Lemma giant_within_two_steps :
  forallb (fun p => forallb (fun q =>
    implb (Nat.eqb (cls p) 2 && Nat.eqb (cls q) 2)%bool (within2 p q)) idx)
    idx = true.
Proof. vm_compute. reflexivity. Qed.

Lemma same_class_cases :
  forallb (fun p => forallb (fun q =>
    implb (Nat.eqb (cls p) (cls q))
      (Nat.eqb p q || (Nat.eqb (cls p) 2 && Nat.eqb (cls q) 2))%bool) idx)
    idx = true.
Proof. vm_compute. reflexivity. Qed.

Lemma class_sizes :
  map (fun c => length (filter (fun p => Nat.eqb (cls p) c) idx)) [2; 0; 1]
  = [14; 1; 1]
  /\ length (nodup Nat.eq_dec (map cls idx)) = 3.
Proof. split; vm_compute; reflexivity. Qed.

(** * Connectivity. *)

Lemma forall_idx (P : nat -> bool) :
  forallb P idx = true -> forall p, p < 16 -> P p = true.
Proof.
  intros H p Hp. unfold idx in H. rewrite forallb_forall in H.
  apply H. apply in_seq. lia.
Qed.

Lemma exists_idx (P : nat -> bool) z :
  z < 16 -> P z = true -> existsb P idx = true.
Proof.
  intros Hz HP. apply existsb_exists. exists z. split.
  - unfold idx. apply in_seq. lia.
  - exact HP.
Qed.

Lemma implb_elim a b : implb a b = true -> a = true -> b = true.
Proof. intros H Ha. destruct a; [exact H | discriminate Ha]. Qed.

Lemma connected_cls : forall p q, connected p q -> cls p = cls q.
Proof.
  intros p q H. induction H as [x y Hxy | x | x y _ IH | x y z _ IH1 _ IH2].
  - destruct Hxy as (Hx & Hy & Ha).
    pose proof (forall_idx _ adj_respects_cls x Hx) as H1.
    apply forallb_forall with (x := y) in H1.
    + apply Nat.eqb_eq. exact (implb_elim _ _ H1 Ha).
    + unfold idx. apply in_seq. lia.
  - reflexivity.
  - symmetry. exact IH.
  - etransitivity; eassumption.
Qed.

Lemma cls_connected : forall p q, p < 16 -> q < 16 -> cls p = cls q -> connected p q.
Proof.
  intros p q Hp Hq Hc.
  pose proof (forall_idx _ same_class_cases p Hp) as H1.
  assert (Hq' : In q idx) by (unfold idx; apply in_seq; lia).
  rewrite forallb_forall in H1. specialize (H1 q Hq').
  pose proof (implb_elim _ _ H1 (proj2 (Nat.eqb_eq _ _) Hc)) as H1'.
  clear H1. rename H1' into H1. apply orb_true_iff in H1. destruct H1 as [Heq | Hg].
  - apply Nat.eqb_eq in Heq. subst q. apply rst_refl.
  - apply andb_true_iff in Hg as [Hp2 Hq2].
    pose proof (forall_idx _ giant_within_two_steps p Hp) as H2.
    rewrite forallb_forall in H2. specialize (H2 q Hq').
    specialize (implb_elim _ _ H2 (andb_true_intro (conj Hp2 Hq2))) as H2'.
    clear H2. rename H2' into H2.
    unfold within2 in H2. apply orb_true_iff in H2. destruct H2 as [H2 | H2].
    + apply orb_true_iff in H2. destruct H2 as [H2 | H2].
      * apply Nat.eqb_eq in H2. subst q. apply rst_refl.
      * apply rst_step. repeat split; assumption.
    + apply existsb_exists in H2. destruct H2 as (z & Hz & Hzz).
      unfold idx in Hz. apply in_seq in Hz.
      apply andb_true_iff in Hzz as [Hpz Hzq].
      apply (rst_trans nat edge_rel p z q).
      * apply rst_step. repeat split; try lia. exact Hpz.
      * apply rst_step. repeat split; try lia. exact Hzq.
Qed.

Theorem participation_components :
  (forall p q, p < 16 -> q < 16 -> connected p q <-> cls p = cls q)
  /\ map (fun c => length (filter (fun p => Nat.eqb (cls p) c) idx)) [2; 0; 1]
     = [14; 1; 1]
  /\ length (nodup Nat.eq_dec (map cls idx)) = 3.
Proof.
  split; [|exact class_sizes].
  intros p q Hp Hq. split.
  - apply connected_cls.
  - apply cls_connected; assumption.
Qed.

(** The three claims of C-946 on one graph: 3 components of sizes
    [14; 1; 1], the singletons {0} and {8}, and 84 edges. *)
Theorem C946_sedenion_zd_participation_graph :
  length (filter (fun e => adj (fst e) (snd e)) vertex_pairs) = 84
  /\ (forall p q, p < 16 -> q < 16 -> connected p q <-> cls p = cls q)
  /\ map (fun c => length (filter (fun p => Nat.eqb (cls p) c) idx)) [2; 0; 1]
     = [14; 1; 1]
  /\ length (nodup Nat.eq_dec (map cls idx)) = 3
  /\ (forall q, q < 16 -> adj 0 q = false /\ adj 8 q = false).
Proof.
  split; [exact participation_edge_count|].
  destruct participation_components as (H1 & H2 & H3).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
  intros q Hq. split.
  - assert (Hd : forallb (fun q => negb (adj 0 q)) idx = true)
      by (vm_compute; reflexivity).
    apply negb_true_iff. exact (forall_idx _ Hd q Hq).
  - assert (Hd : forallb (fun q => negb (adj 8 q)) idx = true)
      by (vm_compute; reflexivity).
    apply negb_true_iff. exact (forall_idx _ Hd q Hq).
Qed.
