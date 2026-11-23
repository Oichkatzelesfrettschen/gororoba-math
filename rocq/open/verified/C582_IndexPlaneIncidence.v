(** * C-582: incidence of the 15 index planes of the sedenions, the
    associator census on them, and the planes that carry zero products.

    Convention.  The algebra is level 4 of the integer Cayley-Dickson tower
    [tz] of [C1468_SlotEmbeddingAllPairs], with the product [tz_mul]:
    (a, b)(c, d) = (a c - conj(d) b, d a + b conj(c)).  e_i is the unit
    vector [tz_basis 4 i] of index [i < 16], and e_i e_j = +- e_(i xor j).
    An index plane is the set [plane u] = {i < 16 | parity(u land i) = 0}
    for [u] in 1..15, eight indices closed under xor, decided by [off_sub]
    of [C029_SedenionOctonionSubalgebras]; it is the index set of
    [in_sub u] there, and that file proves over the
    reals that the span is an octonion subalgebra for [u <= 8] and fails
    left alternativity for [9 <= u].  A line is a triple {a, b, a xor b} of
    nonzero indices, the imaginary units of a quaternion subalgebra.  A
    2-blade is e_i + e_j or e_i - e_j with i < j ([blades16]).

    Decisions and equalities.  Each count below is a count of Boolean
    values of [tz_eqb].  [tz_eqb_iff] proves that [tz_eqb n a b = true]
    exactly when [a = b], so a counted failure is an inequality of integer
    vectors; [associates_at_tower] and [commutes_at_tower] carry the two
    basis decisions to equalities of [tower_mul] over the reals through the
    injective embedding [tz_to_R], and [blade_product_zero_iff] reads a
    zero product as an equality with [tz_zero 4].  [tz_to_R_injective]
    and the two tower theorems rest on the axioms of the Stdlib reals that
    the kernel assumptions of this tree list ([sig_forall_dec],
    [functional_extensionality_dep]); every other lemma and theorem of the
    file is closed under the global context.

    Results, each a decision by evaluation on [tz_mul].
    - [closed_octets_are_planes]: of the 6435 eight-element index sets
      that contain 0, exactly 15 are closed under xor, and they are the
      15 planes, which are pairwise distinct.
    - [plane_line_incidence]: 35 lines; each plane holds 7 lines and each
      line lies in 3 planes; two distinct planes (105 pairs) share 4
      indices and exactly one line; two distinct nonzero indices (105
      pairs) lie on exactly one line.  The index group under xor is
      F_2^4, whose nonzero elements, 2-dimensional and 3-dimensional
      subspaces are the points, lines and planes of PG(3,2).
    - [ordered_nonassociating_counts]: the ordered basis triples with
      (e_a e_b) e_c <> e_a (e_b e_c) number 0 of 64 at level 2, 168 of
      512 at level 3 and 1848 of 4096 at level 4, each in the product of
      its own level.  [CDAssociatorCensus] holds the same three counts on
      the sign exponent of cube coordinates
      ([census_numeric_dimension_sixteen]) and their closed form at every
      level ([associator_census_formula]);
      [nonassociating_matches_cube_census] equates the counts on
      [tz_mul] with those at levels 2, 3 and 4.
      [basis_units_alternate]: (e_a e_a) e_b = e_a (e_a e_b) and
      (e_a e_b) e_b = e_a (e_b e_b) for all 256 pairs of indices, so a
      failure of alternativity in a plane needs an element with two
      terms.  [noncommuting_counts]: 6, 42 and 210 ordered pairs
      of distinct imaginary units do not commute at levels 2, 3 and 4.
    - [sorted_triple_classes]: of the 455 unordered triples of distinct
      nonzero indices, the 35 lines associate in all six orders, 168
      triples fail in exactly two of the six orders and 252 fail in all
      six; a triple a < b < c fails in that order exactly when it fails
      in all six.
    - [plane_triple_counts]: a triple that is no line lies in exactly one
      plane; a plane holds 28 of the 252 triples when [u <= 8] and 4 when
      [9 <= u], so 252 = 8 * 28 + 7 * 4.
    - [zero_products_span_late_planes]: the four indices of each of the
      336 ordered zero products of 2-blades (the count is that of
      [all_blade_zero_products_are_assessor_pairs], used as proved) lie
      in exactly one
      plane, and
      that plane has [9 <= u]; each of those 7 planes carries 48 of them.
    - [late_planes_are_fano_lines]: for [9 <= u] the indices 1..7 of
      [plane u] form a line a, b, a xor b of the octonion index set, the
      remaining four indices are 8 xor i for the four i of 1..7 off that
      line, and the 7 planes give the 7 lines of 1..7.
    - [key_plane_incidence]: both blades of a zero product have the same
      xor key i xor j, one of 9..15; plane [u] carries zero products of key
      [x] exactly when [x] lies in [plane u], and then 12 of them, so each
      plane meets 4 keys and each key 4 planes.  The key is [xor_sig] of
      [ZDGraph], which [all_boxkites_uniform_xor] proves constant on each
      of the seven box-kites.  Membership and xor closure are [nat_mem]
      of [FanoPlane] and [check_closure] of [C1466_SubalgebraClosure].

    Scope.  The statements concern basis units, 2-blades and index sets of
    level 4.  Alternativity of a span over a ring is the subject of C029;
    no statement here concerns zero divisors with more than two terms. *)

From Stdlib Require Import Arith PeanoNat Bool List ZArith Reals.
From OpenGororoba Require Import RecursiveCDTower SchreierSignCode
  CDSignNumericCorrespondence CDTowerSignCorrespondence.
From OpenGororoba Require FanoPlane ZDGraph CDAssociatorCensus.
From OpenGororobaVerified Require Import C1468_SlotEmbeddingAllPairs.
From OpenGororobaVerified Require C029_SedenionOctonionSubalgebras
  C1466_SubalgebraClosure.
Import ListNotations.

(** * Decisions as equalities. *)

Lemma tz_eqb_iff order : forall a b, tz_eqb order a b = true <-> a = b.
Proof.
  induction order as [|order IH]; intros a b.
  - cbn [tz_eqb]. apply Z.eqb_eq.
  - destruct a as [a1 a2], b as [b1 b2]. cbn [tz_eqb fst snd]. split.
    + intros H. apply andb_true_iff in H as [H1 H2].
      apply IH in H1. apply IH in H2. subst. reflexivity.
    + intros H. injection H as H1 H2. apply andb_true_iff.
      split; apply IH; assumption.
Qed.

Lemma tz_to_R_injective order : forall a b,
  tz_to_R order a = tz_to_R order b -> a = b.
Proof.
  induction order as [|order IH]; intros a b H.
  - cbn [tz_to_R] in H. apply eq_IZR. exact H.
  - destruct a as [a1 a2], b as [b1 b2].
    cbn [tz_to_R fst snd] in H. injection H as H1 H2.
    apply IH in H1. apply IH in H2. subst. reflexivity.
Qed.

(** * Index sets. *)

Definition indices : list nat := seq 0 16.
Definition imaginary : list nat := seq 1 15.
Definition late : list nat := seq 9 7.

(** Index [i] lies in the plane of [u]: the index set of [in_sub u]. *)
Definition in_plane (u i : nat) : bool :=
  negb (C029_SedenionOctonionSubalgebras.off_sub u i).

Definition plane (u : nat) : list nat := filter (in_plane u) indices.

Definition planes : list (list nat) := map plane imaginary.

Definition mem : nat -> list nat -> bool := FanoPlane.nat_mem.

Definition subset (s p : list nat) : bool := forallb (fun x => mem x p) s.

Fixpoint nat_list_eqb (a b : list nat) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (Nat.eqb x y && nat_list_eqb a' b')%bool
  | _, _ => false
  end.

(** The sublists of [l] with [k] elements, in the order of [l]. *)
Fixpoint choose (k : nat) (l : list nat) {struct l} : list (list nat) :=
  match l with
  | [] => match k with O => [[]] | S _ => [] end
  | x :: t =>
      match k with
      | O => [[]]
      | S k' => map (cons x) (choose k' t) ++ choose k t
      end
  end.

Definition xor_closed : list nat -> bool :=
  C1466_SubalgebraClosure.check_closure.

Definition octets : list (list nat) := map (cons 0) (choose 7 imaginary).

Theorem closed_octets_are_planes :
  N.of_nat (length octets) = 6435%N
  /\ length (filter xor_closed octets) = 15
  /\ forallb (fun s => existsb (nat_list_eqb s) planes)
       (filter xor_closed octets) = true
  /\ forallb xor_closed planes = true
  /\ forallb (fun p => Nat.eqb (length (filter (nat_list_eqb p) planes)) 1)
       planes = true.
Proof. repeat apply conj; vm_compute; reflexivity. Qed.

(** * Lines and planes. *)

Definition is_line (t : list nat) : bool :=
  match t with
  | [a; b; c] => Nat.eqb (Nat.lxor a b) c
  | _ => false
  end.

Definition sorted_triples : list (list nat) := choose 3 imaginary.

Definition lines : list (list nat) := filter is_line sorted_triples.

Definition common (a b : list nat) : list nat := filter (fun x => mem x b) a.

Theorem plane_line_incidence :
  length lines = 35
  /\ forallb (fun u =>
       Nat.eqb (length (filter (fun l => subset l (plane u)) lines)) 7)
       imaginary = true
  /\ forallb (fun l =>
       Nat.eqb (length (filter (fun u => subset l (plane u)) imaginary)) 3)
       lines = true
  /\ length (choose 2 imaginary) = 105
  /\ forallb (fun p =>
       match p with
       | [u; v] =>
           (Nat.eqb (length (common (plane u) (plane v))) 4
            && Nat.eqb (length (filter (fun l =>
                 subset l (plane u) && subset l (plane v)) lines)) 1)%bool
       | _ => false
       end) (choose 2 imaginary) = true
  /\ forallb (fun p =>
       match p with
       | [a; b] =>
           Nat.eqb (length (filter (fun l => (mem a l && mem b l)%bool) lines)) 1
       | _ => false
       end) (choose 2 imaginary) = true.
Proof. repeat apply conj; vm_compute; reflexivity. Qed.

(** * Associator and commutator census on basis units. *)

Definition associates_at (n a b c : nat) : bool :=
  tz_eqb n
    (tz_mul n (tz_mul n (tz_basis n a) (tz_basis n b)) (tz_basis n c))
    (tz_mul n (tz_basis n a) (tz_mul n (tz_basis n b) (tz_basis n c))).

Definition commutes_at (n a b : nat) : bool :=
  tz_eqb n (tz_mul n (tz_basis n a) (tz_basis n b))
    (tz_mul n (tz_basis n b) (tz_basis n a)).

Definition tower_unit (n i : nat) : cd_tower n :=
  tower_basis n (cube_decode n i).

Theorem associates_at_tower n a b c :
  associates_at n a b c = true <->
  tower_mul n (tower_mul n (tower_unit n a) (tower_unit n b)) (tower_unit n c)
  = tower_mul n (tower_unit n a) (tower_mul n (tower_unit n b) (tower_unit n c)).
Proof.
  unfold associates_at, tower_unit. split.
  - intros H. apply tz_eqb_iff in H.
    rewrite <- !tz_basis_tower, <- !tz_to_R_mul, H. reflexivity.
  - intros H. apply tz_eqb_iff, tz_to_R_injective.
    rewrite !tz_to_R_mul, !tz_basis_tower. exact H.
Qed.

Theorem commutes_at_tower n a b :
  commutes_at n a b = true <->
  tower_mul n (tower_unit n a) (tower_unit n b)
  = tower_mul n (tower_unit n b) (tower_unit n a).
Proof.
  unfold commutes_at, tower_unit. split.
  - intros H. apply tz_eqb_iff in H.
    rewrite <- !tz_basis_tower, <- !tz_to_R_mul, H. reflexivity.
  - intros H. apply tz_eqb_iff, tz_to_R_injective.
    rewrite !tz_to_R_mul, !tz_basis_tower. exact H.
Qed.

Definition ordered_triples (l : list nat) : list (nat * nat * nat) :=
  flat_map (fun a => flat_map (fun b => map (fun c => (a, b, c)) l) l) l.

Definition fails_at (n : nat) (t : nat * nat * nat) : bool :=
  match t with (a, b, c) => negb (associates_at n a b c) end.

Definition fails : nat * nat * nat -> bool := fails_at 4.

(** The count over the basis triples of level [n], in the product of
    level [n]. *)
Definition nonassociating (n : nat) : nat :=
  length (filter (fails_at n) (ordered_triples (seq 0 (Nat.pow 2 n)))).

Theorem ordered_nonassociating_counts :
  nonassociating 2 = 0
  /\ nonassociating 3 = 168
  /\ nonassociating 4 = 1848.
Proof. repeat apply conj; vm_compute; reflexivity. Qed.

(** The counts equal those of [CDAssociatorCensus] on the sign exponent
    of cube coordinates, level by level. *)
Theorem nonassociating_matches_cube_census :
  Z.of_nat (nonassociating 2)
  = CDAssociatorCensus.numeric_associator_defect_count 2
  /\ Z.of_nat (nonassociating 3)
     = CDAssociatorCensus.numeric_associator_defect_count 3
  /\ Z.of_nat (nonassociating 4)
     = CDAssociatorCensus.numeric_associator_defect_count 4.
Proof. repeat apply conj; vm_compute; reflexivity. Qed.

Theorem basis_units_alternate :
  forallb (fun a => forallb (fun b =>
    (associates_at 4 a a b && associates_at 4 a b b)%bool) indices) indices
  = true.
Proof. vm_compute. reflexivity. Qed.

Definition noncommuting (n : nat) : nat :=
  length (filter (fun p =>
    (negb (Nat.eqb (fst p) (snd p))
     && negb (commutes_at n (fst p) (snd p)))%bool)
    (list_prod (seq 1 (Nat.pow 2 n - 1)) (seq 1 (Nat.pow 2 n - 1)))).

Theorem noncommuting_counts :
  noncommuting 2 = 6
  /\ noncommuting 3 = 42
  /\ noncommuting 4 = 210.
Proof. repeat apply conj; vm_compute; reflexivity. Qed.

(** The number of the six orders of a triple in which it fails to
    associate. *)
Definition failing_orders (t : list nat) : nat :=
  match t with
  | [a; b; c] =>
      length (filter fails
        [(a, b, c); (a, c, b); (b, a, c); (b, c, a); (c, a, b); (c, b, a)])
  | _ => 0
  end.

Definition fails_sorted (t : list nat) : bool :=
  match t with
  | [a; b; c] => fails (a, b, c)
  | _ => false
  end.

Definition class (n : nat) : list (list nat) :=
  filter (fun t => Nat.eqb (failing_orders t) n) sorted_triples.

Theorem sorted_triple_classes :
  length sorted_triples = 455
  /\ length (class 0) = 35
  /\ length (class 2) = 168
  /\ length (class 6) = 252
  /\ forallb (fun t => Bool.eqb (is_line t) (Nat.eqb (failing_orders t) 0))
       sorted_triples = true
  /\ forallb (fun t => Bool.eqb (fails_sorted t) (Nat.eqb (failing_orders t) 6))
       sorted_triples = true.
Proof. repeat apply conj; vm_compute; reflexivity. Qed.

Theorem plane_triple_counts :
  forallb (fun t => implb (negb (is_line t))
    (Nat.eqb (length (filter (fun u => subset t (plane u)) imaginary)) 1))
    sorted_triples = true
  /\ forallb (fun u =>
       Nat.eqb (length (filter (fun t => subset t (plane u)) (class 6)))
         (if Nat.leb u 8 then 28 else 4)) imaginary = true.
Proof. repeat apply conj; vm_compute; reflexivity. Qed.

(** * Zero products of 2-blades and the planes that carry them. *)

Definition blade_pair : Type := ((nat * nat * bool) * (nat * nat * bool))%type.

Definition zero_pairs : list blade_pair :=
  filter (fun p => blade_product_zero (fst p) (snd p))
    (list_prod blades16 blades16).

Lemma blade_product_zero_iff (a b : nat * nat * bool) :
  blade_product_zero a b = true <->
  match a, b with
  | (i, j, s), (k, l, t) =>
      tz_mul 4 (blade 4 i j s) (blade 4 k l t) = tz_zero 4
  end.
Proof.
  destruct a as [[i j] s], b as [[k l] t]. unfold blade_product_zero.
  apply tz_eqb_iff.
Qed.

Definition support (p : blade_pair) : list nat :=
  match p with ((i, j, _), (k, l, _)) => [i; j; k; l] end.

Definition carriers (p : blade_pair) : list nat :=
  filter (fun u => subset (support p) (plane u)) imaginary.

Definition carried_by (u : nat) (p : blade_pair) : bool :=
  match carriers p with
  | [v] => Nat.eqb u v
  | _ => false
  end.

Theorem zero_products_span_late_planes :
  length zero_pairs = 336
  /\ forallb (fun p =>
       match carriers p with
       | [u] => Nat.leb 9 u
       | _ => false
       end) zero_pairs = true
  /\ forallb (fun u =>
       Nat.eqb (length (filter (carried_by u) zero_pairs)) 48) late = true.
Proof.
  split.
  - unfold zero_pairs.
    exact (proj1 all_blade_zero_products_are_assessor_pairs).
  - repeat apply conj; vm_compute; reflexivity.
Qed.

Definition low_part (u : nat) : list nat :=
  filter (fun i => (Nat.leb 1 i && Nat.leb i 7)%bool) (plane u).

Theorem late_planes_are_fano_lines :
  forallb (fun u =>
    (is_line (low_part u)
     && nat_list_eqb (plane u)
          (0 :: low_part u
             ++ map (Nat.lxor 8)
                  (filter (fun i => negb (mem i (low_part u))) (seq 1 7))))%bool)
    late = true
  /\ length (filter is_line (choose 3 (seq 1 7))) = 7
  /\ forallb (fun l => existsb (nat_list_eqb l) (map low_part late))
       (filter is_line (choose 3 (seq 1 7))) = true.
Proof. repeat apply conj; vm_compute; reflexivity. Qed.

Definition key (b : nat * nat * bool) : nat := ZDGraph.xor_sig (fst b).

Theorem key_plane_incidence :
  forallb (fun p =>
    (Nat.eqb (key (fst p)) (key (snd p))
     && Nat.leb 9 (key (fst p)) && Nat.leb (key (fst p)) 15)%bool)
    zero_pairs = true
  /\ forallb (fun u => forallb (fun x =>
       Nat.eqb
         (length (filter (fun p =>
            (carried_by u p && Nat.eqb (key (fst p)) x)%bool) zero_pairs))
         (if in_plane u x then 12 else 0)) late) late = true
  /\ forallb (fun u =>
       Nat.eqb (length (filter (in_plane u) late)) 4) late = true
  /\ forallb (fun x =>
       Nat.eqb (length (filter (fun u => in_plane u x) late)) 4) late = true.
Proof. repeat apply conj; vm_compute; reflexivity. Qed.
