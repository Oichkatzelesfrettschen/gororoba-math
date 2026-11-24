(** * C-1467: associative triples among the imaginary octonion basis
    elements (Fano plane lines).

    Convention.  The octonion product is the level-3 product of the
    Cayley-Dickson tower used by the sedenion files: e_p * e_q =
    sign3 p q * e_{p XOR q} for p, q < 8, with [sign3] = [cd_sign_fuel 4 8]
    of [C1467_XORSignCocycle], the recurrence whose level-4 extension is
    [sed_sign].  [sign3_is_sed_sign] shows that [sed_sign] restricted to
    labels below 8 is [sign3], so the sedenion table of the other files
    contains this octonion table.  A triple (i, j, k) is associative in
    the given order when (e_i e_j) e_k = e_i (e_j e_k); both sides are
    +-e_{i XOR j XOR k}, so the test is equality of the two signs
    ([assoc_ordered]).  An unordered triple {i, j, k} is associative when
    all six orderings are ([assoc_all]).

    Row answered: gororoba-open C-1467 (Wilmot, arXiv 2505.06011, Fano
    3-form verification).
    - [oct_triples_count]: 35 unordered triples of distinct imaginary
      units (i < j < k, labels 1 to 7).
    - [assoc_triples_are_fano_lines]: exactly 7 are associative, and they
      are the triples with i XOR j XOR k = 0, the lines of the Fano plane
      (the list is spelled out).
    - [nonassoc_triples_count]: the other 28 are non-associative.
    - [assoc_all_iff_given_order], [nonassoc_in_every_order]: the 28 fail
      to associate in every one of the six orderings, and associativity in
      the order i < j < k is equivalent to associativity in all orders.
    - [fano_lines_cover_edges]: each of the 21 pairs of distinct imaginary
      units lies on exactly one associative triple, so the 7 triples cover
      all 21 edges of the 6-simplex.
    - [fano_lines_close]: each associative triple {i, j, k} satisfies
      i XOR j = k, so {0, i, j, k} is closed under the product index; that
      the span is a subalgebra isomorphic to the quaternions is not stated
      here.
    - [oct_ordered_nonassoc_count]: 168 ordered triples of labels below 8
      fail to associate (the octonion count of the sedenion census).  The
      domain [triples_below 8] holds all 512 ordered triples, repeats and
      label 0 included; those associate in an alternative algebra, so the
      count equals the count over ordered triples of distinct imaginary
      labels. *)

From Stdlib Require Import Arith PeanoNat Bool List ZArith.
From OpenGororobaVerified Require Import C1467_XORSignCocycle
  C1630_BasisAssociatorTensor.
Import ListNotations.

Open Scope Z_scope.

Definition sign3 (p q : nat) : Z := cd_sign_fuel 4 8 p q.

Theorem sign3_is_sed_sign :
  forallb (fun i => forallb (fun j => Z.eqb (sed_sign i j) (sign3 i j))
                            (seq 0 8)) (seq 0 8) = true.
Proof. exact sign_restrict_level3. Qed.

Definition assoc_ordered (i j k : nat) : bool :=
  Z.eqb (sign3 i j * sign3 (Nat.lxor i j) k)
        (sign3 j k * sign3 i (Nat.lxor j k)).

Definition assoc_all (t : nat * nat * nat) : bool :=
  let '(i, j, k) := t in
  assoc_ordered i j k && assoc_ordered i k j && assoc_ordered j i k
  && assoc_ordered j k i && assoc_ordered k i j && assoc_ordered k j i.

Definition assoc_some (t : nat * nat * nat) : bool :=
  let '(i, j, k) := t in
  assoc_ordered i j k || assoc_ordered i k j || assoc_ordered j i k
  || assoc_ordered j k i || assoc_ordered k i j || assoc_ordered k j i.

(** Unordered triples of distinct imaginary units, as i < j < k. *)
Definition oct_triples : list (nat * nat * nat) :=
  flat_map (fun i => flat_map (fun j => map (fun k => (i, j, k))
                                            (seq (S j) (7 - j)))
                              (seq (S i) (7 - i))) (seq 1 7).

Theorem oct_triples_count : length oct_triples = 35%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem assoc_triples_are_fano_lines :
  filter assoc_all oct_triples =
  ([(1,2,3); (1,4,5); (1,6,7); (2,4,6); (2,5,7); (3,4,7); (3,5,6)])%nat
  /\ filter assoc_all oct_triples =
     filter (fun t => let '(i, j, k) := t in
               Nat.eqb (xor3 i j k) 0) oct_triples.
Proof. split; vm_compute; reflexivity. Qed.

Theorem nonassoc_triples_count :
  length (filter (fun t => negb (assoc_all t)) oct_triples) = 28%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem nonassoc_in_every_order :
  forallb (fun t => implb (negb (assoc_all t)) (negb (assoc_some t)))
          oct_triples = true.
Proof. vm_compute. reflexivity. Qed.

Theorem assoc_all_iff_given_order :
  forallb (fun t => let '(i, j, k) := t in
             Bool.eqb (assoc_ordered i j k) (assoc_all t)) oct_triples = true.
Proof. vm_compute. reflexivity. Qed.

Definition on_triple (a b : nat) (t : nat * nat * nat) : bool :=
  let '(i, j, k) := t in
  (Nat.eqb a i || Nat.eqb a j || Nat.eqb a k)
  && (Nat.eqb b i || Nat.eqb b j || Nat.eqb b k).

Theorem fano_lines_cover_edges :
  forallb (fun a => forallb (fun b =>
      implb (Nat.ltb a b)
        (Nat.eqb (length (filter (fun t => assoc_all t && on_triple a b t)
                                 oct_triples)) 1))
    (seq 1 7)) (seq 1 7) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem fano_lines_close :
  forallb (fun t => let '(i, j, k) := t in
             implb (assoc_all t)
               (Nat.eqb (Nat.lxor i j) k && Nat.eqb (Nat.lxor j k) i
                && Nat.eqb (Nat.lxor i k) j))
          oct_triples = true.
Proof. vm_compute. reflexivity. Qed.

Theorem oct_ordered_nonassoc_count :
  cnt (fun t => let '(i, j, k) := t in negb (assoc_ordered i j k))
      (triples_below 8) = 168%N.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions sign3_is_sed_sign.
Print Assumptions oct_triples_count.
Print Assumptions assoc_triples_are_fano_lines.
Print Assumptions nonassoc_triples_count.
Print Assumptions nonassoc_in_every_order.
Print Assumptions assoc_all_iff_given_order.
Print Assumptions fano_lines_cover_edges.
Print Assumptions fano_lines_close.
Print Assumptions oct_ordered_nonassoc_count.
