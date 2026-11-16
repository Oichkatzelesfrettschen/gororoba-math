(** * C-016: ordered triples of the Fano plane, their parity, and |GL(3,2)|.

    Convention: the points are 1 .. 7, a Fano line is a member of fano_lines of
    FanoPlane.v, and an oriented triple (a, b, c) is an ordered triple of
    distinct points with a xor b xor c = 0.  The parity of an oriented triple
    is the parity of its number of inversions, the pairs of positions whose
    entries are in decreasing order: (a > b) + (a > c) + (b > c).

    The module proves:
    - the ordered triples of distinct points of {1, ..., 7} number
      7 * 6 * 5 = 210, of which 42 are oriented and 168 are not; the 42
      oriented triples are the orderings of the points of the 7 Fano lines,
      6 each;
    - exchanging the first two entries of an oriented triple gives an oriented
      triple of the other parity, and 21 oriented triples have even parity and
      21 odd parity;
    - exactly 168 of the 512 binary 3 x 3 matrices have determinant 1 modulo
      2, the order of GL(3, 2).

    The split of 210 into 42 and 168 is a count of ordered triples; the module
    constructs no bijection between the 168 non-oriented triples and GL(3, 2),
    so the equality of the two numbers is a coincidence of values here.  The
    module defines no totally antisymmetric 3-form m3: the signs of the
    parity count are inversion parities, not values of a form.  The sum
    C(7, 3) + 168 is 203, not 210. *)

From Stdlib Require Import List ZArith Arith PeanoNat Lia Bool.
From OpenGororoba Require Import FanoPlane.
Import ListNotations.

Definition points : list nat := seq 1 7.

Definition distinct_triple (t : nat * nat * nat) : bool :=
  let a := fst (fst t) in let b := snd (fst t) in let c := snd t in
  (negb (Nat.eqb a b) && negb (Nat.eqb a c) && negb (Nat.eqb b c))%bool.

Definition ordered_triples : list (nat * nat * nat) :=
  filter distinct_triple
    (map (fun p => (fst (fst p), snd (fst p), snd p))
         (list_prod (list_prod points points) points)).

Definition is_oriented (t : nat * nat * nat) : bool :=
  Nat.eqb (Nat.lxor (Nat.lxor (fst (fst t)) (snd (fst t))) (snd t)) 0.

Definition oriented_triples : list (nat * nat * nat) :=
  filter is_oriented ordered_triples.

Definition other_triples : list (nat * nat * nat) :=
  filter (fun t => negb (is_oriented t)) ordered_triples.

Theorem ordered_triple_counts :
  length ordered_triples = 210 /\
  length oriented_triples = 42 /\
  length other_triples = 168.
Proof. vm_compute. repeat split. Qed.

Theorem ordered_triples_count_is_falling_factorial :
  length ordered_triples = 7 * 6 * 5.
Proof. vm_compute. reflexivity. Qed.

Definition on_a_line (t : nat * nat * nat) : bool :=
  let a := fst (fst t) in let b := snd (fst t) in let c := snd t in
  existsb (fun l => (existsb (Nat.eqb a) l && existsb (Nat.eqb b) l &&
                     existsb (Nat.eqb c) l)%bool) fano_lines.

Theorem oriented_triples_lie_on_lines :
  forallb on_a_line oriented_triples = true.
Proof. vm_compute. reflexivity. Qed.

(** Every line contributes its six orderings. *)
Theorem every_line_has_six_orientations :
  forallb (fun l =>
    Nat.eqb (length (filter (fun t =>
      (existsb (Nat.eqb (fst (fst t))) l && existsb (Nat.eqb (snd (fst t))) l &&
       existsb (Nat.eqb (snd t)) l)%bool) oriented_triples)) 6)
    fano_lines = true.
Proof. vm_compute. reflexivity. Qed.

Definition inversions (t : nat * nat * nat) : nat :=
  let a := fst (fst t) in let b := snd (fst t) in let c := snd t in
  Nat.b2n (Nat.ltb b a) + Nat.b2n (Nat.ltb c a) + Nat.b2n (Nat.ltb c b).

Definition even_triple (t : nat * nat * nat) : bool :=
  Nat.even (inversions t).

Definition swap_first_two (t : nat * nat * nat) : nat * nat * nat :=
  (snd (fst t), fst (fst t), snd t).

Theorem oriented_swap_flips_parity :
  forallb (fun t =>
    existsb (fun u => Nat.eqb (fst (fst u)) (fst (fst (swap_first_two t))) &&
                      Nat.eqb (snd (fst u)) (snd (fst (swap_first_two t))) &&
                      Nat.eqb (snd u) (snd (swap_first_two t)))
            oriented_triples &&
    negb (Bool.eqb (even_triple t) (even_triple (swap_first_two t))))
    oriented_triples = true.
Proof. vm_compute. reflexivity. Qed.

Theorem oriented_parity_split :
  length (filter even_triple oriented_triples) = 21 /\
  length (filter (fun t => negb (even_triple t)) oriented_triples) = 21.
Proof. vm_compute. split; reflexivity. Qed.

(** * Binary 3 x 3 matrices. *)

Definition bit (n i : nat) : Z := if Nat.testbit n i then 1%Z else 0%Z.

Definition det3_mod2 (n : nat) : Z :=
  let a := bit n 0 in let b := bit n 1 in let c := bit n 2 in
  let d := bit n 3 in let e := bit n 4 in let f := bit n 5 in
  let g := bit n 6 in let h := bit n 7 in let i := bit n 8 in
  Z.modulo (a * (e * i - f * h) - b * (d * i - f * g) + c * (d * h - e * g)) 2.

Theorem gl32_order_by_enumeration :
  length (filter (fun n => Z.eqb (det3_mod2 n) 1) (seq 0 512)) = 168.
Proof. vm_compute. reflexivity. Qed.

(** C(7, 3) + 168 = 35 + 168 = 203 differs from the 210 ordered triples. *)
Theorem ordered_triples_not_binomial_plus_gl32 :
  7 * 6 * 5 / 6 + length other_triples <> length ordered_triples.
Proof. vm_compute. discriminate. Qed.
