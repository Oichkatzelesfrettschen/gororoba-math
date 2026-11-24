(** * Box-kite sign census: edge types, switching minimum and the twist.

    Convention.  The product, the term lists and the squared norm
    [bnorm] are those of [BoxKiteTwoBladeCensus]: e_p * e_q =
    sed_sign p q * e_{p XOR q}.  The assessor planes are the 42 planes
    (l, h) with l < 8 < h and l XOR h <> 8 ([zd_planes_are_assessors]).
    The kite of strut constant S (1 <= S <= 7) holds the six assessors
    (l, l XOR X) for 1 <= l <= 7, l <> S, with X = 8 XOR S, in increasing
    order of l.  For assessors p = (l, h) and q = (l', h') the zero set
    is the set of sign pairs (s, t) in {+1, -1}^2 for which the product
    (e_l + s e_h)(e_l' + t e_h') is zero; [rel_of] reads it as 1 (same:
    the zero set is {(+,+), (-,-)}), 2 (opposite: {(+,-), (-,+)}),
    0 (strut: empty) or 3 (anything else).  The 15 pairs of assessors of
    a kite are 12 edges (relation 1 or 2) and 3 struts (relation 0).

    Rows answered (gororoba-quantum docs/evidence/box_kite_census/
    README.md).
    - Line 49 (edge sign totals): [kite_relation_counts] gives, for each
      of the 7 kites, 6 same, 6 opposite, 3 strut and 0 other pairs, so
      12 edges per kite; [kite_totals] gives 42 same-sign and 42
      opposite-sign edges, 21 struts, in all; [kite_planes_are_zd_planes]
      shows the 42 kite assessors are exactly the planes carrying a zero
      product.
    - Line 51 (frustration minimum): [frustration_negative_on_same] and
      [frustration_negative_on_opposite]: over the 64 vertex switchings of
      the octahedron of a kite, the fewest negative edges is 0 when the
      same-sign edges are negative and 4 when the opposite-sign edges are,
      in each of the 7 kites.
    - Line 53 (twist test): [twist_counts] gives 28224 signed basis
      tests, 0 mismatches and 1344 zero products for the claim that
      (e_B sB + e_b sb)(e_D sD + e_d sd) = 0 exactly when
      (e_B sB + e_d sd)(e_D sD - e_b sb) = 0 over B, D in 9..15, b, d in
      1..7, b <> d, B <> D; [twist_swaps_edge_types] shows the twist maps
      each of the 84 edges (b, B)(d, D) to the pair (d, B)(b, D) of
      the opposite sign type, and [twist_sends_struts_to_nonkite_planes]
      sends each of the 21 struts to planes (l, l XOR 8). *)

From Stdlib Require Import Arith PeanoNat Bool List ZArith.
From OpenGororobaVerified Require Import C1467_XORSignCocycle
  BoxKiteTwoBladeCensus.
Import ListNotations.

Open Scope Z_scope.

Definition zset (p q : nat * nat) : bool * bool * bool * bool :=
  let z := fun s t => Z.eqb (bnorm (fst p, snd p, s) (fst q, snd q, t)) 0 in
  (z 1 1, z 1 (-1), z (-1) 1, z (-1) (-1)).

Definition rel_of (p q : nat * nat) : nat :=
  match zset p q with
  | (false, false, false, false) => 0%nat
  | (true, false, false, true) => 1%nat
  | (false, true, true, false) => 2%nat
  | _ => 3%nat
  end.

Definition swap_rel (r : nat) : nat :=
  match r with 1%nat => 2%nat | 2%nat => 1%nat | _ => r end.

Definition p00 : nat * nat := (0%nat, 0%nat).

Definition kite_assessors (s : nat) : list (nat * nat) :=
  map (fun l => (l, Nat.lxor l (Nat.lxor 8 s)))
      (filter (fun l => negb (Nat.eqb l s)) (seq 1 7)).

Definition kite_pairs (s : nat) : list (nat * nat * nat) :=
  let a := kite_assessors s in
  flat_map (fun u => map (fun v =>
               (u, v, rel_of (nth u a p00) (nth v a p00)))
             (seq (S u) (5 - u))) (seq 0 6).

Definition count_rel (r : nat) (l : list (nat * nat * nat)) : nat :=
  length (filter (fun e => Nat.eqb (snd e) r) l).

Definition kites : list nat := seq 1 7.

Theorem kite_relation_counts :
  map (fun s => let l := kite_pairs s in
         (count_rel 1 l, count_rel 2 l, count_rel 0 l, count_rel 3 l)) kites
  = repeat (6%nat, 6%nat, 3%nat, 0%nat) 7.
Proof. vm_compute. reflexivity. Qed.

Definition total_rel (r : nat) : nat :=
  fold_left Nat.add (map (fun s => count_rel r (kite_pairs s)) kites) 0%nat.

Theorem kite_totals :
  (total_rel 1, total_rel 2, total_rel 0, total_rel 3)
  = (42%nat, 42%nat, 21%nat, 0%nat).
Proof. vm_compute. reflexivity. Qed.

Definition kite_planes : list (nat * nat) := flat_map kite_assessors kites.

Theorem kite_planes_are_zd_planes :
  length kite_planes = 42%nat
  /\ forallb (fun p => mem_plane p zd_planes) kite_planes = true
  /\ forallb (fun p => mem_plane p kite_planes) zd_planes = true.
Proof. repeat apply conj; vm_compute; reflexivity. Qed.

(** Minimum over vertex switchings of the number of negative edges, the
    edges of relation [neg] being negative. *)
Definition negative_after (s neg m : nat) : nat :=
  length (filter (fun e =>
    let '(u, v, r) := e in
    xorb (Nat.eqb r neg) (xorb (Nat.testbit m u) (Nat.testbit m v)))
    (filter (fun e => negb (Nat.eqb (snd e) 0)) (kite_pairs s))).

Definition frustration (s neg : nat) : nat :=
  fold_left Nat.min (map (negative_after s neg) (seq 0 64)) 12%nat.

Theorem frustration_negative_on_same :
  map (fun s => frustration s 1) kites = repeat 0%nat 7.
Proof. vm_compute. reflexivity. Qed.

Theorem frustration_negative_on_opposite :
  map (fun s => frustration s 2) kites = repeat 4%nat 7.
Proof. vm_compute. reflexivity. Qed.

(** The twist test. *)
Definition signs : list Z := [1; -1].

Definition lows : list nat := seq 1 7.
Definition highs : list nat := seq 9 7.

Definition twist_cases : list (nat * nat * nat * nat * (Z * Z * Z * Z)) :=
  flat_map (fun b => flat_map (fun bb => flat_map (fun d =>
    flat_map (fun dd =>
      if Nat.eqb b d || Nat.eqb bb dd then []
      else map (fun ss => (b, bb, d, dd, ss))
        (flat_map (fun sb => flat_map (fun sbb => flat_map (fun sd =>
           map (fun sdd => (sb, sbb, sd, sdd)) signs) signs) signs) signs))
      highs) lows) highs) lows.

Definition is_zero_prod (x y : svec) : bool :=
  forallb (fun n => Z.eqb (scoef (smul x y) n) 0) idx16.

Definition twist_lhs (c : nat * nat * nat * nat * (Z * Z * Z * Z)) : bool :=
  let '(b, bb, d, dd, (sb, sbb, sd, sdd)) := c in
  is_zero_prod [(bb, sbb); (b, sb)] [(dd, sdd); (d, sd)].

Definition twist_rhs (c : nat * nat * nat * nat * (Z * Z * Z * Z)) : bool :=
  let '(b, bb, d, dd, (sb, sbb, sd, sdd)) := c in
  is_zero_prod [(bb, sbb); (d, sd)] [(dd, sdd); (b, - sb)].

(** (tests, mismatches, zero products). *)
Definition twist_tally : N * N * N :=
  fold_left (fun h c =>
    let '(t, m, z) := h in
    let l := twist_lhs c in
    (N.succ t, if Bool.eqb l (twist_rhs c) then m else N.succ m,
     if l then N.succ z else z)) twist_cases (0, 0, 0)%N.

Theorem twist_counts : twist_tally = (28224%N, 0%N, 1344%N).
Proof. vm_compute. reflexivity. Qed.

(** The twist on the pairs of a kite. *)
Definition twisted_pair (a1 a2 : nat * nat) : (nat * nat) * (nat * nat) :=
  ((fst a2, snd a1), (fst a1, snd a2)).

Definition kite_twist_ok (check : nat -> nat -> bool) : nat :=
  fold_left Nat.add (map (fun s =>
    let a := kite_assessors s in
    length (filter (fun e => let '(u, v, r) := e in
      check r (rel_of (fst (twisted_pair (nth u a p00) (nth v a p00)))
                      (snd (twisted_pair (nth u a p00) (nth v a p00)))))
      (kite_pairs s))) kites) 0%nat.

Theorem twist_swaps_edge_types :
  kite_twist_ok (fun r r' => Nat.eqb r' (swap_rel r) && negb (Nat.eqb r 0))
  = 84%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem twist_sends_struts_to_nonkite_planes :
  fold_left Nat.add (map (fun s =>
    let a := kite_assessors s in
    length (filter (fun e => let '(u, v, r) := e in
      let '(p', q') := twisted_pair (nth u a p00) (nth v a p00) in
      Nat.eqb r 0
      && Nat.eqb (Nat.lxor (fst p') (snd p')) 8
      && Nat.eqb (Nat.lxor (fst q') (snd q')) 8) (kite_pairs s))) kites) 0%nat
  = 21%nat.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions kite_relation_counts.
Print Assumptions kite_totals.
Print Assumptions kite_planes_are_zd_planes.
Print Assumptions frustration_negative_on_same.
Print Assumptions frustration_negative_on_opposite.
Print Assumptions twist_counts.
Print Assumptions twist_swaps_edge_types.
Print Assumptions twist_sends_struts_to_nonkite_planes.
