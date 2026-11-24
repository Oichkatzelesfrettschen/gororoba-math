(** * C-468: the 15 x 15 emanation table of the sedenion algebra.

    Convention.  The product is e_p * e_q = sed_sign p q * e_{p XOR q},
    the table [sed_sign] of [C1467_XORSignCocycle], multiplied through
    the term lists of [BoxKiteTwoBladeCensus] ([smul], [scoef]).  A cell
    of the emanation table is a pair (row, col) of imaginary labels 1 to
    15; its sign is that of the basis product e_row * e_col.  A plane
    (lo, hi) with lo < hi is zero-divisor-bearing ([zero_bearing] of
    [BoxKiteTwoBladeCensus]) when some two-blade e_lo + s e_hi has a
    vanishing product with some two-blade, for a sign s of either value.
    A cell is zero-divisor-marked when its row and column lie on opposite
    sides of 8 (one label below 8, one at 8 or above) and its plane
    (min, max) is zero-divisor-bearing; this is the semantic reading of
    the motif-component membership that the emanation table builder of
    gororoba-open (crates/algebra_experimental/src/emanation/
    table_builder.rs) uses, and the equality of those two readings is
    not stated here.

    Row answered: gororoba-open C-468.
    - [et_cells_count]: 225 cells.
    - [marked_cells_count]: 84 cells are marked, [marked_symmetric]: a
      cell is marked exactly when its transpose is, and
      [marked_iff_not_nonkite]: marked cells are the cells with one label
      below 8, the other above 8 and row XOR col <> 8, so the 84 are the 42 assessor planes with
      both orders ([zd_planes_are_assessors]).
    - [et_diagonal_minus_one]: every diagonal cell has e_i * e_i = -1 at
      label 0 and no other component.
    - [et_product_index_xor]: each cell product has the single component
      sed_sign i j at label i XOR j (this holds by the definition of
      [smul] and records the XOR indexing of the table). *)

From Stdlib Require Import Arith PeanoNat Bool List ZArith.
From OpenGororobaVerified Require Import C1467_XORSignCocycle
  BoxKiteTwoBladeCensus.
Import ListNotations.

Open Scope Z_scope.

Definition et_cells : list (nat * nat) :=
  flat_map (fun i => map (fun j => (i, j)) (seq 1 15)) (seq 1 15).

Definition is_cross (i j : nat) : bool :=
  (Nat.ltb i 8 && Nat.leb 8 j) || (Nat.ltb j 8 && Nat.leb 8 i).

Definition marked (c : nat * nat) : bool :=
  let '(i, j) := c in
  is_cross i j && mem_plane (Nat.min i j, Nat.max i j) zd_planes.

Definition unit_vec (i : nat) : svec := [(i, 1)].

Theorem et_cells_count : length et_cells = 225%nat.
Proof. vm_compute. reflexivity. Qed.

Theorem marked_cells_count : cnt marked et_cells = 84%N.
Proof. vm_compute. reflexivity. Qed.

Theorem marked_symmetric :
  forallb (fun c => Bool.eqb (marked c) (marked (snd c, fst c))) et_cells
  = true.
Proof. vm_compute. reflexivity. Qed.

Theorem marked_iff_not_nonkite :
  forallb (fun c => Bool.eqb (marked c)
             (is_cross (fst c) (snd c)
              && Nat.ltb 8 (Nat.max (fst c) (snd c))
              && negb (Nat.eqb (Nat.lxor (fst c) (snd c)) 8))) et_cells
  = true.
Proof. vm_compute. reflexivity. Qed.

Theorem et_diagonal_minus_one :
  forallb (fun i =>
    forallb (fun n =>
      Z.eqb (scoef (smul (unit_vec i) (unit_vec i)) n)
            (if Nat.eqb n 0 then -1 else 0)) idx16) (seq 1 15) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem et_product_index_xor :
  forallb (fun c =>
    forallb (fun n =>
      Z.eqb (scoef (smul (unit_vec (fst c)) (unit_vec (snd c))) n)
            (if Nat.eqb n (Nat.lxor (fst c) (snd c))
             then sed_sign (fst c) (snd c) else 0)) idx16) et_cells = true.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions et_cells_count.
Print Assumptions marked_cells_count.
Print Assumptions marked_symmetric.
Print Assumptions marked_iff_not_nonkite.
Print Assumptions et_diagonal_minus_one.
Print Assumptions et_product_index_xor.
