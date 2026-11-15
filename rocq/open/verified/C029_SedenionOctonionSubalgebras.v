(** * C029: the octonion subalgebras of the sedenions spanned by basis units.

    Convention. The product is [sed_mul] and the octonion product is
    [oct_mul] of [theories/Sedenion.v], both Cayley-Dickson doublings
    [(a,b)(c,d) = (ac - conj(d) b, d a + b conj(c))] over the Hamilton
    product [quat_mul]. A sedenion has 16 real coordinates indexed
    [0..15]: index [k < 8] is the coordinate [oct_coord (sed_lo s) k] and
    index [8 + k] is [oct_coord (sed_hi s) k], where octonion index
    [k < 4] is the quaternion coordinate [qa, qb, qc, qd] of [oct_lo]
    and [k >= 4] that of [oct_hi]. [sed_e i] is the unit at index [i].
    The product of two units is a signed unit at the xor of the indices;
    the signs enter only through the tables [tab1 .. tab15] below, and the
    lemmas that use them are checked on all real coordinates.

    The family. For [u] in [1..15] the set [{k < 16 | parity(u land k) = 0}]
    is a 3-dimensional subspace of F_2^4 containing 0, so it holds 8
    indices; all 15 such subspaces arise from the 15 nonzero [u]. [in_sub u]
    is the real span of the 8 units with those indices. Over the reals the
    set of all subalgebras isomorphic to the octonions is infinite; the
    count here is of the 15 coordinate-defined members.

    Results.
    - Each [in_sub u] is closed under [sed_mul] (all 15).
    - For [u <= 8] an explicit linear injective product-preserving map
      [emb (tabs u) : CDOct -> CDSed] has image exactly [in_sub u]; so 8
      members are isomorphic to the octonions.
    - For [9 <= u <= 15] a pair of members [x], [y] of [in_sub u] violates
      left alternativity [(x x) y = x (x y)], which holds in the octonions
      ([oct_left_alt_gen]); no product-preserving map from CDOct has image
      containing [in_sub u], so these 7 are not isomorphic to the octonions.
    - Hence exactly 8 of the 15 members are octonion subalgebras, and the
      15 members are pairwise distinct subspaces.
    - The high half, the diagonal, and an index set not closed under xor
      are not subalgebras. *)

From Stdlib Require Import List Lia.
From OpenGororoba Require Import Prelude CayleyDicksonAlgebra Sedenion OctonionNorm.
From OpenGororoba Require Import C1542_MorHaStabilityArb.
Open Scope R_scope.

(** * Coordinates. *)

Definition oct_coord (x : CDOct) (k : nat) : R :=
  match k with
  | 0%nat => qa (oct_lo x) | 1%nat => qb (oct_lo x)
  | 2%nat => qc (oct_lo x) | 3%nat => qd (oct_lo x)
  | 4%nat => qa (oct_hi x) | 5%nat => qb (oct_hi x)
  | 6%nat => qc (oct_hi x) | 7%nat => qd (oct_hi x)
  | _ => 0
  end.

Definition sed_coord (s : CDSed) (k : nat) : R :=
  match k with
  | 0%nat => oct_coord (sed_lo s) 0 | 1%nat => oct_coord (sed_lo s) 1
  | 2%nat => oct_coord (sed_lo s) 2 | 3%nat => oct_coord (sed_lo s) 3
  | 4%nat => oct_coord (sed_lo s) 4 | 5%nat => oct_coord (sed_lo s) 5
  | 6%nat => oct_coord (sed_lo s) 6 | 7%nat => oct_coord (sed_lo s) 7
  | 8%nat => oct_coord (sed_hi s) 0 | 9%nat => oct_coord (sed_hi s) 1
  | 10%nat => oct_coord (sed_hi s) 2 | 11%nat => oct_coord (sed_hi s) 3
  | 12%nat => oct_coord (sed_hi s) 4 | 13%nat => oct_coord (sed_hi s) 5
  | 14%nat => oct_coord (sed_hi s) 6 | 15%nat => oct_coord (sed_hi s) 7
  | _ => 0
  end.

Definition mk8 (c : nat -> R) : CDOct :=
  mkOct (mkQuat (c 0%nat) (c 1%nat) (c 2%nat) (c 3%nat))
        (mkQuat (c 4%nat) (c 5%nat) (c 6%nat) (c 7%nat)).

Definition mk16 (c : nat -> R) : CDSed :=
  mkSed (mk8 c) (mk8 (fun k => c (8 + k)%nat)).

(** * The family of 15 coordinate subspaces. *)

(** Parity of the number of one bits among bits 0..3 of [n]. *)
Definition par4 (n : nat) : bool :=
  Nat.odd (n mod 2 + (n / 2) mod 2 + (n / 4) mod 2 + (n / 8) mod 2).

(** [off_sub u k = true] when index [k] lies outside the subspace [u]. *)
Definition off_sub (u k : nat) : bool := par4 (Nat.land u k).

(** The real span of the units whose index lies in the subspace [u]. *)
Definition in_sub (u : nat) (s : CDSed) : Prop :=
  forall k, off_sub u k = true -> sed_coord s k = 0.

Lemma in_sub_intro : forall u s,
  (forall k, (k < 16)%nat -> off_sub u k = true -> sed_coord s k = 0) ->
  in_sub u s.
Proof.
  intros u s H k Hk.
  destruct (Nat.lt_ge_cases k 16) as [Hlt | Hge]; [exact (H k Hlt Hk) |].
  do 16 (destruct k as [|k]; [lia |]).
  reflexivity.
Qed.

(** * Embeddings from a table of signed target indices. *)

(** [tab k = (p, s)] sends octonion unit [k] to [s * sed_e p], [s = +-1]. *)
Definition emb_term (tab : nat -> nat * R) (x : CDOct) (m k : nat) : R :=
  if Nat.eqb (fst (tab k)) m then snd (tab k) * oct_coord x k else 0.

Definition emb (tab : nat -> nat * R) (x : CDOct) : CDSed :=
  mk16 (fun m =>
    emb_term tab x m 0%nat + emb_term tab x m 1%nat
    + emb_term tab x m 2%nat + emb_term tab x m 3%nat
    + emb_term tab x m 4%nat + emb_term tab x m 5%nat
    + emb_term tab x m 6%nat + emb_term tab x m 7%nat).

(** The left inverse of [emb] on the span of the image units. *)
Definition proj (tab : nat -> nat * R) (s : CDSed) : CDOct :=
  mk8 (fun k => snd (tab k) * sed_coord s (fst (tab k))).

Ltac unf tab :=
  cbv [emb proj mk8 mk16 emb_term oct_coord sed_coord tab fst snd Nat.eqb Nat.add oct_e oct_zero quat_zero quat_one
       oct_mul oct_conj sed_mul sed_lo sed_hi oct_lo oct_hi
       oct_add oct_scale sed_add sed_scale quat_scale
       quat_mul quat_add quat_neg quat_conj qa qb qc qd].

Ltac dx x :=
  destruct x as [[x0 x1 x2 x3] [x4 x5 x6 x7]].

Ltac dy y :=
  destruct y as [[y0 y1 y2 y3] [y4 y5 y6 y7]].

Ltac proj_emb_tac tab :=
  intros x; dx x; unf tab; f_equal; f_equal; ring.

Ltac emb_in_sub_tac tab :=
  intros x; apply in_sub_intro; intros k Hlt Hk; dx x;
  do 16 (destruct k as [|k];
         [ first [ (cbv in Hk; discriminate Hk) | (unf tab; ring) ] | ]);
  exfalso; lia.

Ltac zc Hs k :=
  try (let h := fresh "z" in pose proof (Hs k eq_refl) as h).

Ltac emb_proj_tac u tab :=
  intros s Hs;
  zc Hs 0%nat; zc Hs 1%nat; zc Hs 2%nat; zc Hs 3%nat;
  zc Hs 4%nat; zc Hs 5%nat; zc Hs 6%nat; zc Hs 7%nat;
  zc Hs 8%nat; zc Hs 9%nat; zc Hs 10%nat; zc Hs 11%nat;
  zc Hs 12%nat; zc Hs 13%nat; zc Hs 14%nat; zc Hs 15%nat;
  destruct s as [[[a0 a1 a2 a3] [a4 a5 a6 a7]] [[b0 b1 b2 b3] [b4 b5 b6 b7]]];
  clear Hs; unf tab; unfold sed_coord, oct_coord in *; simpl in *;
  f_equal; f_equal; f_equal; lra.

Ltac emb_mul_tac tab :=
  intros x y; dx x; dy y; unf tab;
  f_equal; f_equal; f_equal; abstract ring.

Ltac emb_lin_tac tab :=
  intros; (let x := fresh "x" in match goal with
    | |- context [oct_add ?a ?b] => destruct a as [[x0 x1 x2 x3] [x4 x5 x6 x7]];
         destruct b as [[y0 y1 y2 y3] [y4 y5 y6 y7]]
    | |- context [oct_scale ?r ?a] => destruct a as [[x0 x1 x2 x3] [x4 x5 x6 x7]]
    end); unf tab; f_equal; f_equal; f_equal; ring.

Ltac mul_closed_tac tab :=
  intros x y; exists (proj tab (sed_mul (emb tab x) (emb tab y)));
  dx x; dy y; unf tab; f_equal; f_equal; f_equal; abstract ring.

Definition tab1 (k : nat) : nat * R :=
  match k with
  | 0 => (0%nat, 1)
  | 1 => (2%nat, 1)
  | 2 => (4%nat, 1)
  | 3 => (6%nat, 1)
  | 4 => (8%nat, 1)
  | 5 => (10%nat, 1)
  | 6 => (12%nat, 1)
  | 7 => (14%nat, 1)
  | _ => (16%nat, 0)
  end.

Definition tab2 (k : nat) : nat * R :=
  match k with
  | 0 => (0%nat, 1)
  | 1 => (1%nat, 1)
  | 2 => (4%nat, 1)
  | 3 => (5%nat, 1)
  | 4 => (8%nat, 1)
  | 5 => (9%nat, 1)
  | 6 => (12%nat, 1)
  | 7 => (13%nat, 1)
  | _ => (16%nat, 0)
  end.

Definition tab3 (k : nat) : nat * R :=
  match k with
  | 0 => (0%nat, 1)
  | 1 => (3%nat, 1)
  | 2 => (4%nat, 1)
  | 3 => (7%nat, 1)
  | 4 => (8%nat, 1)
  | 5 => (11%nat, 1)
  | 6 => (12%nat, 1)
  | 7 => (15%nat, 1)
  | _ => (16%nat, 0)
  end.

Definition tab4 (k : nat) : nat * R :=
  match k with
  | 0 => (0%nat, 1)
  | 1 => (1%nat, 1)
  | 2 => (2%nat, 1)
  | 3 => (3%nat, 1)
  | 4 => (8%nat, 1)
  | 5 => (9%nat, 1)
  | 6 => (10%nat, 1)
  | 7 => (11%nat, 1)
  | _ => (16%nat, 0)
  end.

Definition tab5 (k : nat) : nat * R :=
  match k with
  | 0 => (0%nat, 1)
  | 1 => (2%nat, 1)
  | 2 => (5%nat, 1)
  | 3 => (7%nat, 1)
  | 4 => (8%nat, 1)
  | 5 => (10%nat, 1)
  | 6 => (13%nat, 1)
  | 7 => (15%nat, 1)
  | _ => (16%nat, 0)
  end.

Definition tab6 (k : nat) : nat * R :=
  match k with
  | 0 => (0%nat, 1)
  | 1 => (1%nat, 1)
  | 2 => (7%nat, 1)
  | 3 => (6%nat, 1)
  | 4 => (8%nat, 1)
  | 5 => (9%nat, 1)
  | 6 => (15%nat, 1)
  | 7 => (14%nat, 1)
  | _ => (16%nat, 0)
  end.

Definition tab7 (k : nat) : nat * R :=
  match k with
  | 0 => (0%nat, 1)
  | 1 => (3%nat, 1)
  | 2 => (6%nat, 1)
  | 3 => (5%nat, 1)
  | 4 => (8%nat, 1)
  | 5 => (11%nat, 1)
  | 6 => (14%nat, 1)
  | 7 => (13%nat, 1)
  | _ => (16%nat, 0)
  end.

Definition tab8 (k : nat) : nat * R :=
  match k with
  | 0 => (0%nat, 1)
  | 1 => (1%nat, 1)
  | 2 => (2%nat, 1)
  | 3 => (3%nat, 1)
  | 4 => (4%nat, 1)
  | 5 => (5%nat, 1)
  | 6 => (6%nat, 1)
  | 7 => (7%nat, 1)
  | _ => (16%nat, 0)
  end.

Definition tab9 (k : nat) : nat * R :=
  match k with
  | 0 => (0%nat, 1)
  | 1 => (2%nat, 1)
  | 2 => (4%nat, 1)
  | 3 => (6%nat, 1)
  | 4 => (9%nat, 1)
  | 5 => (11%nat, 1)
  | 6 => (13%nat, 1)
  | 7 => (15%nat, 1)
  | _ => (16%nat, 0)
  end.

Definition tab10 (k : nat) : nat * R :=
  match k with
  | 0 => (0%nat, 1)
  | 1 => (1%nat, 1)
  | 2 => (4%nat, 1)
  | 3 => (5%nat, 1)
  | 4 => (10%nat, 1)
  | 5 => (11%nat, 1)
  | 6 => (14%nat, 1)
  | 7 => (15%nat, 1)
  | _ => (16%nat, 0)
  end.

Definition tab11 (k : nat) : nat * R :=
  match k with
  | 0 => (0%nat, 1)
  | 1 => (3%nat, 1)
  | 2 => (4%nat, 1)
  | 3 => (7%nat, 1)
  | 4 => (9%nat, 1)
  | 5 => (10%nat, 1)
  | 6 => (13%nat, 1)
  | 7 => (14%nat, 1)
  | _ => (16%nat, 0)
  end.

Definition tab12 (k : nat) : nat * R :=
  match k with
  | 0 => (0%nat, 1)
  | 1 => (1%nat, 1)
  | 2 => (2%nat, 1)
  | 3 => (3%nat, 1)
  | 4 => (12%nat, 1)
  | 5 => (13%nat, 1)
  | 6 => (14%nat, 1)
  | 7 => (15%nat, 1)
  | _ => (16%nat, 0)
  end.

Definition tab13 (k : nat) : nat * R :=
  match k with
  | 0 => (0%nat, 1)
  | 1 => (2%nat, 1)
  | 2 => (5%nat, 1)
  | 3 => (7%nat, 1)
  | 4 => (9%nat, 1)
  | 5 => (11%nat, 1)
  | 6 => (12%nat, 1)
  | 7 => (14%nat, 1)
  | _ => (16%nat, 0)
  end.

Definition tab14 (k : nat) : nat * R :=
  match k with
  | 0 => (0%nat, 1)
  | 1 => (1%nat, 1)
  | 2 => (6%nat, 1)
  | 3 => (7%nat, 1)
  | 4 => (10%nat, 1)
  | 5 => (11%nat, 1)
  | 6 => (12%nat, 1)
  | 7 => (13%nat, 1)
  | _ => (16%nat, 0)
  end.

Definition tab15 (k : nat) : nat * R :=
  match k with
  | 0 => (0%nat, 1)
  | 1 => (3%nat, 1)
  | 2 => (5%nat, 1)
  | 3 => (6%nat, 1)
  | 4 => (9%nat, 1)
  | 5 => (10%nat, 1)
  | 6 => (12%nat, 1)
  | 7 => (15%nat, 1)
  | _ => (16%nat, 0)
  end.

(** * Per-subspace facts. *)

(** ** Subspace 1: index set {0, 2, 4, 6, 8, 10, 12, 14}. *)

Lemma proj_emb_1 : forall x, proj tab1 (emb tab1 x) = x.
Proof. proj_emb_tac tab1. Qed.

Lemma emb_in_sub_1 : forall x, in_sub 1 (emb tab1 x).
Proof. emb_in_sub_tac tab1. Qed.

Lemma emb_proj_1 : forall s, in_sub 1 s -> emb tab1 (proj tab1 s) = s.
Proof. emb_proj_tac 1 tab1. Qed.

Lemma emb_mul_1 : forall x y,
  sed_mul (emb tab1 x) (emb tab1 y) = emb tab1 (oct_mul x y).
Proof. emb_mul_tac tab1. Qed.

Lemma emb_add_1 : forall x y,
  emb tab1 (oct_add x y) = sed_add (emb tab1 x) (emb tab1 y).
Proof. emb_lin_tac tab1. Qed.

Lemma emb_scale_1 : forall r x,
  emb tab1 (oct_scale r x) = sed_scale r (emb tab1 x).
Proof. emb_lin_tac tab1. Qed.

(** ** Subspace 2: index set {0, 1, 4, 5, 8, 9, 12, 13}. *)

Lemma proj_emb_2 : forall x, proj tab2 (emb tab2 x) = x.
Proof. proj_emb_tac tab2. Qed.

Lemma emb_in_sub_2 : forall x, in_sub 2 (emb tab2 x).
Proof. emb_in_sub_tac tab2. Qed.

Lemma emb_proj_2 : forall s, in_sub 2 s -> emb tab2 (proj tab2 s) = s.
Proof. emb_proj_tac 2 tab2. Qed.

Lemma emb_mul_2 : forall x y,
  sed_mul (emb tab2 x) (emb tab2 y) = emb tab2 (oct_mul x y).
Proof. emb_mul_tac tab2. Qed.

Lemma emb_add_2 : forall x y,
  emb tab2 (oct_add x y) = sed_add (emb tab2 x) (emb tab2 y).
Proof. emb_lin_tac tab2. Qed.

Lemma emb_scale_2 : forall r x,
  emb tab2 (oct_scale r x) = sed_scale r (emb tab2 x).
Proof. emb_lin_tac tab2. Qed.

(** ** Subspace 3: index set {0, 3, 4, 7, 8, 11, 12, 15}. *)

Lemma proj_emb_3 : forall x, proj tab3 (emb tab3 x) = x.
Proof. proj_emb_tac tab3. Qed.

Lemma emb_in_sub_3 : forall x, in_sub 3 (emb tab3 x).
Proof. emb_in_sub_tac tab3. Qed.

Lemma emb_proj_3 : forall s, in_sub 3 s -> emb tab3 (proj tab3 s) = s.
Proof. emb_proj_tac 3 tab3. Qed.

Lemma emb_mul_3 : forall x y,
  sed_mul (emb tab3 x) (emb tab3 y) = emb tab3 (oct_mul x y).
Proof. emb_mul_tac tab3. Qed.

Lemma emb_add_3 : forall x y,
  emb tab3 (oct_add x y) = sed_add (emb tab3 x) (emb tab3 y).
Proof. emb_lin_tac tab3. Qed.

Lemma emb_scale_3 : forall r x,
  emb tab3 (oct_scale r x) = sed_scale r (emb tab3 x).
Proof. emb_lin_tac tab3. Qed.

(** ** Subspace 4: index set {0, 1, 2, 3, 8, 9, 10, 11}. *)

Lemma proj_emb_4 : forall x, proj tab4 (emb tab4 x) = x.
Proof. proj_emb_tac tab4. Qed.

Lemma emb_in_sub_4 : forall x, in_sub 4 (emb tab4 x).
Proof. emb_in_sub_tac tab4. Qed.

Lemma emb_proj_4 : forall s, in_sub 4 s -> emb tab4 (proj tab4 s) = s.
Proof. emb_proj_tac 4 tab4. Qed.

Lemma emb_mul_4 : forall x y,
  sed_mul (emb tab4 x) (emb tab4 y) = emb tab4 (oct_mul x y).
Proof. emb_mul_tac tab4. Qed.

Lemma emb_add_4 : forall x y,
  emb tab4 (oct_add x y) = sed_add (emb tab4 x) (emb tab4 y).
Proof. emb_lin_tac tab4. Qed.

Lemma emb_scale_4 : forall r x,
  emb tab4 (oct_scale r x) = sed_scale r (emb tab4 x).
Proof. emb_lin_tac tab4. Qed.

(** ** Subspace 5: index set {0, 2, 5, 7, 8, 10, 13, 15}. *)

Lemma proj_emb_5 : forall x, proj tab5 (emb tab5 x) = x.
Proof. proj_emb_tac tab5. Qed.

Lemma emb_in_sub_5 : forall x, in_sub 5 (emb tab5 x).
Proof. emb_in_sub_tac tab5. Qed.

Lemma emb_proj_5 : forall s, in_sub 5 s -> emb tab5 (proj tab5 s) = s.
Proof. emb_proj_tac 5 tab5. Qed.

Lemma emb_mul_5 : forall x y,
  sed_mul (emb tab5 x) (emb tab5 y) = emb tab5 (oct_mul x y).
Proof. emb_mul_tac tab5. Qed.

Lemma emb_add_5 : forall x y,
  emb tab5 (oct_add x y) = sed_add (emb tab5 x) (emb tab5 y).
Proof. emb_lin_tac tab5. Qed.

Lemma emb_scale_5 : forall r x,
  emb tab5 (oct_scale r x) = sed_scale r (emb tab5 x).
Proof. emb_lin_tac tab5. Qed.

(** ** Subspace 6: index set {0, 1, 6, 7, 8, 9, 14, 15}. *)

Lemma proj_emb_6 : forall x, proj tab6 (emb tab6 x) = x.
Proof. proj_emb_tac tab6. Qed.

Lemma emb_in_sub_6 : forall x, in_sub 6 (emb tab6 x).
Proof. emb_in_sub_tac tab6. Qed.

Lemma emb_proj_6 : forall s, in_sub 6 s -> emb tab6 (proj tab6 s) = s.
Proof. emb_proj_tac 6 tab6. Qed.

Lemma emb_mul_6 : forall x y,
  sed_mul (emb tab6 x) (emb tab6 y) = emb tab6 (oct_mul x y).
Proof. emb_mul_tac tab6. Qed.

Lemma emb_add_6 : forall x y,
  emb tab6 (oct_add x y) = sed_add (emb tab6 x) (emb tab6 y).
Proof. emb_lin_tac tab6. Qed.

Lemma emb_scale_6 : forall r x,
  emb tab6 (oct_scale r x) = sed_scale r (emb tab6 x).
Proof. emb_lin_tac tab6. Qed.

(** ** Subspace 7: index set {0, 3, 5, 6, 8, 11, 13, 14}. *)

Lemma proj_emb_7 : forall x, proj tab7 (emb tab7 x) = x.
Proof. proj_emb_tac tab7. Qed.

Lemma emb_in_sub_7 : forall x, in_sub 7 (emb tab7 x).
Proof. emb_in_sub_tac tab7. Qed.

Lemma emb_proj_7 : forall s, in_sub 7 s -> emb tab7 (proj tab7 s) = s.
Proof. emb_proj_tac 7 tab7. Qed.

Lemma emb_mul_7 : forall x y,
  sed_mul (emb tab7 x) (emb tab7 y) = emb tab7 (oct_mul x y).
Proof. emb_mul_tac tab7. Qed.

Lemma emb_add_7 : forall x y,
  emb tab7 (oct_add x y) = sed_add (emb tab7 x) (emb tab7 y).
Proof. emb_lin_tac tab7. Qed.

Lemma emb_scale_7 : forall r x,
  emb tab7 (oct_scale r x) = sed_scale r (emb tab7 x).
Proof. emb_lin_tac tab7. Qed.

(** ** Subspace 8: index set {0, 1, 2, 3, 4, 5, 6, 7}. *)

Lemma proj_emb_8 : forall x, proj tab8 (emb tab8 x) = x.
Proof. proj_emb_tac tab8. Qed.

Lemma emb_in_sub_8 : forall x, in_sub 8 (emb tab8 x).
Proof. emb_in_sub_tac tab8. Qed.

Lemma emb_proj_8 : forall s, in_sub 8 s -> emb tab8 (proj tab8 s) = s.
Proof. emb_proj_tac 8 tab8. Qed.

Lemma emb_mul_8 : forall x y,
  sed_mul (emb tab8 x) (emb tab8 y) = emb tab8 (oct_mul x y).
Proof. emb_mul_tac tab8. Qed.

Lemma emb_add_8 : forall x y,
  emb tab8 (oct_add x y) = sed_add (emb tab8 x) (emb tab8 y).
Proof. emb_lin_tac tab8. Qed.

Lemma emb_scale_8 : forall r x,
  emb tab8 (oct_scale r x) = sed_scale r (emb tab8 x).
Proof. emb_lin_tac tab8. Qed.

(** ** Subspace 9: index set {0, 2, 4, 6, 9, 11, 13, 15}. *)

Lemma proj_emb_9 : forall x, proj tab9 (emb tab9 x) = x.
Proof. proj_emb_tac tab9. Qed.

Lemma emb_in_sub_9 : forall x, in_sub 9 (emb tab9 x).
Proof. emb_in_sub_tac tab9. Qed.

Lemma emb_proj_9 : forall s, in_sub 9 s -> emb tab9 (proj tab9 s) = s.
Proof. emb_proj_tac 9 tab9. Qed.

Lemma mul_closed_9 : forall x y, exists z,
  sed_mul (emb tab9 x) (emb tab9 y) = emb tab9 z.
Proof. mul_closed_tac tab9. Qed.

Lemma not_left_alt_9 :
  let x := emb tab9 (oct_add (oct_e 1) (oct_e 4)) in
  let y := emb tab9 (oct_e 2) in
  sed_mul (sed_mul x x) y <> sed_mul x (sed_mul x y).
Proof. intros x y H. apply (f_equal (fun s => sed_coord s 15)) in H.
  revert H; cbv [x y]; unf tab9; intro H.
  lra. Qed.

(** ** Subspace 10: index set {0, 1, 4, 5, 10, 11, 14, 15}. *)

Lemma proj_emb_10 : forall x, proj tab10 (emb tab10 x) = x.
Proof. proj_emb_tac tab10. Qed.

Lemma emb_in_sub_10 : forall x, in_sub 10 (emb tab10 x).
Proof. emb_in_sub_tac tab10. Qed.

Lemma emb_proj_10 : forall s, in_sub 10 s -> emb tab10 (proj tab10 s) = s.
Proof. emb_proj_tac 10 tab10. Qed.

Lemma mul_closed_10 : forall x y, exists z,
  sed_mul (emb tab10 x) (emb tab10 y) = emb tab10 z.
Proof. mul_closed_tac tab10. Qed.

Lemma not_left_alt_10 :
  let x := emb tab10 (oct_add (oct_e 1) (oct_e 4)) in
  let y := emb tab10 (oct_e 2) in
  sed_mul (sed_mul x x) y <> sed_mul x (sed_mul x y).
Proof. intros x y H. apply (f_equal (fun s => sed_coord s 15)) in H.
  revert H; cbv [x y]; unf tab10; intro H.
  lra. Qed.

(** ** Subspace 11: index set {0, 3, 4, 7, 9, 10, 13, 14}. *)

Lemma proj_emb_11 : forall x, proj tab11 (emb tab11 x) = x.
Proof. proj_emb_tac tab11. Qed.

Lemma emb_in_sub_11 : forall x, in_sub 11 (emb tab11 x).
Proof. emb_in_sub_tac tab11. Qed.

Lemma emb_proj_11 : forall s, in_sub 11 s -> emb tab11 (proj tab11 s) = s.
Proof. emb_proj_tac 11 tab11. Qed.

Lemma mul_closed_11 : forall x y, exists z,
  sed_mul (emb tab11 x) (emb tab11 y) = emb tab11 z.
Proof. mul_closed_tac tab11. Qed.

Lemma not_left_alt_11 :
  let x := emb tab11 (oct_add (oct_e 1) (oct_e 4)) in
  let y := emb tab11 (oct_e 2) in
  sed_mul (sed_mul x x) y <> sed_mul x (sed_mul x y).
Proof. intros x y H. apply (f_equal (fun s => sed_coord s 14)) in H.
  revert H; cbv [x y]; unf tab11; intro H.
  lra. Qed.

(** ** Subspace 12: index set {0, 1, 2, 3, 12, 13, 14, 15}. *)

Lemma proj_emb_12 : forall x, proj tab12 (emb tab12 x) = x.
Proof. proj_emb_tac tab12. Qed.

Lemma emb_in_sub_12 : forall x, in_sub 12 (emb tab12 x).
Proof. emb_in_sub_tac tab12. Qed.

Lemma emb_proj_12 : forall s, in_sub 12 s -> emb tab12 (proj tab12 s) = s.
Proof. emb_proj_tac 12 tab12. Qed.

Lemma mul_closed_12 : forall x y, exists z,
  sed_mul (emb tab12 x) (emb tab12 y) = emb tab12 z.
Proof. mul_closed_tac tab12. Qed.

Lemma not_left_alt_12 :
  let x := emb tab12 (oct_add (oct_e 1) (oct_e 4)) in
  let y := emb tab12 (oct_e 2) in
  sed_mul (sed_mul x x) y <> sed_mul x (sed_mul x y).
Proof. intros x y H. apply (f_equal (fun s => sed_coord s 15)) in H.
  revert H; cbv [x y]; unf tab12; intro H.
  lra. Qed.

(** ** Subspace 13: index set {0, 2, 5, 7, 9, 11, 12, 14}. *)

Lemma proj_emb_13 : forall x, proj tab13 (emb tab13 x) = x.
Proof. proj_emb_tac tab13. Qed.

Lemma emb_in_sub_13 : forall x, in_sub 13 (emb tab13 x).
Proof. emb_in_sub_tac tab13. Qed.

Lemma emb_proj_13 : forall s, in_sub 13 s -> emb tab13 (proj tab13 s) = s.
Proof. emb_proj_tac 13 tab13. Qed.

Lemma mul_closed_13 : forall x y, exists z,
  sed_mul (emb tab13 x) (emb tab13 y) = emb tab13 z.
Proof. mul_closed_tac tab13. Qed.

Lemma not_left_alt_13 :
  let x := emb tab13 (oct_add (oct_e 1) (oct_e 4)) in
  let y := emb tab13 (oct_e 2) in
  sed_mul (sed_mul x x) y <> sed_mul x (sed_mul x y).
Proof. intros x y H. apply (f_equal (fun s => sed_coord s 14)) in H.
  revert H; cbv [x y]; unf tab13; intro H.
  lra. Qed.

(** ** Subspace 14: index set {0, 1, 6, 7, 10, 11, 12, 13}. *)

Lemma proj_emb_14 : forall x, proj tab14 (emb tab14 x) = x.
Proof. proj_emb_tac tab14. Qed.

Lemma emb_in_sub_14 : forall x, in_sub 14 (emb tab14 x).
Proof. emb_in_sub_tac tab14. Qed.

Lemma emb_proj_14 : forall s, in_sub 14 s -> emb tab14 (proj tab14 s) = s.
Proof. emb_proj_tac 14 tab14. Qed.

Lemma mul_closed_14 : forall x y, exists z,
  sed_mul (emb tab14 x) (emb tab14 y) = emb tab14 z.
Proof. mul_closed_tac tab14. Qed.

Lemma not_left_alt_14 :
  let x := emb tab14 (oct_add (oct_e 1) (oct_e 4)) in
  let y := emb tab14 (oct_e 2) in
  sed_mul (sed_mul x x) y <> sed_mul x (sed_mul x y).
Proof. intros x y H. apply (f_equal (fun s => sed_coord s 13)) in H.
  revert H; cbv [x y]; unf tab14; intro H.
  lra. Qed.

(** ** Subspace 15: index set {0, 3, 5, 6, 9, 10, 12, 15}. *)

Lemma proj_emb_15 : forall x, proj tab15 (emb tab15 x) = x.
Proof. proj_emb_tac tab15. Qed.

Lemma emb_in_sub_15 : forall x, in_sub 15 (emb tab15 x).
Proof. emb_in_sub_tac tab15. Qed.

Lemma emb_proj_15 : forall s, in_sub 15 s -> emb tab15 (proj tab15 s) = s.
Proof. emb_proj_tac 15 tab15. Qed.

Lemma mul_closed_15 : forall x y, exists z,
  sed_mul (emb tab15 x) (emb tab15 y) = emb tab15 z.
Proof. mul_closed_tac tab15. Qed.

Lemma not_left_alt_15 :
  let x := emb tab15 (oct_add (oct_e 1) (oct_e 4)) in
  let y := emb tab15 (oct_e 2) in
  sed_mul (sed_mul x x) y <> sed_mul x (sed_mul x y).
Proof. intros x y H. apply (f_equal (fun s => sed_coord s 15)) in H.
  revert H; cbv [x y]; unf tab15; intro H.
  lra. Qed.

(** * The family and its subalgebra facts. *)

Definition tabs (u : nat) : nat -> nat * R :=
  match u with
  | 1%nat => tab1
  | 2%nat => tab2
  | 3%nat => tab3
  | 4%nat => tab4
  | 5%nat => tab5
  | 6%nat => tab6
  | 7%nat => tab7
  | 8%nat => tab8
  | 9%nat => tab9
  | 10%nat => tab10
  | 11%nat => tab11
  | 12%nat => tab12
  | 13%nat => tab13
  | 14%nat => tab14
  | 15%nat => tab15
  | _ => tab1
  end.

Definition emb_ok (u : nat) : Prop :=
  (forall x, in_sub u (emb (tabs u) x))
  /\ (forall x, proj (tabs u) (emb (tabs u) x) = x)
  /\ (forall s, in_sub u s -> emb (tabs u) (proj (tabs u) s) = s).

Lemma emb_ok_all : forall u, (1 <= u <= 15)%nat -> emb_ok u.
Proof.
  intros u Hu.
  assert (Hc : u = 1%nat \/ u = 2%nat \/ u = 3%nat \/ u = 4%nat \/ u = 5%nat \/ u = 6%nat \/ u = 7%nat \/ u = 8%nat \/ u = 9%nat \/ u = 10%nat \/ u = 11%nat \/ u = 12%nat \/ u = 13%nat \/ u = 14%nat \/ u = 15%nat) by lia.
  destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ] ] ] ] ] ] ] ] ].
  - exact (conj emb_in_sub_1 (conj proj_emb_1 emb_proj_1)).
  - exact (conj emb_in_sub_2 (conj proj_emb_2 emb_proj_2)).
  - exact (conj emb_in_sub_3 (conj proj_emb_3 emb_proj_3)).
  - exact (conj emb_in_sub_4 (conj proj_emb_4 emb_proj_4)).
  - exact (conj emb_in_sub_5 (conj proj_emb_5 emb_proj_5)).
  - exact (conj emb_in_sub_6 (conj proj_emb_6 emb_proj_6)).
  - exact (conj emb_in_sub_7 (conj proj_emb_7 emb_proj_7)).
  - exact (conj emb_in_sub_8 (conj proj_emb_8 emb_proj_8)).
  - exact (conj emb_in_sub_9 (conj proj_emb_9 emb_proj_9)).
  - exact (conj emb_in_sub_10 (conj proj_emb_10 emb_proj_10)).
  - exact (conj emb_in_sub_11 (conj proj_emb_11 emb_proj_11)).
  - exact (conj emb_in_sub_12 (conj proj_emb_12 emb_proj_12)).
  - exact (conj emb_in_sub_13 (conj proj_emb_13 emb_proj_13)).
  - exact (conj emb_in_sub_14 (conj proj_emb_14 emb_proj_14)).
  - exact (conj emb_in_sub_15 (conj proj_emb_15 emb_proj_15)).
Qed.

(** [mul_closed u]: the product of two embedded octonions is embedded. *)
Definition mul_closed (u : nat) : Prop :=
  forall x y, exists z,
    sed_mul (emb (tabs u) x) (emb (tabs u) y) = emb (tabs u) z.

Lemma mul_closed_all : forall u, (1 <= u <= 15)%nat -> mul_closed u.
Proof.
  intros u Hu.
  assert (Hc : u = 1%nat \/ u = 2%nat \/ u = 3%nat \/ u = 4%nat \/ u = 5%nat \/ u = 6%nat \/ u = 7%nat \/ u = 8%nat \/ u = 9%nat \/ u = 10%nat \/ u = 11%nat \/ u = 12%nat \/ u = 13%nat \/ u = 14%nat \/ u = 15%nat) by lia.
  destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ] ] ] ] ] ] ] ] ].
  - intros x y; exists (oct_mul x y); exact (emb_mul_1 x y).
  - intros x y; exists (oct_mul x y); exact (emb_mul_2 x y).
  - intros x y; exists (oct_mul x y); exact (emb_mul_3 x y).
  - intros x y; exists (oct_mul x y); exact (emb_mul_4 x y).
  - intros x y; exists (oct_mul x y); exact (emb_mul_5 x y).
  - intros x y; exists (oct_mul x y); exact (emb_mul_6 x y).
  - intros x y; exists (oct_mul x y); exact (emb_mul_7 x y).
  - intros x y; exists (oct_mul x y); exact (emb_mul_8 x y).
  - exact mul_closed_9.
  - exact mul_closed_10.
  - exact mul_closed_11.
  - exact mul_closed_12.
  - exact mul_closed_13.
  - exact mul_closed_14.
  - exact mul_closed_15.
Qed.

(** * Every member of the family is closed under the sedenion product. *)
Theorem C029_family_closed : forall u, (1 <= u <= 15)%nat ->
  forall x y, in_sub u x -> in_sub u y -> in_sub u (sed_mul x y).
Proof.
  intros u Hu x y Hx Hy.
  destruct (emb_ok_all u Hu) as [E1 [E2 E3]].
  destruct (mul_closed_all u Hu (proj (tabs u) x) (proj (tabs u) y)) as [z Hz].
  rewrite (E3 x Hx) in Hz. rewrite (E3 y Hy) in Hz.
  rewrite Hz. apply E1.
Qed.

(** * The members isomorphic to the octonions. *)

(** [oct_sub_iso u]: a linear, product-preserving, injective map from the
    octonions whose image is exactly the member [u]. *)
Definition oct_sub_iso (u : nat) : Prop :=
  exists phi : CDOct -> CDSed,
    (forall a b, phi (oct_mul a b) = sed_mul (phi a) (phi b))
    /\ (forall a b, phi (oct_add a b) = sed_add (phi a) (phi b))
    /\ (forall r a, phi (oct_scale r a) = sed_scale r (phi a))
    /\ (forall a b, phi a = phi b -> a = b)
    /\ (forall s, in_sub u s <-> exists a, phi a = s).

Lemma iso_small : forall u, (1 <= u <= 8)%nat -> oct_sub_iso u.
Proof.
  intros u Hu.
  assert (Hc : u = 1%nat \/ u = 2%nat \/ u = 3%nat \/ u = 4%nat \/ u = 5%nat \/ u = 6%nat \/ u = 7%nat \/ u = 8%nat) by lia.
  destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ] ].
  - exists (emb tab1); repeat split.
    + intros a b. symmetry. exact (emb_mul_1 a b).
    + exact emb_add_1.
    + exact emb_scale_1.
    + intros a b H. rewrite <- (proj_emb_1 a), <- (proj_emb_1 b), H. reflexivity.
    + intros Hs. exists (proj tab1 s). exact (emb_proj_1 s Hs).
    + intros [a Ha]. rewrite <- Ha. exact (emb_in_sub_1 a).
  - exists (emb tab2); repeat split.
    + intros a b. symmetry. exact (emb_mul_2 a b).
    + exact emb_add_2.
    + exact emb_scale_2.
    + intros a b H. rewrite <- (proj_emb_2 a), <- (proj_emb_2 b), H. reflexivity.
    + intros Hs. exists (proj tab2 s). exact (emb_proj_2 s Hs).
    + intros [a Ha]. rewrite <- Ha. exact (emb_in_sub_2 a).
  - exists (emb tab3); repeat split.
    + intros a b. symmetry. exact (emb_mul_3 a b).
    + exact emb_add_3.
    + exact emb_scale_3.
    + intros a b H. rewrite <- (proj_emb_3 a), <- (proj_emb_3 b), H. reflexivity.
    + intros Hs. exists (proj tab3 s). exact (emb_proj_3 s Hs).
    + intros [a Ha]. rewrite <- Ha. exact (emb_in_sub_3 a).
  - exists (emb tab4); repeat split.
    + intros a b. symmetry. exact (emb_mul_4 a b).
    + exact emb_add_4.
    + exact emb_scale_4.
    + intros a b H. rewrite <- (proj_emb_4 a), <- (proj_emb_4 b), H. reflexivity.
    + intros Hs. exists (proj tab4 s). exact (emb_proj_4 s Hs).
    + intros [a Ha]. rewrite <- Ha. exact (emb_in_sub_4 a).
  - exists (emb tab5); repeat split.
    + intros a b. symmetry. exact (emb_mul_5 a b).
    + exact emb_add_5.
    + exact emb_scale_5.
    + intros a b H. rewrite <- (proj_emb_5 a), <- (proj_emb_5 b), H. reflexivity.
    + intros Hs. exists (proj tab5 s). exact (emb_proj_5 s Hs).
    + intros [a Ha]. rewrite <- Ha. exact (emb_in_sub_5 a).
  - exists (emb tab6); repeat split.
    + intros a b. symmetry. exact (emb_mul_6 a b).
    + exact emb_add_6.
    + exact emb_scale_6.
    + intros a b H. rewrite <- (proj_emb_6 a), <- (proj_emb_6 b), H. reflexivity.
    + intros Hs. exists (proj tab6 s). exact (emb_proj_6 s Hs).
    + intros [a Ha]. rewrite <- Ha. exact (emb_in_sub_6 a).
  - exists (emb tab7); repeat split.
    + intros a b. symmetry. exact (emb_mul_7 a b).
    + exact emb_add_7.
    + exact emb_scale_7.
    + intros a b H. rewrite <- (proj_emb_7 a), <- (proj_emb_7 b), H. reflexivity.
    + intros Hs. exists (proj tab7 s). exact (emb_proj_7 s Hs).
    + intros [a Ha]. rewrite <- Ha. exact (emb_in_sub_7 a).
  - exists (emb tab8); repeat split.
    + intros a b. symmetry. exact (emb_mul_8 a b).
    + exact emb_add_8.
    + exact emb_scale_8.
    + intros a b H. rewrite <- (proj_emb_8 a), <- (proj_emb_8 b), H. reflexivity.
    + intros Hs. exists (proj tab8 s). exact (emb_proj_8 s Hs).
    + intros [a Ha]. rewrite <- Ha. exact (emb_in_sub_8 a).
Qed.

(** A product-preserving map from the octonions carries the left
    alternative law to its image. *)
Lemma left_alt_transfer : forall phi : CDOct -> CDSed,
  (forall a b, phi (oct_mul a b) = sed_mul (phi a) (phi b)) ->
  forall a b,
    sed_mul (sed_mul (phi a) (phi a)) (phi b)
    = sed_mul (phi a) (sed_mul (phi a) (phi b)).
Proof.
  intros phi Hm a b.
  rewrite <- (Hm a a), <- (Hm a b), <- (Hm (oct_mul a a) b),
          <- (Hm a (oct_mul a b)).
  rewrite oct_left_alt_gen. reflexivity.
Qed.

Lemma not_iso_large : forall u, (9 <= u <= 15)%nat -> ~ oct_sub_iso u.
Proof.
  intros u Hu [phi [Hm [_ [_ [_ Him]]]]].
  assert (Hc : u = 9%nat \/ u = 10%nat \/ u = 11%nat \/ u = 12%nat \/ u = 13%nat \/ u = 14%nat \/ u = 15%nat) by lia.
  destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ].
  - destruct (proj1 (Him (emb tab9 (oct_add (oct_e 1) (oct_e 4)))) (emb_in_sub_9 _)) as [a Ha].
    destruct (proj1 (Him (emb tab9 (oct_e 2))) (emb_in_sub_9 _)) as [b Hb].
    pose proof (left_alt_transfer phi Hm a b) as Ht.
    rewrite Ha, Hb in Ht. exact (not_left_alt_9 Ht).
  - destruct (proj1 (Him (emb tab10 (oct_add (oct_e 1) (oct_e 4)))) (emb_in_sub_10 _)) as [a Ha].
    destruct (proj1 (Him (emb tab10 (oct_e 2))) (emb_in_sub_10 _)) as [b Hb].
    pose proof (left_alt_transfer phi Hm a b) as Ht.
    rewrite Ha, Hb in Ht. exact (not_left_alt_10 Ht).
  - destruct (proj1 (Him (emb tab11 (oct_add (oct_e 1) (oct_e 4)))) (emb_in_sub_11 _)) as [a Ha].
    destruct (proj1 (Him (emb tab11 (oct_e 2))) (emb_in_sub_11 _)) as [b Hb].
    pose proof (left_alt_transfer phi Hm a b) as Ht.
    rewrite Ha, Hb in Ht. exact (not_left_alt_11 Ht).
  - destruct (proj1 (Him (emb tab12 (oct_add (oct_e 1) (oct_e 4)))) (emb_in_sub_12 _)) as [a Ha].
    destruct (proj1 (Him (emb tab12 (oct_e 2))) (emb_in_sub_12 _)) as [b Hb].
    pose proof (left_alt_transfer phi Hm a b) as Ht.
    rewrite Ha, Hb in Ht. exact (not_left_alt_12 Ht).
  - destruct (proj1 (Him (emb tab13 (oct_add (oct_e 1) (oct_e 4)))) (emb_in_sub_13 _)) as [a Ha].
    destruct (proj1 (Him (emb tab13 (oct_e 2))) (emb_in_sub_13 _)) as [b Hb].
    pose proof (left_alt_transfer phi Hm a b) as Ht.
    rewrite Ha, Hb in Ht. exact (not_left_alt_13 Ht).
  - destruct (proj1 (Him (emb tab14 (oct_add (oct_e 1) (oct_e 4)))) (emb_in_sub_14 _)) as [a Ha].
    destruct (proj1 (Him (emb tab14 (oct_e 2))) (emb_in_sub_14 _)) as [b Hb].
    pose proof (left_alt_transfer phi Hm a b) as Ht.
    rewrite Ha, Hb in Ht. exact (not_left_alt_14 Ht).
  - destruct (proj1 (Him (emb tab15 (oct_add (oct_e 1) (oct_e 4)))) (emb_in_sub_15 _)) as [a Ha].
    destruct (proj1 (Him (emb tab15 (oct_e 2))) (emb_in_sub_15 _)) as [b Hb].
    pose proof (left_alt_transfer phi Hm a b) as Ht.
    rewrite Ha, Hb in Ht. exact (not_left_alt_15 Ht).
Qed.

Theorem C029_octonion_subalgebra_iff : forall u, (1 <= u <= 15)%nat ->
  (oct_sub_iso u <-> (u <= 8)%nat).
Proof.
  intros u Hu. split.
  - intros H. destruct (Nat.le_gt_cases u 8) as [Hle | Hgt]; [exact Hle |].
    exfalso. exact (not_iso_large u ltac:(lia) H).
  - intros H. apply iso_small. lia.
Qed.

(** Exactly 8 of the 15 members are isomorphic to the octonions. *)
Theorem C029_octonion_subalgebra_count :
  exists L : list nat,
    NoDup L /\ length L = 8%nat
    /\ forall u, In u L <-> ((1 <= u <= 15)%nat /\ oct_sub_iso u).
Proof.
  exists (seq 1 8). split; [apply seq_NoDup |]. split; [reflexivity |].
  intros u. rewrite in_seq. split.
  - intros H. split; [lia |]. apply iso_small. lia.
  - intros [Hu H]. apply (C029_octonion_subalgebra_iff u Hu) in H. lia.
Qed.

(** * The 15 members are pairwise distinct subspaces. *)

Lemma sed_coord_e : forall k j, (k < 16)%nat ->
  sed_coord (sed_e k) j = if Nat.eqb k j then 1 else 0.
Proof.
  intros k j Hk.
  do 16 (destruct k as [|k];
         [ do 16 (destruct j as [|j];
                  [ cbv [sed_coord sed_e oct_e oct_coord oct_zero
                         quat_zero quat_one oct_lo oct_hi sed_lo sed_hi
                         qa qb qc qd Nat.eqb]; reflexivity | ]);
           cbv [sed_coord sed_e oct_e oct_coord oct_zero quat_zero quat_one
                oct_lo oct_hi sed_lo sed_hi qa qb qc qd Nat.eqb];
           reflexivity
         | ]).
  exfalso. lia.
Qed.

Lemma in_sub_e : forall u k, (k < 16)%nat ->
  (in_sub u (sed_e k) <-> off_sub u k = false).
Proof.
  intros u k Hk. split.
  - intros H. destruct (off_sub u k) eqn:E; [| reflexivity].
    pose proof (H k E) as H1. rewrite sed_coord_e in H1 by exact Hk.
    rewrite Nat.eqb_refl in H1. lra.
  - intros H j Hj. rewrite sed_coord_e by exact Hk.
    destruct (Nat.eqb k j) eqn:E; [| reflexivity].
    apply Nat.eqb_eq in E. subst j. rewrite H in Hj. discriminate Hj.
Qed.

Lemma off_differ_check : forallb (fun u => forallb (fun v =>
    orb (Nat.eqb u v) (existsb (fun k =>
      negb (Bool.eqb (off_sub u k) (off_sub v k))) (seq 0 16)))
    (seq 1 15)) (seq 1 15) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma off_differ : forall u v, (1 <= u <= 15)%nat -> (1 <= v <= 15)%nat ->
  u <> v -> exists k, (k < 16)%nat /\ off_sub u k <> off_sub v k.
Proof.
  intros u v Hu Hv Huv.
  pose proof off_differ_check as C.
  rewrite forallb_forall in C.
  specialize (C u ltac:(apply in_seq; lia)).
  rewrite forallb_forall in C.
  specialize (C v ltac:(apply in_seq; lia)).
  apply Bool.orb_true_iff in C. destruct C as [C | C].
  - apply Nat.eqb_eq in C. contradiction.
  - apply existsb_exists in C. destruct C as [k [Hk C]].
    apply in_seq in Hk. exists k. split; [lia |].
    apply Bool.negb_true_iff in C. intros E. rewrite E in C.
    rewrite Bool.eqb_reflx in C. discriminate C.
Qed.

Theorem C029_family_distinct : forall u v,
  (1 <= u <= 15)%nat -> (1 <= v <= 15)%nat ->
  (forall s, in_sub u s <-> in_sub v s) -> u = v.
Proof.
  intros u v Hu Hv H.
  destruct (Nat.eq_dec u v) as [E | N]; [exact E |].
  destruct (off_differ u v Hu Hv N) as [k [Hk D]].
  exfalso.
  pose proof (H (sed_e k)) as Hs.
  rewrite (in_sub_e u k Hk), (in_sub_e v k Hk) in Hs.
  destruct (off_sub u k), (off_sub v k); try (apply D; reflexivity);
  [ destruct Hs as [H1 H2]; discriminate (H2 eq_refl)
  | destruct Hs as [H1 H2]; discriminate (H1 eq_refl) ].
Qed.

(** * The low half is the member 8. *)

Lemma emb_tab8_lo : forall x, emb tab8 x = mkSed x oct_zero.
Proof.
  intros x. dx x. unf tab8. cbv [oct_zero quat_zero].
  f_equal; f_equal; f_equal; ring.
Qed.

(** * Subsets that are not subalgebras. *)

(** The high half: two factors with [sed_lo = 0] have a product with
    [sed_lo <> 0]. *)
Theorem C029_high_half_not_closed :
  sed_lo (sed_e 8) = oct_zero
  /\ sed_mul (sed_e 8) (sed_e 8) = sed_scale (-1) (sed_e 0)
  /\ sed_lo (sed_mul (sed_e 8) (sed_e 8)) <> oct_zero.
Proof.
  split; [reflexivity |]. split.
  - cbv [sed_e oct_e sed_mul oct_mul oct_conj oct_zero sed_scale oct_scale
         quat_scale sed_lo sed_hi oct_lo oct_hi quat_mul quat_add quat_neg
         quat_conj quat_zero quat_one qa qb qc qd].
    f_equal; f_equal; f_equal; ring.
  - cbv [sed_e oct_e sed_mul oct_mul oct_conj oct_zero sed_lo sed_hi oct_lo
         oct_hi quat_mul quat_add quat_neg quat_conj quat_zero quat_one
         qa qb qc qd].
    intros H. injection H as H1 _. lra.
Qed.

(** The diagonal [sed_lo s = sed_hi s]: [(1,1)(1,1) = (0,2)]. *)
Theorem C029_diagonal_not_closed :
  sed_lo (mkSed (oct_e 0) (oct_e 0)) = sed_hi (mkSed (oct_e 0) (oct_e 0))
  /\ sed_lo (sed_mul (mkSed (oct_e 0) (oct_e 0)) (mkSed (oct_e 0) (oct_e 0)))
     <> sed_hi (sed_mul (mkSed (oct_e 0) (oct_e 0)) (mkSed (oct_e 0) (oct_e 0))).
Proof.
  split; [reflexivity |].
  cbv [oct_e sed_mul oct_mul oct_conj oct_zero sed_lo sed_hi oct_lo oct_hi
       quat_mul quat_add quat_neg quat_conj quat_zero quat_one qa qb qc qd].
  intros H. injection H as H1 _. lra.
Qed.

(** An 8-index set containing 0 that is not closed under xor: the real
    span of its units contains units whose product leaves the span. *)
Definition span_idx (S : list nat) (s : CDSed) : Prop :=
  forall k, ~ In k S -> sed_coord s k = 0.

Theorem C029_degenerate_index_set_not_closed :
  let S := (0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 8 :: nil)%nat in
  span_idx S (sed_e 3) /\ span_idx S (sed_e 4)
  /\ ~ span_idx S (sed_mul (sed_e 3) (sed_e 4)).
Proof.
  intros S. repeat split.
  - intros k Hk. destruct (Nat.lt_ge_cases k 16) as [Hlt | Hge].
    + rewrite sed_coord_e by lia. destruct (Nat.eqb 3 k) eqn:E; [| reflexivity].
      apply Nat.eqb_eq in E. subst k. exfalso. apply Hk. simpl. tauto.
    + do 16 (destruct k as [|k]; [lia |]). reflexivity.
  - intros k Hk. destruct (Nat.lt_ge_cases k 16) as [Hlt | Hge].
    + rewrite sed_coord_e by lia. destruct (Nat.eqb 4 k) eqn:E; [| reflexivity].
      apply Nat.eqb_eq in E. subst k. exfalso. apply Hk. simpl. tauto.
    + do 16 (destruct k as [|k]; [lia |]). reflexivity.
  - intros H. specialize (H 7%nat ltac:(simpl; intuition lia)).
    cbv [sed_coord oct_coord sed_e oct_e sed_mul oct_mul oct_conj oct_zero
         sed_lo sed_hi oct_lo oct_hi quat_mul quat_add quat_neg quat_conj
         quat_zero quat_one qa qb qc qd] in H.
    lra.
Qed.
