(** * C-1463: eight sedenion left multiplications satisfy the Cl(0, 8)
    relations and their 256 monomials form a basis of M(16, R).

    Convention: the sedenion basis e_0 .. e_15 is indexed by the bit patterns
    of Sedenion.sed_e, and e_i * e_j = sigma(i, j) e_{i XOR j} with
    sigma = CDFusedBilinear.sed_sign (the bounded Cayley-Dickson sign
    recurrence cd_sign_fuel 5 16).  [Gmat a] is the 16 x 16 real matrix of
    x |-> e_a * x in this basis: its entry (j, l) is the coefficient of e_j
    in e_a * e_l, which is sigma(a, l) at j = a XOR l and 0 elsewhere.  [mat],
    [mmul], [mat_eq] and [sum_to] are those of C1463_MatrixColumnIdeal, so a
    matrix is a function nat -> nat -> R read on 0 .. 15.  [Idmat] is the
    identity.  The monomial G_S, for S a subset of {1 .. 8}, is the product
    of the G_a with a in S in increasing order, G_empty = Idmat; [Gm m] is
    G_S for the S whose indicator is the bit pattern of m < 256 (bit a - 1
    set exactly when a is in S).  The signature is Cl(0, 8): each
    generator squares to -1.  C1463_ArithmeticInventory names the
    256-dimensional algebra Cl8 (cl8_dim, cl8_is_mat16) and fixes no
    signature.

    Theorems.
    - [Gmat_is_left_mult_on_basis] and [Gmat_is_left_mult] tie [Gmat a] to
      Sedenion.sed_mul: the coordinates of e_a * e_l are the column l of
      [Gmat a], and for every vector v the coordinates of
      e_a * (sum_l v_l e_l) are [Gmat a] applied to v.  The table of signs
      is [sed_sign] of CDFusedBilinear, which that file proves equal to the
      basis products of sed_mul; [sed_sign_agrees_with_C1467] shows that the
      literal table of C1467_XORSignCocycle agrees with it on all 256 cells.
    - [Gmat_square] and [Gmat_anticommute]: for a, b in 1 .. 8, G_a G_a = -I,
      and G_a G_b + G_b G_a = 0 for a <> b (the relations of Cl(0, 8)).
    - [C1463_trace_orthogonality]: trace(G_S^T G_T) is 16 if S = T and 0
      otherwise, for all 65536 pairs of monomials, by an evaluation of
      integer signed-permutation products.
    - [C1463_monomials_independent]: a real combination of the 256 monomials
      that vanishes on 0 .. 15 has every coefficient zero.
    - [C1463_matrix_unit_in_span] and [C1463_monomials_span]: each matrix
      unit E_ij is the combination of the monomials with coefficients
      (G_S)_ij / 16, and every real 16 x 16 matrix M is the combination with
      coefficients trace(M^T G_S) / 16.  Surjectivity is proved directly,
      through a finite check of the 256-term column relations, and not by
      a dimension count.
    - [C1463_column_ideal_compat] and [C1463_monomial_column_compat]: reading
      column 0 of a matrix as a sedenion by [sed_of_vec] (inverse to [coord]),
      left multiplication by [Gmat a] is sed_mul (sed_e a), and the monomial
      G_S acts as the iterated left multiplication e_a1 (e_a2 (... x)).
      [col_embed] gives the converse embedding of R^16 into the column ideal
      [col_space 16 0].
    - [C1463_clifford_matrix_basis] collects the relations, the orthogonality,
      the independence and the spanning statement.

    Scope.  This exhibits a representation of the Clifford relations on
    R^16 whose 256 ordered monomials are a basis of M(16, R).  The abstract
    algebra Cl(0, 8), a quotient of the tensor algebra, is not defined here.
    The statement that Cl(0, 8) is isomorphic to M(16, R) follows from
    these theorems together with the standard fact that Cl(0, 8) is spanned
    by its 256 ordered monomials; that step is not formalized.  The
    equivalence of "256 independent elements" with "a basis of a
    256-dimensional space" is not proved either, since the spanning theorem
    covers it directly.  The index m of [Gm] covers all 256 bit patterns;
    that the subsets so listed are pairwise distinct is a consequence of
    [C1463_monomials_independent] and is not stated separately.

    Cost (Rocq 9.3.0, one 4-vCPU host): the compile takes 51 s; rocq check
    of this module with its required libraries takes 76 s, 34 s of which
    re-check the imports (CDFusedBilinear, C1467_XORSignCocycle,
    C1463_MatrixColumnIdeal and their closure).

    Trust.  The proofs use the real-number axioms that Stdlib Reals carries
    (see Print Assumptions below).  [gram_check] and [comp_check] are
    evaluations by vm_compute of boolean checks over the 256 monomials
    (65536 pairs, and 4096 triples of class and row indices); the
    kernel replays them. *)


From Stdlib Require Import Reals Lra Lia Arith PeanoNat Bool List ZArith.
From OpenGororoba Require Import
  CayleyDicksonAlgebra Sedenion OctonionNorm CDLinearLemmas CDSignBridge
  CDFusedBilinear.
From OpenGororobaVerified Require Import C1463_MatrixColumnIdeal.
From OpenGororobaVerified Require C1467_XORSignCocycle.
Import ListNotations.

Local Open Scope nat_scope.

(** ** Finite-check helpers *)

Fixpoint all_lt (n : nat) (p : nat -> bool) : bool :=
  match n with
  | O => true
  | S m => all_lt m p && p m
  end.

Lemma all_lt_spec :
  forall n p, all_lt n p = true -> forall i, i < n -> p i = true.
Proof.
  induction n as [|m IH]; intros p H i Hi; [lia |].
  simpl in H. apply andb_prop in H as [H1 H2].
  destruct (Nat.eq_dec i m) as [-> | E]; [exact H2 |].
  apply IH; [exact H1 | lia].
Qed.

Lemma all_lt2 :
  forall n (p : nat -> nat -> bool),
    all_lt n (fun a => all_lt n (fun b => p a b)) = true ->
    forall a b, a < n -> b < n -> p a b = true.
Proof.
  intros n p H a b Ha Hb.
  pose proof (all_lt_spec _ _ H a Ha) as H1. cbv beta in H1.
  exact (all_lt_spec _ _ H1 b Hb).
Qed.

Lemma all_lt3 :
  forall n (p : nat -> nat -> nat -> bool),
    all_lt n (fun a => all_lt n (fun b => all_lt n (fun c => p a b c))) = true ->
    forall a b c, a < n -> b < n -> c < n -> p a b c = true.
Proof.
  intros n p H a b c Ha Hb Hc.
  pose proof (all_lt_spec _ _ H a Ha) as H1. cbv beta in H1.
  exact (all_lt2 n (fun b c => p a b c) H1 b c Hb Hc).
Qed.

Fixpoint zsum_to (n : nat) (f : nat -> Z) : Z :=
  match n with
  | O => 0%Z
  | S m => (zsum_to m f + f m)%Z
  end.

Lemma sum_to_IZR :
  forall n f, sum_to n (fun r => IZR (f r)) = IZR (zsum_to n f).
Proof.
  induction n as [|m IH]; intros f; simpl; [reflexivity |].
  rewrite IH, plus_IZR. reflexivity.
Qed.

Lemma zsum_to_zero :
  forall n f, (forall l, l < n -> f l = 0%Z) -> zsum_to n f = 0%Z.
Proof.
  induction n as [|m IH]; intros f H; simpl; [reflexivity |].
  rewrite IH by (intros l Hl; apply H; lia).
  rewrite (H m) by lia. reflexivity.
Qed.

Lemma sum_to_ext :
  forall n f g, (forall l, l < n -> f l = g l) -> sum_to n f = sum_to n g.
Proof.
  induction n as [|m IH]; intros f g H; simpl; [reflexivity |].
  rewrite (IH f g) by (intros l Hl; apply H; lia).
  rewrite (H m) by lia. reflexivity.
Qed.

Lemma sum_to_add :
  forall n f g,
    sum_to n (fun l => (f l + g l)%R) = (sum_to n f + sum_to n g)%R.
Proof.
  induction n as [|m IH]; intros f g; simpl; [ring |].
  rewrite IH. ring.
Qed.

Lemma sum_to_scale :
  forall n c f, sum_to n (fun l => (c * f l)%R) = (c * sum_to n f)%R.
Proof.
  induction n as [|m IH]; intros c f; simpl; [ring |].
  rewrite IH. ring.
Qed.

Lemma sum_to_mul_r :
  forall n f h, (sum_to n f * h)%R = sum_to n (fun l => (f l * h)%R).
Proof.
  induction n as [|m IH]; intros f h; simpl; [ring |].
  rewrite <- IH. ring.
Qed.

Lemma sum_to_swap :
  forall n m (f : nat -> nat -> R),
    sum_to n (fun i => sum_to m (fun j => f i j)) =
    sum_to m (fun j => sum_to n (fun i => f i j)).
Proof.
  induction n as [|n IH]; intros m f; simpl.
  - symmetry. apply sum_to_zero. intros; reflexivity.
  - rewrite IH. rewrite <- sum_to_add. reflexivity.
Qed.

Lemma nth_map_seq :
  forall (f : nat -> Z) n r, r < n -> nth r (map f (seq 0 n)) 0%Z = f r.
Proof.
  intros f n r H.
  rewrite (nth_indep _ _ (f 0)) by (rewrite length_map, length_seq; exact H).
  rewrite map_nth, seq_nth by exact H. reflexivity.
Qed.

(** ** Bitwise facts on indices below 16, decided by evaluation *)

Lemma xor_lt16 : forall a b, a < 16 -> b < 16 -> Nat.lxor a b < 16.
Proof.
  intros a b Ha Hb.
  assert (H : all_lt 16 (fun a => all_lt 16 (fun b =>
                Nat.ltb (Nat.lxor a b) 16)) = true)
    by (vm_compute; reflexivity).
  apply Nat.ltb_lt. exact (all_lt2 16 (fun a b => Nat.ltb (Nat.lxor a b) 16) H a b Ha Hb).
Qed.

Lemma xor_shift :
  forall a b r, a < 16 -> b < 16 -> r < 16 ->
    Nat.lxor (Nat.lxor a b) r = Nat.lxor b (Nat.lxor a r).
Proof.
  intros a b r Ha Hb Hr.
  assert (H : all_lt 16 (fun a => all_lt 16 (fun b => all_lt 16 (fun r =>
      Nat.eqb (Nat.lxor (Nat.lxor a b) r) (Nat.lxor b (Nat.lxor a r))))) = true)
    by (vm_compute; reflexivity).
  apply Nat.eqb_eq.
  exact (all_lt3 16 (fun a b r =>
    Nat.eqb (Nat.lxor (Nat.lxor a b) r) (Nat.lxor b (Nat.lxor a r))) H a b r Ha Hb Hr).
Qed.

Lemma xor_cancel :
  forall a b r, a < 16 -> b < 16 -> r < 16 ->
    Nat.eqb (Nat.lxor a r) (Nat.lxor b r) = Nat.eqb a b.
Proof.
  intros a b r Ha Hb Hr.
  assert (H : all_lt 16 (fun a => all_lt 16 (fun b => all_lt 16 (fun r =>
      Bool.eqb (Nat.eqb (Nat.lxor a r) (Nat.lxor b r)) (Nat.eqb a b)))) = true)
    by (vm_compute; reflexivity).
  apply Bool.eqb_prop.
  exact (all_lt3 16 (fun a b r =>
    Bool.eqb (Nat.eqb (Nat.lxor a r) (Nat.lxor b r)) (Nat.eqb a b)) H a b r Ha Hb Hr).
Qed.

Lemma xor_iff :
  forall a i j, a < 16 -> i < 16 -> j < 16 ->
    Nat.eqb j (Nat.lxor a i) = Nat.eqb a (Nat.lxor i j).
Proof.
  intros a i j Ha Hi Hj.
  assert (H : all_lt 16 (fun a => all_lt 16 (fun i => all_lt 16 (fun j =>
      Bool.eqb (Nat.eqb j (Nat.lxor a i)) (Nat.eqb a (Nat.lxor i j))))) = true)
    by (vm_compute; reflexivity).
  apply Bool.eqb_prop.
  exact (all_lt3 16 (fun a i j =>
    Bool.eqb (Nat.eqb j (Nat.lxor a i)) (Nat.eqb a (Nat.lxor i j))) H a i j Ha Hi Hj).
Qed.

Lemma xor_sym :
  forall a j l, a < 16 -> j < 16 -> l < 16 ->
    Nat.eqb j (Nat.lxor a l) = Nat.eqb l (Nat.lxor a j).
Proof.
  intros a j l Ha Hj Hl.
  assert (H : all_lt 16 (fun a => all_lt 16 (fun j => all_lt 16 (fun l =>
      Bool.eqb (Nat.eqb j (Nat.lxor a l)) (Nat.eqb l (Nat.lxor a j))))) = true)
    by (vm_compute; reflexivity).
  apply Bool.eqb_prop.
  exact (all_lt3 16 (fun a j l =>
    Bool.eqb (Nat.eqb j (Nat.lxor a l)) (Nat.eqb l (Nat.lxor a j))) H a j l Ha Hj Hl).
Qed.

(** ** The sign table and its tie to the sedenion product *)

(** The sign function of [CDFusedBilinear.sed_sign] is [cd_sign_fuel 5 16]; the
    table of [C1467_XORSignCocycle] agrees with it on all 256 cells. *)
Theorem sed_sign_agrees_with_C1467 :
  forall i j, i < 16 -> j < 16 ->
    C1467_XORSignCocycle.sed_sign i j = sed_sign i j.
Proof.
  intros i j Hi Hj.
  assert (H : all_lt 16 (fun i => all_lt 16 (fun j =>
      Z.eqb (C1467_XORSignCocycle.sed_sign i j) (sed_sign i j))) = true)
    by (vm_compute; reflexivity).
  apply Z.eqb_eq.
  exact (all_lt2 16 (fun i j =>
    Z.eqb (C1467_XORSignCocycle.sed_sign i j) (sed_sign i j)) H i j Hi Hj).
Qed.

Lemma sign_to_R_IZR :
  forall a l, a < 16 -> l < 16 -> sign_to_R (sed_sign a l) = IZR (sed_sign a l).
Proof.
  intros a l Ha Hl.
  assert (H : all_lt 16 (fun a => all_lt 16 (fun l =>
      Z.eqb (sed_sign a l) 1 || Z.eqb (sed_sign a l) (-1))) = true)
    by (vm_compute; reflexivity).
  pose proof (all_lt2 16 (fun a l =>
    Z.eqb (sed_sign a l) 1 || Z.eqb (sed_sign a l) (-1)) H a l Ha Hl) as H1.
  apply orb_true_iff in H1. apply or_comm in H1.
  destruct H1 as [H1 | H1]; apply Z.eqb_eq in H1; rewrite H1;
    unfold sign_to_R; simpl; lra.
Qed.

(** ** Coordinates of a sedenion *)

Definition coord (x : CDSed) (j : nat) : R :=
  match j with
  | 0 => qa (oct_lo (sed_lo x))
  | 1 => qb (oct_lo (sed_lo x))
  | 2 => qc (oct_lo (sed_lo x))
  | 3 => qd (oct_lo (sed_lo x))
  | 4 => qa (oct_hi (sed_lo x))
  | 5 => qb (oct_hi (sed_lo x))
  | 6 => qc (oct_hi (sed_lo x))
  | 7 => qd (oct_hi (sed_lo x))
  | 8 => qa (oct_lo (sed_hi x))
  | 9 => qb (oct_lo (sed_hi x))
  | 10 => qc (oct_lo (sed_hi x))
  | 11 => qd (oct_lo (sed_hi x))
  | 12 => qa (oct_hi (sed_hi x))
  | 13 => qb (oct_hi (sed_hi x))
  | 14 => qc (oct_hi (sed_hi x))
  | 15 => qd (oct_hi (sed_hi x))
  | _ => 0%R
  end.

Definition sed_of_vec (v : nat -> R) : CDSed :=
  mkSed
    (mkOct (mkQuat (v 0) (v 1) (v 2) (v 3)) (mkQuat (v 4) (v 5) (v 6) (v 7)))
    (mkOct (mkQuat (v 8) (v 9) (v 10) (v 11))
           (mkQuat (v 12) (v 13) (v 14) (v 15))).

Ltac dsed x :=
  destruct x as [[[?a ?b ?c ?d] [?e ?f ?g ?h]] [[?i ?j ?k ?l] [?m ?n ?o ?p]]].

Lemma coord_of_vec :
  forall v j, j < 16 -> coord (sed_of_vec v) j = v j.
Proof.
  intros v j Hj.
  do 16 (destruct j as [|j]; [reflexivity |]). lia.
Qed.

Lemma sed_of_coord : forall x, sed_of_vec (coord x) = x.
Proof. intros x. dsed x. reflexivity. Qed.

Lemma sed_of_vec_ext :
  forall v w, (forall j, j < 16 -> v j = w j) -> sed_of_vec v = sed_of_vec w.
Proof.
  intros v w H. unfold sed_of_vec.
  repeat (f_equal; try (apply H; lia)).
Qed.

Lemma sed_ext :
  forall x y, (forall j, j < 16 -> coord x j = coord y j) -> x = y.
Proof.
  intros x y H.
  rewrite <- (sed_of_coord x), <- (sed_of_coord y).
  apply sed_of_vec_ext. exact H.
Qed.

Lemma coord_zero : forall j, coord sed_zero j = 0%R.
Proof. intros j. do 16 (destruct j as [|j]; [reflexivity |]). reflexivity. Qed.

Lemma coord_add :
  forall x y j, coord (sed_add x y) j = (coord x j + coord y j)%R.
Proof.
  intros x y j. dsed x. destruct y as [[[?a' ?b' ?c' ?d'] [?e' ?f' ?g' ?h']]
                                       [[?i' ?j' ?k' ?l'] [?m' ?n' ?o' ?p']]].
  do 16 (destruct j as [|j]; [reflexivity |]).
  simpl. ring.
Qed.

Lemma coord_scale :
  forall r x j, coord (sed_scale r x) j = (r * coord x j)%R.
Proof.
  intros r x j. dsed x.
  do 16 (destruct j as [|j]; [reflexivity |]).
  simpl. ring.
Qed.

Lemma coord_sed_e :
  forall i j, i < 16 -> j < 16 ->
    coord (sed_e i) j = if Nat.eqb i j then 1%R else 0%R.
Proof.
  intros i j Hi Hj.
  do 16 (destruct i as [|i];
         [ do 16 (destruct j as [|j]; [reflexivity |]); exfalso; lia | ]).
  exfalso; lia.
Qed.

Fixpoint sed_sum (n : nat) (f : nat -> CDSed) : CDSed :=
  match n with
  | O => sed_zero
  | S m => sed_add (sed_sum m f) (f m)
  end.

Lemma coord_sum :
  forall n f j, coord (sed_sum n f) j = sum_to n (fun l => coord (f l) j).
Proof.
  induction n as [|m IH]; intros f j; simpl; [apply coord_zero |].
  rewrite coord_add, IH. reflexivity.
Qed.

Lemma coord_mul_zero : forall x j, coord (sed_mul x sed_zero) j = 0%R.
Proof.
  intros x j. dsed x.
  do 16 (destruct j as [|j]; [simpl; ring |]).
  reflexivity.
Qed.

Lemma coord_mul_sum :
  forall x n f j,
    coord (sed_mul x (sed_sum n f)) j =
    sum_to n (fun l => coord (sed_mul x (f l)) j).
Proof.
  intros x n f j. induction n as [|m IH]; simpl; [apply coord_mul_zero |].
  rewrite sed_mul_add_right, coord_add, IH. reflexivity.
Qed.

Lemma sed_of_vec_sum :
  forall v, sed_of_vec v = sed_sum 16 (fun l => sed_scale (v l) (sed_e l)).
Proof.
  intros v. apply sed_ext. intros j Hj.
  rewrite coord_of_vec by exact Hj.
  rewrite coord_sum.
  rewrite (sum_to_single 16 j).
  - rewrite coord_scale, coord_sed_e by assumption.
    rewrite Nat.eqb_refl. ring.
  - exact Hj.
  - intros l Hl Hlj.
    rewrite coord_scale, coord_sed_e by assumption.
    destruct (Nat.eqb_spec l j) as [E | E]; [contradiction | ring].
Qed.

(** ** The eight left multiplications as sixteen-by-sixteen matrices *)

(** Column l of [Gmat a] is the coordinate vector of e_a * e_l, which holds
    the sign sigma(a, l) in row a XOR l. *)
Definition Gmat (a : nat) : mat :=
  fun j l => if Nat.eqb j (Nat.lxor a l) then IZR (sed_sign a l) else 0%R.

Definition Idmat : mat := fun i j => if Nat.eqb i j then 1%R else 0%R.

Theorem Gmat_is_left_mult_on_basis :
  forall a l j, a < 16 -> l < 16 -> j < 16 ->
    coord (sed_mul (sed_e a) (sed_e l)) j = Gmat a j l.
Proof.
  intros a l j Ha Hl Hj.
  rewrite <- sed_mul_fused_eq, sed_mul_fused_basis_xor by assumption.
  rewrite coord_scale, coord_sed_e by (try assumption; apply xor_lt16; assumption).
  unfold Gmat. rewrite sign_to_R_IZR by assumption.
  destruct (Nat.eqb_spec (Nat.lxor a l) j) as [E | E];
    destruct (Nat.eqb_spec j (Nat.lxor a l)) as [E' | E']; try lra; congruence.
Qed.

(** Item 5: under the identification of R^16 with the sedenions by
    [coord] and [sed_of_vec], left multiplication by e_a is [Gmat a]. *)
Theorem Gmat_is_left_mult :
  forall a v j, a < 16 -> j < 16 ->
    coord (sed_mul (sed_e a) (sed_of_vec v)) j =
    sum_to 16 (fun l => (Gmat a j l * v l)%R).
Proof.
  intros a v j Ha Hj.
  rewrite sed_of_vec_sum, coord_mul_sum.
  apply sum_to_ext. intros l Hl.
  rewrite sed_mul_scale_right, coord_scale,
    Gmat_is_left_mult_on_basis by assumption.
  ring.
Qed.

(** ** Signed XOR-translation matrices: a computable form *)

(** A pair [(x, s)] stands for the matrix with the entry [s r] (an integer)
    at row r, column x XOR r, and 0 elsewhere. *)
Definition sv : Type := (nat * list Z)%type.

Definition sv_ent (A : sv) (r : nat) : Z := nth r (snd A) 0%Z.

Definition sv_mat (A : sv) : mat :=
  fun r c => if Nat.eqb c (Nat.lxor (fst A) r) then IZR (sv_ent A r) else 0%R.

Definition sv_wf (A : sv) : Prop := fst A < 16 /\ length (snd A) = 16.

Definition sv_mul (A B : sv) : sv :=
  (Nat.lxor (fst A) (fst B),
   map (fun r => (sv_ent A r * sv_ent B (Nat.lxor (fst A) r))%Z) (seq 0 16)).

Definition sv_id : sv := (0, map (fun _ => 1%Z) (seq 0 16)).

Definition sv_neg (A : sv) : sv := (fst A, map Z.opp (snd A)).

Definition Gsv (a : nat) : sv :=
  (a, map (fun r => sed_sign a (Nat.lxor a r)) (seq 0 16)).

Lemma sv_ent_mul :
  forall A B r, r < 16 ->
    sv_ent (sv_mul A B) r = (sv_ent A r * sv_ent B (Nat.lxor (fst A) r))%Z.
Proof.
  intros A B r Hr. unfold sv_ent at 1. unfold sv_mul. cbn [snd].
  apply nth_map_seq. exact Hr.
Qed.

Lemma sv_ent_id : forall r, r < 16 -> sv_ent sv_id r = 1%Z.
Proof.
  intros r Hr. unfold sv_ent, sv_id. cbn [snd].
  apply (nth_map_seq (fun _ => 1%Z)). exact Hr.
Qed.

Lemma sv_ent_neg : forall A r, sv_ent (sv_neg A) r = (- sv_ent A r)%Z.
Proof.
  intros A r. unfold sv_ent, sv_neg. cbn [snd].
  exact (map_nth Z.opp (snd A) 0%Z r).
Qed.

Lemma sv_ent_G :
  forall a r, r < 16 -> sv_ent (Gsv a) r = sed_sign a (Nat.lxor a r).
Proof.
  intros a r Hr. unfold sv_ent, Gsv. cbn [snd].
  apply (nth_map_seq (fun r => sed_sign a (Nat.lxor a r))). exact Hr.
Qed.

Lemma sv_wf_mul : forall A B, sv_wf A -> sv_wf B -> sv_wf (sv_mul A B).
Proof.
  intros A B [HA1 HA2] [HB1 HB2]. split.
  - unfold sv_mul. cbn [fst]. apply xor_lt16; assumption.
  - unfold sv_mul. cbn [snd]. rewrite length_map, length_seq. reflexivity.
Qed.

Lemma sv_wf_id : sv_wf sv_id.
Proof.
  split; [unfold sv_id; cbn [fst]; lia |].
  unfold sv_id. cbn [snd]. rewrite length_map, length_seq. reflexivity.
Qed.

Lemma sv_wf_G : forall a, a < 16 -> sv_wf (Gsv a).
Proof.
  intros a Ha. split; [unfold Gsv; cbn [fst]; exact Ha |].
  unfold Gsv. cbn [snd]. rewrite length_map, length_seq. reflexivity.
Qed.

Lemma sv_mat_mul :
  forall A B, sv_wf A -> sv_wf B ->
    forall r k, r < 16 -> k < 16 ->
      mmul 16 (sv_mat A) (sv_mat B) r k = sv_mat (sv_mul A B) r k.
Proof.
  intros A B [HA1 HA2] [HB1 HB2] r k Hr Hk.
  assert (Hp : Nat.lxor (fst A) r < 16) by (apply xor_lt16; assumption).
  unfold mmul. cbv beta.
  rewrite (sum_to_single 16 (Nat.lxor (fst A) r)).
  - unfold sv_mat at 1 2 3. cbv beta.
    rewrite Nat.eqb_refl, sv_ent_mul by exact Hr.
    simpl fst.
    rewrite (xor_shift (fst A) (fst B) r) by assumption.
    destruct (Nat.eqb k (Nat.lxor (fst B) (Nat.lxor (fst A) r))).
    + rewrite mult_IZR. reflexivity.
    + ring.
  - exact Hp.
  - intros l Hl Hlp. unfold sv_mat at 1. cbv beta.
    destruct (Nat.eqb_spec l (Nat.lxor (fst A) r)) as [E | E];
      [contradiction | ring].
Qed.

Lemma sv_mat_id : forall r c, r < 16 -> sv_mat sv_id r c = Idmat r c.
Proof.
  intros r c Hr. unfold sv_mat, Idmat. simpl fst.
  rewrite Nat.lxor_0_l, sv_ent_id by exact Hr.
  rewrite Nat.eqb_sym. reflexivity.
Qed.

Lemma sv_mat_neg : forall A r c, sv_mat (sv_neg A) r c = (- sv_mat A r c)%R.
Proof.
  intros A r c. unfold sv_mat. simpl fst.
  destruct (Nat.eqb c (Nat.lxor (fst A) r));
    [rewrite sv_ent_neg, opp_IZR; reflexivity | ring].
Qed.

Lemma Gmat_sv : forall a, a < 16 -> mat_eq 16 (Gmat a) (sv_mat (Gsv a)).
Proof.
  intros a Ha j l Hj Hl.
  unfold Gmat, sv_mat. simpl fst.
  rewrite (xor_sym a j l) by assumption.
  rewrite sv_ent_G by exact Hj.
  destruct (Nat.eqb_spec l (Nat.lxor a j)) as [E | E]; [| reflexivity].
  rewrite E. reflexivity.
Qed.

Lemma mmul_congr :
  forall A A' B B', mat_eq 16 A A' -> mat_eq 16 B B' ->
    mat_eq 16 (mmul 16 A B) (mmul 16 A' B').
Proof.
  intros A A' B B' HA HB r k Hr Hk. unfold mmul.
  apply sum_to_ext. intros l Hl.
  rewrite (HA r l Hr Hl), (HB l k Hl Hk). reflexivity.
Qed.

(** ** The Clifford relations *)

Definition idx8 : list nat := seq 1 8.

Lemma sv_square_all :
  Forall (fun a => sv_mul (Gsv a) (Gsv a) = sv_neg sv_id) idx8.
Proof.
  unfold idx8. simpl. repeat constructor; vm_compute; reflexivity.
Qed.

Lemma sv_anticomm_all :
  Forall (fun a => Forall (fun b => a <> b ->
    sv_mul (Gsv a) (Gsv b) = sv_neg (sv_mul (Gsv b) (Gsv a))) idx8) idx8.
Proof.
  unfold idx8. simpl. repeat constructor;
    first [ (intros _; vm_compute; reflexivity)
          | (intros H; exfalso; apply H; reflexivity) ].
Qed.

Lemma in_idx8 : forall a, 1 <= a -> a <= 8 -> In a idx8.
Proof. intros a H1 H2. unfold idx8. apply in_seq. lia. Qed.

Theorem Gmat_square :
  forall a, 1 <= a -> a <= 8 ->
    mat_eq 16 (mmul 16 (Gmat a) (Gmat a)) (fun i j => (- Idmat i j)%R).
Proof.
  intros a H1 H2 r k Hr Hk.
  assert (Ha : a < 16) by lia.
  pose proof (proj1 (Forall_forall _ _) sv_square_all a (in_idx8 a H1 H2)) as E.
  cbv beta in E.
  transitivity (mmul 16 (sv_mat (Gsv a)) (sv_mat (Gsv a)) r k).
  - exact (mmul_congr _ _ _ _ (Gmat_sv a Ha) (Gmat_sv a Ha) r k Hr Hk).
  - rewrite sv_mat_mul by (try apply sv_wf_G; assumption).
    rewrite E, sv_mat_neg, sv_mat_id by exact Hr. reflexivity.
Qed.

Theorem Gmat_anticommute :
  forall a b, 1 <= a -> a <= 8 -> 1 <= b -> b <= 8 -> a <> b ->
    mat_eq 16 (fun i j => (mmul 16 (Gmat a) (Gmat b) i j
                           + mmul 16 (Gmat b) (Gmat a) i j)%R)
              (fun _ _ => 0%R).
Proof.
  intros a b Ha1 Ha2 Hb1 Hb2 Hab r k Hr Hk.
  assert (Ha : a < 16) by lia. assert (Hb : b < 16) by lia.
  pose proof (proj1 (Forall_forall _ _) sv_anticomm_all a (in_idx8 a Ha1 Ha2)) as E.
  cbv beta in E.
  pose proof (proj1 (Forall_forall _ _) E b (in_idx8 b Hb1 Hb2)) as E2.
  cbv beta in E2. specialize (E2 Hab).
  cbv beta.
  rewrite (mmul_congr _ _ _ _ (Gmat_sv a Ha) (Gmat_sv b Hb) r k Hr Hk).
  rewrite (mmul_congr _ _ _ _ (Gmat_sv b Hb) (Gmat_sv a Ha) r k Hr Hk).
  rewrite !sv_mat_mul by (try apply sv_wf_G; assumption).
  rewrite E2, sv_mat_neg. ring.
Qed.

(** ** The 256 ordered monomials *)

(** Bit a - 1 of the index m records whether a belongs to the subset S;
    [subset m] lists S in increasing order. *)
Definition subset (m : nat) : list nat :=
  filter (fun a => Nat.testbit m (a - 1)) idx8.

Definition mono_mat (l : list nat) : mat :=
  fold_right (fun a acc => mmul 16 (Gmat a) acc) Idmat l.

Definition mono_sv (l : list nat) : sv :=
  fold_right (fun a acc => sv_mul (Gsv a) acc) sv_id l.

(** G_S as a real matrix, the product of the G_a for a in S in increasing
    order, and G_empty = I. *)
Definition Gm (m : nat) : mat := mono_mat (subset m).

Definition msv (m : nat) : sv := mono_sv (subset m).

Lemma subset_in_idx8 : forall m a, In a (subset m) -> 1 <= a /\ a <= 8.
Proof.
  intros m a H. unfold subset in H. apply filter_In in H as [H _].
  unfold idx8 in H. apply in_seq in H. lia.
Qed.

Lemma mono_sv_wf :
  forall l, (forall a, In a l -> a < 16) -> sv_wf (mono_sv l).
Proof.
  induction l as [|a l IH]; intros H; simpl.
  - exact sv_wf_id.
  - apply sv_wf_mul.
    + apply sv_wf_G. apply H. left. reflexivity.
    + apply IH. intros b Hb. apply H. right. exact Hb.
Qed.

Lemma mono_mat_eq :
  forall l, (forall a, In a l -> a < 16) ->
    mat_eq 16 (mono_mat l) (sv_mat (mono_sv l)).
Proof.
  induction l as [|a l IH]; intros H.
  - intros r k Hr Hk. simpl. rewrite sv_mat_id by exact Hr. reflexivity.
  - assert (Ha : a < 16) by (apply H; left; reflexivity).
    assert (Hl : forall b, In b l -> b < 16) by (intros b Hb; apply H; right; exact Hb).
    intros r k Hr Hk. simpl.
    transitivity (mmul 16 (sv_mat (Gsv a)) (sv_mat (mono_sv l)) r k).
    + exact (mmul_congr _ _ _ _ (Gmat_sv a Ha) (IH Hl) r k Hr Hk).
    + apply sv_mat_mul; [apply sv_wf_G; exact Ha | apply mono_sv_wf; exact Hl | exact Hr | exact Hk].
Qed.

Lemma msv_wf : forall m, sv_wf (msv m).
Proof.
  intros m. apply mono_sv_wf. intros a Ha.
  apply subset_in_idx8 in Ha. lia.
Qed.

Lemma Gm_sv : forall m, mat_eq 16 (Gm m) (sv_mat (msv m)).
Proof.
  intros m. apply mono_mat_eq. intros a Ha.
  apply subset_in_idx8 in Ha. lia.
Qed.

(** ** The trace form on the monomials *)

Definition mtrans (A : mat) : mat := fun i j => A j i.
Definition mtrace (A : mat) : R := sum_to 16 (fun i => A i i).
Definition frob (A B : mat) : R :=
  sum_to 16 (fun r => sum_to 16 (fun c => (A r c * B r c)%R)).

Lemma trace_frob : forall A B, mtrace (mmul 16 (mtrans A) B) = frob A B.
Proof.
  intros A B. unfold mtrace, frob, mmul, mtrans. cbv beta.
  apply sum_to_swap.
Qed.

Lemma frob_ext :
  forall A A' B B', mat_eq 16 A A' -> mat_eq 16 B B' -> frob A B = frob A' B'.
Proof.
  intros A A' B B' HA HB. unfold frob.
  apply sum_to_ext. intros r Hr. apply sum_to_ext. intros c Hc.
  rewrite (HA r c Hr Hc), (HB r c Hr Hc). reflexivity.
Qed.

Definition fz (A B : sv) : Z :=
  if Nat.eqb (fst A) (fst B)
  then zsum_to 16 (fun r => (sv_ent A r * sv_ent B r)%Z) else 0%Z.

Lemma frob_sv :
  forall A B, sv_wf A -> sv_wf B -> frob (sv_mat A) (sv_mat B) = IZR (fz A B).
Proof.
  intros A B [HA1 HA2] [HB1 HB2]. unfold frob.
  transitivity (sum_to 16 (fun r =>
    if Nat.eqb (fst A) (fst B) then IZR (sv_ent A r * sv_ent B r)%Z else 0%R)).
  - apply sum_to_ext. intros r Hr.
    assert (Hp : Nat.lxor (fst A) r < 16) by (apply xor_lt16; assumption).
    rewrite (sum_to_single 16 (Nat.lxor (fst A) r)).
    + unfold sv_mat at 1 2. cbv beta.
      rewrite Nat.eqb_refl.
      rewrite (xor_cancel (fst A) (fst B) r) by assumption.
      destruct (Nat.eqb (fst A) (fst B)); [rewrite mult_IZR; reflexivity | ring].
    + exact Hp.
    + intros l Hl Hlp. unfold sv_mat at 1. cbv beta.
      destruct (Nat.eqb_spec l (Nat.lxor (fst A) r)) as [E | E];
        [contradiction | ring].
  - unfold fz. destruct (Nat.eqb (fst A) (fst B)).
    + apply sum_to_IZR.
    + apply sum_to_zero. intros; reflexivity.
Qed.

Definition tabm : list (nat * sv) := map (fun m => (m, msv m)) (seq 0 256).

Lemma in_tabm : forall m, m < 256 -> In (m, msv m) tabm.
Proof.
  intros m Hm. unfold tabm. apply in_map_iff. exists m.
  split; [reflexivity | apply in_seq; lia].
Qed.

(** Evaluation: all 65536 pairs of monomials. *)
Definition gram_ok : bool :=
  forallb (fun p => forallb (fun q =>
    Z.eqb (fz (snd p) (snd q)) (if Nat.eqb (fst p) (fst q) then 16%Z else 0%Z))
    tabm) tabm.

Lemma gram_check : gram_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma gram_spec :
  forall S T, S < 256 -> T < 256 ->
    fz (msv S) (msv T) = if Nat.eqb S T then 16%Z else 0%Z.
Proof.
  intros S T HS HT. pose proof gram_check as H. unfold gram_ok in H.
  rewrite forallb_forall in H. specialize (H _ (in_tabm S HS)).
  rewrite forallb_forall in H. specialize (H _ (in_tabm T HT)).
  apply Z.eqb_eq in H. exact H.
Qed.

Lemma frob_Gm :
  forall S T, S < 256 -> T < 256 ->
    frob (Gm S) (Gm T) = IZR (if Nat.eqb S T then 16%Z else 0%Z).
Proof.
  intros S T HS HT.
  rewrite (frob_ext _ _ _ _ (Gm_sv S) (Gm_sv T)).
  rewrite frob_sv by apply msv_wf.
  rewrite gram_spec by assumption. reflexivity.
Qed.

(** Item 3, orthogonality: trace(G_S^T G_T) = 16 if S = T and 0 otherwise. *)
Theorem C1463_trace_orthogonality :
  forall S T, S < 256 -> T < 256 ->
    mtrace (mmul 16 (mtrans (Gm S)) (Gm T)) = if Nat.eqb S T then 16%R else 0%R.
Proof.
  intros S T HS HT. rewrite trace_frob, frob_Gm by assumption.
  destruct (Nat.eqb S T); [| reflexivity].
  replace (IZR 16%Z) with 16%R by (simpl; lra). reflexivity.
Qed.

(** Item 3, independence: a real combination of the 256 monomials that
    vanishes has all coefficients zero. *)
Theorem C1463_monomials_independent :
  forall c : nat -> R,
    mat_eq 16 (fun r k => sum_to 256 (fun m => (c m * Gm m r k)%R))
              (fun _ _ => 0%R) ->
    forall T, T < 256 -> c T = 0%R.
Proof.
  intros c H T HT.
  assert (E : frob (fun r k => sum_to 256 (fun m => (c m * Gm m r k)%R)) (Gm T)
              = frob (fun _ _ => 0%R) (Gm T)).
  { apply frob_ext; [exact H | intros r k Hr Hk; reflexivity]. }
  assert (E0 : frob (fun _ _ => 0%R) (Gm T) = 0%R).
  { unfold frob. apply sum_to_zero. intros r Hr. cbv beta.
    apply sum_to_zero. intros k Hk. cbv beta. ring. }
  assert (E1 : frob (fun r k => sum_to 256 (fun m => (c m * Gm m r k)%R)) (Gm T)
               = sum_to 256 (fun m => (c m * frob (Gm m) (Gm T))%R)).
  { unfold frob.
    transitivity (sum_to 16 (fun r => sum_to 16 (fun k =>
      sum_to 256 (fun m => (c m * (Gm m r k * Gm T r k))%R)))).
    - apply sum_to_ext. intros r Hr. apply sum_to_ext. intros k Hk. cbv beta.
      rewrite sum_to_mul_r.
      apply sum_to_ext. intros m Hm. cbv beta. ring.
    - transitivity (sum_to 16 (fun r => sum_to 256 (fun m =>
        sum_to 16 (fun k => (c m * (Gm m r k * Gm T r k))%R)))).
      + apply sum_to_ext. intros r Hr. apply sum_to_swap.
      + rewrite sum_to_swap. apply sum_to_ext. intros m Hm. cbv beta.
        rewrite <- sum_to_scale. apply sum_to_ext. intros r Hr. cbv beta.
        rewrite <- sum_to_scale. reflexivity. }
  rewrite E0 in E. rewrite E1 in E.
  rewrite (sum_to_single 256 T) in E.
  - rewrite frob_Gm in E by assumption.
    rewrite Nat.eqb_refl in E.
    replace (IZR 16%Z) with 16%R in E by (simpl; lra).
    lra.
  - exact HT.
  - intros m Hm Hmt. rewrite frob_Gm by assumption.
    destruct (Nat.eqb_spec m T) as [Hc | Hc]; [contradiction |].
    simpl. ring.
Qed.

(** ** Item 4: the monomials span M(16, R) *)

Lemma zsum_to_ext :
  forall n f g, (forall l, l < n -> f l = g l) -> zsum_to n f = zsum_to n g.
Proof.
  induction n as [|m IH]; intros f g H; simpl; [reflexivity |].
  rewrite (IH f g) by (intros l Hl; apply H; lia).
  rewrite (H m) by lia. reflexivity.
Qed.

Lemma seq_fold :
  forall n (f : nat -> Z) z,
    fold_right (fun m acc => (f m + acc)%Z) z (seq 0 n) = (z + zsum_to n f)%Z.
Proof.
  induction n as [|n IH]; intros f z; [simpl; lia |].
  rewrite seq_S, fold_right_app. cbn [fold_right zsum_to].
  rewrite IH. change (0 + n) with n. lia.
Qed.

Definition tab_sum (F : sv -> Z) : Z :=
  fold_right (fun p acc => (F (snd p) + acc)%Z) 0%Z tabm.

Lemma tab_sum_eq :
  forall F, tab_sum F = zsum_to 256 (fun m => F (msv m)).
Proof.
  intros F. unfold tab_sum, tabm.
  transitivity (fold_right (fun m acc => (F (msv m) + acc)%Z) 0%Z (seq 0 256)).
  - generalize (seq 0 256) as l. induction l as [|m l IH]; [reflexivity |].
    simpl. rewrite IH. reflexivity.
  - rewrite seq_fold. lia.
Qed.

Definition ent (A : sv) (i j : nat) : Z :=
  if Nat.eqb j (Nat.lxor (fst A) i) then sv_ent A i else 0%Z.

Lemma sv_mat_ent : forall A r c, sv_mat A r c = IZR (ent A r c).
Proof.
  intros A r c. unfold sv_mat, ent.
  destruct (Nat.eqb c (Nat.lxor (fst A) r)); reflexivity.
Qed.

Definition cls_term (x i r : nat) (A : sv) : Z :=
  if Nat.eqb (fst A) x then (sv_ent A i * sv_ent A r)%Z else 0%Z.

(** Evaluation: for each translation class x and rows i, r, the 16
    monomials of class x have sign vectors with inner product 16 [i = r]. *)
Definition comp_ok : bool :=
  all_lt 16 (fun x => all_lt 16 (fun i => all_lt 16 (fun r =>
    Z.eqb (tab_sum (cls_term x i r)) (if Nat.eqb i r then 16%Z else 0%Z)))).

Lemma comp_check : comp_ok = true.
Proof. vm_compute. reflexivity. Qed.

Lemma comp_class :
  forall x i r, x < 16 -> i < 16 -> r < 16 ->
    tab_sum (cls_term x i r) = if Nat.eqb i r then 16%Z else 0%Z.
Proof.
  intros x i r Hx Hi Hr. pose proof comp_check as H. unfold comp_ok in H.
  apply Z.eqb_eq.
  exact (all_lt3 16 (fun x i r =>
    Z.eqb (tab_sum (cls_term x i r)) (if Nat.eqb i r then 16%Z else 0%Z)) H x i r Hx Hi Hr).
Qed.

Lemma comp_spec :
  forall i j r k, i < 16 -> j < 16 -> r < 16 -> k < 16 ->
    zsum_to 256 (fun m => (ent (msv m) i j * ent (msv m) r k)%Z) =
    if (Nat.eqb i r && Nat.eqb j k)%bool then 16%Z else 0%Z.
Proof.
  intros i j r k Hi Hj Hr Hk.
  destruct (Nat.eqb_spec (Nat.lxor i j) (Nat.lxor r k)) as [Hx | Hx].
  - transitivity (zsum_to 256 (fun m => cls_term (Nat.lxor i j) i r (msv m))).
    + apply zsum_to_ext. intros m Hm.
      destruct (msv_wf m) as [Ha _]. unfold ent, cls_term.
      rewrite (xor_iff (fst (msv m)) i j Ha Hi Hj),
              (xor_iff (fst (msv m)) r k Ha Hr Hk), <- Hx.
      destruct (Nat.eqb (fst (msv m)) (Nat.lxor i j)); lia.
    + rewrite <- tab_sum_eq.
      rewrite comp_class by (try assumption; apply xor_lt16; assumption).
      destruct (Nat.eqb_spec i r) as [E | E].
      * subst r.
        assert (Hjk : Nat.eqb j k = true).
        { rewrite <- (xor_cancel j k i) by assumption.
          rewrite (Nat.lxor_comm j i), (Nat.lxor_comm k i).
          apply Nat.eqb_eq. exact Hx. }
        rewrite Hjk. reflexivity.
      * destruct (Nat.eqb_spec i r); [contradiction | reflexivity].
  - transitivity 0%Z.
    + apply zsum_to_zero. intros m Hm.
      destruct (msv_wf m) as [Ha _]. unfold ent.
      rewrite (xor_iff (fst (msv m)) i j Ha Hi Hj),
              (xor_iff (fst (msv m)) r k Ha Hr Hk).
      destruct (Nat.eqb (fst (msv m)) (Nat.lxor i j)) eqn:E1;
        destruct (Nat.eqb (fst (msv m)) (Nat.lxor r k)) eqn:E2;
        try (simpl; lia).
      exfalso. apply Hx.
      apply Nat.eqb_eq in E1. apply Nat.eqb_eq in E2.
      rewrite <- E1, <- E2. reflexivity.
    + destruct (Nat.eqb i r) eqn:A; destruct (Nat.eqb j k) eqn:B;
        simpl; try reflexivity.
      apply Nat.eqb_eq in A. apply Nat.eqb_eq in B. subst.
      exfalso. apply Hx. reflexivity.
Qed.

(** The matrix unit E_ij is the combination of the monomials with
    coefficients (G_S)_ij / 16. *)
Theorem C1463_matrix_unit_in_span :
  forall i j, i < 16 -> j < 16 ->
    mat_eq 16
      (fun r k => if (Nat.eqb i r && Nat.eqb j k)%bool then 1%R else 0%R)
      (fun r k => sum_to 256 (fun m => (Gm m i j / 16 * Gm m r k)%R)).
Proof.
  intros i j Hi Hj r k Hr Hk. cbv beta.
  transitivity (sum_to 256 (fun m =>
    (IZR (ent (msv m) i j) / 16 * IZR (ent (msv m) r k))%R)).
  - transitivity (/ 16 * IZR (zsum_to 256 (fun m =>
        (ent (msv m) i j * ent (msv m) r k)%Z)))%R.
    + rewrite comp_spec by assumption.
      destruct ((Nat.eqb i r && Nat.eqb j k)%bool);
        replace (IZR 16%Z) with 16%R by (simpl; lra); lra.
    + rewrite <- sum_to_IZR, <- sum_to_scale.
      apply sum_to_ext. intros m Hm. cbv beta.
      rewrite mult_IZR. field.
  - apply sum_to_ext. intros m Hm. cbv beta.
    rewrite (Gm_sv m i j Hi Hj), (Gm_sv m r k Hr Hk), !sv_mat_ent.
    reflexivity.
Qed.

Lemma div16_comm : forall a b : R, (a / 16 * b)%R = (b / 16 * a)%R.
Proof. intros a b. unfold Rdiv. ring. Qed.

Lemma frob_expand :
  forall M G c, (c * frob M G)%R =
    sum_to 16 (fun i => sum_to 16 (fun j => (c * (M i j * G i j))%R)).
Proof.
  intros M G c. unfold frob. rewrite <- sum_to_scale.
  apply sum_to_ext. intros i Hi. cbv beta.
  rewrite <- sum_to_scale. reflexivity.
Qed.

(** Surjectivity onto M(16, R): every real 16 x 16 matrix M equals the
    combination of the monomials with coefficients trace(M^T G_S) / 16. *)
Theorem C1463_monomials_span :
  forall M : mat,
    mat_eq 16 M
      (fun r k => sum_to 256 (fun m => (frob M (Gm m) / 16 * Gm m r k)%R)).
Proof.
  intros M r k Hr Hk. cbv beta.
  transitivity (sum_to 256 (fun m => sum_to 16 (fun i => sum_to 16 (fun j =>
      (M i j * (Gm m i j / 16 * Gm m r k))%R)))).
  2: { apply sum_to_ext. intros m Hm. cbv beta.
       rewrite (div16_comm (frob M (Gm m)) (Gm m r k)), frob_expand.
       apply sum_to_ext. intros i Hi. cbv beta.
       apply sum_to_ext. intros j Hj. cbv beta. unfold Rdiv. ring. }
  rewrite sum_to_swap.
  transitivity (sum_to 16 (fun i => sum_to 16 (fun j =>
      (M i j * (if (Nat.eqb i r && Nat.eqb j k)%bool then 1%R else 0%R))%R))).
  - rewrite (sum_to_single 16 r).
    + rewrite (sum_to_single 16 k).
      * rewrite !Nat.eqb_refl. simpl. ring.
      * exact Hk.
      * intros l Hl Hlk. destruct (Nat.eqb_spec l k) as [E | E]; [contradiction |].
        cbv beta. rewrite Nat.eqb_refl. simpl. ring.
    + exact Hr.
    + intros l Hl Hlr. destruct (Nat.eqb_spec l r) as [E | E]; [contradiction |].
      cbv beta. simpl. ring.
  - apply sum_to_ext. intros i Hi. cbv beta.
    rewrite sum_to_swap.
    apply sum_to_ext. intros j Hj. cbv beta.
    rewrite (C1463_matrix_unit_in_span i j Hi Hj r k Hr Hk). cbv beta.
    rewrite <- sum_to_scale. reflexivity.
Qed.

(** ** Item 5: the column ideal and the sedenions *)

(** The column ideal [col_space 16 0] holds the matrices whose entries lie
    in column 0; [col_embed v] is the one with column 0 equal to [v], and
    reading column 0 inverts it.  The sedenions are read from the column by
    [sed_of_vec] and [coord], which are mutually inverse. *)
Definition col_embed (v : nat -> R) : mat :=
  fun r c => if Nat.eqb c 0 then v r else 0%R.

Lemma col_embed_in : forall v, col_space 16 0 (col_embed v).
Proof.
  intros v i k Hi Hk Hk0. unfold col_embed.
  destruct (Nat.eqb_spec k 0); [contradiction | reflexivity].
Qed.

Lemma col_embed_read :
  forall M, col_space 16 0 M -> mat_eq 16 M (col_embed (fun r => M r 0)).
Proof.
  intros M H r k Hr Hk. unfold col_embed.
  destruct (Nat.eqb_spec k 0) as [E | E]; [subst; reflexivity |].
  exact (H r k Hr Hk E).
Qed.

(** Left multiplication by G_a on column 0 is left multiplication by e_a on
    the sedenion that the column spells. *)
Theorem C1463_column_ideal_compat :
  forall a M, a < 16 ->
    sed_of_vec (fun r => mmul 16 (Gmat a) M r 0) =
    sed_mul (sed_e a) (sed_of_vec (fun r => M r 0)).
Proof.
  intros a M Ha. apply sed_ext. intros j Hj.
  rewrite coord_of_vec by exact Hj.
  rewrite (Gmat_is_left_mult a (fun r => M r 0) j Ha Hj).
  reflexivity.
Qed.

Lemma mmul_assoc16 :
  forall A B C, mat_eq 16 (mmul 16 (mmul 16 A B) C) (mmul 16 A (mmul 16 B C)).
Proof.
  intros A B C i k Hi Hk. unfold mmul. cbv beta.
  transitivity (sum_to 16 (fun l => sum_to 16 (fun m => (A i m * B m l * C l k)%R))).
  - apply sum_to_ext. intros l Hl. cbv beta. rewrite sum_to_mul_r.
    apply sum_to_ext. intros m Hm. cbv beta. reflexivity.
  - rewrite sum_to_swap. apply sum_to_ext. intros m Hm. cbv beta.
    rewrite <- sum_to_scale. apply sum_to_ext. intros l Hl. cbv beta. ring.
Qed.

Definition sed_lmul_list (l : list nat) (x : CDSed) : CDSed :=
  fold_right (fun a acc => sed_mul (sed_e a) acc) x l.

(** The monomial G_S, applied to a column, is the iterated left
    multiplication e_a1 (e_a2 (... x)) on the corresponding sedenion. *)
Theorem C1463_monomial_column_compat :
  forall l, (forall a, In a l -> a < 16) -> forall M,
    sed_of_vec (fun r => mmul 16 (mono_mat l) M r 0) =
    sed_lmul_list l (sed_of_vec (fun r => M r 0)).
Proof.
  induction l as [|a l IH]; intros H M.
  - simpl. apply sed_of_vec_ext. intros j Hj. unfold mmul, Idmat. cbv beta.
    rewrite (sum_to_single 16 j).
    + rewrite Nat.eqb_refl. ring.
    + exact Hj.
    + intros m Hm Hmj. destruct (Nat.eqb_spec j m); [subst; contradiction | ring].
  - assert (Ha : a < 16) by (apply H; left; reflexivity).
    assert (Hl : forall b, In b l -> b < 16) by (intros b Hb; apply H; right; exact Hb).
    simpl mono_mat. simpl sed_lmul_list.
    rewrite <- (IH Hl M).
    rewrite <- (C1463_column_ideal_compat a (mmul 16 (mono_mat l) M) Ha).
    apply sed_of_vec_ext. intros j Hj.
    exact (mmul_assoc16 (Gmat a) (mono_mat l) M j 0 Hj ltac:(lia)).
Qed.

(** ** Summary *)

(** The relations of Cl(0, 8) (squares -1) hold for G_1 .. G_8, the 256
    ordered monomials are orthogonal for the trace form and independent,
    and they span M(16, R). *)
Theorem C1463_clifford_matrix_basis :
  (forall a, 1 <= a -> a <= 8 ->
     mat_eq 16 (mmul 16 (Gmat a) (Gmat a)) (fun i j => (- Idmat i j)%R)) /\
  (forall a b, 1 <= a -> a <= 8 -> 1 <= b -> b <= 8 -> a <> b ->
     mat_eq 16 (fun i j => (mmul 16 (Gmat a) (Gmat b) i j
                            + mmul 16 (Gmat b) (Gmat a) i j)%R)
               (fun _ _ => 0%R)) /\
  (forall S T, S < 256 -> T < 256 ->
     mtrace (mmul 16 (mtrans (Gm S)) (Gm T)) = if Nat.eqb S T then 16%R else 0%R) /\
  (forall c : nat -> R,
     mat_eq 16 (fun r k => sum_to 256 (fun m => (c m * Gm m r k)%R))
               (fun _ _ => 0%R) ->
     forall T, T < 256 -> c T = 0%R) /\
  (forall M : mat,
     mat_eq 16 M
       (fun r k => sum_to 256 (fun m => (frob M (Gm m) / 16 * Gm m r k)%R))).
Proof.
  split; [exact Gmat_square |].
  split; [exact Gmat_anticommute |].
  split; [exact C1463_trace_orthogonality |].
  split; [exact C1463_monomials_independent | exact C1463_monomials_span].
Qed.

Print Assumptions Gmat_is_left_mult_on_basis.
Print Assumptions Gmat_is_left_mult.
Print Assumptions Gmat_square.
Print Assumptions Gmat_anticommute.
Print Assumptions C1463_trace_orthogonality.
Print Assumptions C1463_monomials_independent.
Print Assumptions C1463_matrix_unit_in_span.
Print Assumptions C1463_monomials_span.
Print Assumptions C1463_column_ideal_compat.
Print Assumptions C1463_monomial_column_compat.
Print Assumptions C1463_clifford_matrix_basis.
Print Assumptions sed_sign_agrees_with_C1467.
