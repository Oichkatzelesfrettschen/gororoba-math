(** The Leibniz rule of a linear map on level k of the ring tower as a homogeneous linear system.

    For a linear map F of level k over a target ring B, write x(m, q) for coordinate q of F(e_m) ([entry]). With
    structure constants e_a e_b = sum_m s(a, b, m) e_m over the source ring A ([structure], bound to the product
    of CdTowerRing.v by the hypothesis [structure_source]), coordinate c of
    F(e_a e_b) - F(e_a) e_b - e_a F(e_b) is the linear form in x with coefficients

      [coefficient a b c m q] = [q = c] s(a, b, m) - [m = a] s(q, b, c) - [m = b] s(a, q, c).

    [equation_holds] states that this form vanishes for a map that satisfies the Leibniz rule on the basis
    units, and [system_solved] the same for a list of triples (a, b, c), in the flat indexing
    j = 2^k m + q of [unknown] and [matrix] that MatrixSplittingCertificate.v reads. *)

From Stdlib Require Import Ring Lia PeanoNat List Bool.
Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange.

Module LeibnizSystem (A B : CommutativeRing) (H : RingHom A B).
Module BC := BaseChange A B H.
Import BC.

Add Ring leibniz_target : B.ring_th.

Lemma dsum_add n g g' : SB.dsum n (fun m => B.add (g m) (g' m)) = B.add (SB.dsum n g) (SB.dsum n g').
Proof. induction n as [|m IH]; cbn [SB.dsum]; [ring | rewrite IH; ring]. Qed.

Lemma dsum_opp n g : SB.dsum n (fun m => B.opp (g m)) = B.opp (SB.dsum n g).
Proof. induction n as [|m IH]; cbn [SB.dsum]; [ring | rewrite IH; ring]. Qed.

Lemma dsum_scale_right n r g : SB.dsum n (fun m => B.mul (g m) r) = B.mul (SB.dsum n g) r.
Proof. induction n as [|m IH]; cbn [SB.dsum]; [ring | rewrite IH; ring]. Qed.

Lemma dsum_app a b f : SB.dsum (a + b) f = B.add (SB.dsum a f) (SB.dsum b (fun i => f (a + i)%nat)).
Proof.
  induction b as [|b IH].
  - rewrite Nat.add_0_r. cbn [SB.dsum]. ring.
  - rewrite Nat.add_succ_r. cbn [SB.dsum]. rewrite IH. ring.
Qed.

(** A sum over a grid of M rows of N cells, read in row order. *)
Lemma dsum_grid N M (g : nat -> nat -> B.t) : (0 < N)%nat ->
  SB.dsum (M * N) (fun j => g (j / N)%nat (j mod N)%nat) = SB.dsum M (fun m => SB.dsum N (g m)).
Proof.
  intro HN. induction M as [|M IH]; [reflexivity |].
  rewrite Nat.mul_succ_l, dsum_app, IH. cbn [SB.dsum]. f_equal.
  apply SB.dsum_ext. intros q Hq.
  rewrite (Nat.add_comm (M * N) q), Nat.div_add by lia.
  rewrite Nat.Div0.mod_add, (Nat.div_small q N Hq), (Nat.mod_small q N Hq). reflexivity.
Qed.

Lemma h_if (p : bool) (s : A.t) : H.h (if p then s else A.zero) = if p then H.h s else B.zero.
Proof. destruct p; [reflexivity | apply H.h_zero]. Qed.

Section System.

Variables (k : nat) (structure : nat -> nat -> nat -> A.t).

Hypothesis structure_source : forall a b m,
  (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat -> (m < Nat.pow 2 k)%nat ->
  TA.coord k (TA.mul k (SA.basis k a) (SA.basis k b)) m = structure a b m.

Lemma structure_target a b m :
  (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat -> (m < Nat.pow 2 k)%nat ->
  TB.coord k (TB.mul k (SB.basis k a) (SB.basis k b)) m = H.h (structure a b m).
Proof.
  intros Ha Hb Hm. rewrite <- (structure_source a b m Ha Hb Hm), tmap_coord, tmap_mul, !tmap_basis.
  reflexivity.
Qed.

Definition coefficient (a b c m q : nat) : A.t :=
  A.add (A.add (if Nat.eqb q c then structure a b m else A.zero)
               (A.opp (if Nat.eqb m a then structure q b c else A.zero)))
        (A.opp (if Nat.eqb m b then structure a q c else A.zero)).

Variable F : TB.cd k -> TB.cd k.

Hypothesis F_linear : SB.linear k F.

Hypothesis F_leibniz : forall a b, (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  F (TB.mul k (SB.basis k a) (SB.basis k b)) =
  TB.add k (TB.mul k (F (SB.basis k a)) (SB.basis k b)) (TB.mul k (SB.basis k a) (F (SB.basis k b))).

(** Coordinate q of F(e_m). *)
Definition entry (m q : nat) : B.t := TB.coord k (F (SB.basis k m)) q.

Lemma image_of_product a b c : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  TB.coord k (F (TB.mul k (SB.basis k a) (SB.basis k b))) c =
  SB.dsum (Nat.pow 2 k) (fun m => B.mul (H.h (structure a b m)) (entry m c)).
Proof.
  intros Ha Hb. rewrite (SB.decompose k (TB.mul k (SB.basis k a) (SB.basis k b))).
  rewrite (SB.linear_tsum k F _ _ F_linear), SB.coord_tsum. apply SB.dsum_ext. intros m Hm.
  rewrite (proj2 F_linear), TB.coord_scale. unfold entry.
  rewrite (structure_target a b m Ha Hb Hm). reflexivity.
Qed.

Lemma product_of_image_left a b c :
  (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat -> (c < Nat.pow 2 k)%nat ->
  TB.coord k (TB.mul k (F (SB.basis k a)) (SB.basis k b)) c =
  SB.dsum (Nat.pow 2 k) (fun q => B.mul (H.h (structure q b c)) (entry a q)).
Proof.
  intros Ha Hb Hc. rewrite (SB.decompose k (F (SB.basis k a))).
  pose proof (SB.linear_tsum k (fun y => TB.mul k y (SB.basis k b)) (Nat.pow 2 k)
                (fun i => TB.scale k (TB.coord k (F (SB.basis k a)) i) (SB.basis k i))
                (proj1 (SB.mul_bilinear k) (SB.basis k b))) as E.
  cbn beta in E. rewrite E, SB.coord_tsum. apply SB.dsum_ext. intros q Hq.
  rewrite TB.mul_scale_l, TB.coord_scale, (structure_target q b c Hq Hb Hc). unfold entry. ring.
Qed.

Lemma product_of_image_right a b c :
  (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat -> (c < Nat.pow 2 k)%nat ->
  TB.coord k (TB.mul k (SB.basis k a) (F (SB.basis k b))) c =
  SB.dsum (Nat.pow 2 k) (fun q => B.mul (H.h (structure a q c)) (entry b q)).
Proof.
  intros Ha Hb Hc. rewrite (SB.decompose k (F (SB.basis k b))).
  rewrite (SB.linear_tsum k (TB.mul k (SB.basis k a)) _ _ (proj2 (SB.mul_bilinear k) (SB.basis k a))).
  rewrite SB.coord_tsum. apply SB.dsum_ext. intros q Hq.
  rewrite TB.mul_scale_r, TB.coord_scale, (structure_target a q c Ha Hq Hc). unfold entry. ring.
Qed.

(** Coordinate c of the Leibniz rule at the pair (e_a, e_b), as a linear form in the entries of F. *)
Theorem equation_holds a b c :
  (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat -> (c < Nat.pow 2 k)%nat ->
  SB.dsum (Nat.pow 2 k * Nat.pow 2 k)
    (fun j => B.mul (H.h (coefficient a b c (j / Nat.pow 2 k) (j mod Nat.pow 2 k)))
                    (entry (j / Nat.pow 2 k) (j mod Nat.pow 2 k))) = B.zero.
Proof.
  intros Ha Hb Hc.
  assert (HN : (0 < Nat.pow 2 k)%nat) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; discriminate).
  rewrite (dsum_grid (Nat.pow 2 k) (Nat.pow 2 k)
             (fun m q => B.mul (H.h (coefficient a b c m q)) (entry m q)) HN).
  pose proof (f_equal (fun w => TB.coord k w c) (F_leibniz a b Ha Hb)) as L. cbn beta in L.
  rewrite TB.coord_add, (image_of_product a b c Ha Hb), (product_of_image_left a b c Ha Hb Hc),
    (product_of_image_right a b c Ha Hb Hc) in L.
  rewrite (SB.dsum_ext (Nat.pow 2 k) _
             (fun m => B.add (B.add (B.mul (H.h (structure a b m)) (entry m c))
                (B.opp (B.mul (SB.dsum (Nat.pow 2 k) (fun q => B.mul (H.h (structure q b c)) (entry m q)))
                              (if Nat.eqb m a then B.one else B.zero))))
                (B.opp (B.mul (SB.dsum (Nat.pow 2 k) (fun q => B.mul (H.h (structure a q c)) (entry m q)))
                              (if Nat.eqb m b then B.one else B.zero))))).
  - rewrite !dsum_add, !dsum_opp, !SB.dsum_delta, (proj2 (Nat.ltb_lt _ _) Ha), (proj2 (Nat.ltb_lt _ _) Hb).
    rewrite L. ring.
  - intros m Hm.
    rewrite (SB.dsum_ext (Nat.pow 2 k) _
               (fun q => B.add (B.add
                  (B.mul (B.mul (H.h (structure a b m)) (entry m q)) (if Nat.eqb q c then B.one else B.zero))
                  (B.opp (B.mul (B.mul (H.h (structure q b c)) (entry m q))
                                (if Nat.eqb m a then B.one else B.zero))))
                  (B.opp (B.mul (B.mul (H.h (structure a q c)) (entry m q))
                                (if Nat.eqb m b then B.one else B.zero))))).
    + rewrite !dsum_add, !dsum_opp, SB.dsum_delta, (proj2 (Nat.ltb_lt _ _) Hc), !dsum_scale_right.
      reflexivity.
    + intros q Hq. unfold coefficient. rewrite !H.h_add, !H.h_opp, !h_if.
      destruct (Nat.eqb q c), (Nat.eqb m a), (Nat.eqb m b); ring.
Qed.

(** The flat indexing: unknown j = 2^k m + q is the entry (m, q), and row r of the matrix is the form of the
    r-th triple of a list. *)
Definition unknown (j : nat) : B.t := entry (j / Nat.pow 2 k) (j mod Nat.pow 2 k).

Definition matrix (equations : list (nat * nat * nat)) (r j : nat) : A.t :=
  match nth r equations (0, 0, 0)%nat with
  | (a, b, c) => coefficient a b c (j / Nat.pow 2 k) (j mod Nat.pow 2 k)
  end.

Definition in_range (equation : nat * nat * nat) : bool :=
  match equation with
  | (a, b, c) => Nat.ltb a (Nat.pow 2 k) && Nat.ltb b (Nat.pow 2 k) && Nat.ltb c (Nat.pow 2 k)
  end.

Theorem system_solved (equations : list (nat * nat * nat)) :
  forallb in_range equations = true ->
  forall r, (r < length equations)%nat ->
  SB.dsum (Nat.pow 2 k * Nat.pow 2 k) (fun j => B.mul (H.h (matrix equations r j)) (unknown j)) = B.zero.
Proof.
  intros R r Hr. unfold matrix, unknown. rewrite forallb_forall in R.
  specialize (R (nth r equations (0, 0, 0)%nat) (nth_In _ _ Hr)).
  destruct (nth r equations (0, 0, 0)%nat) as [[a b] c]. unfold in_range in R.
  apply andb_prop in R as [R Hc]. apply andb_prop in R as [Ha Hb].
  apply Nat.ltb_lt in Ha, Hb, Hc. exact (equation_holds a b c Ha Hb Hc).
Qed.

End System.

End LeibnizSystem.
