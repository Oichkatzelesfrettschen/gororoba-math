(** Basis products of the integer pair tower of CdImaginarySumConference.v.
    In the standard basis e_a, a < 2^k, the tower multiplies basis units as
    e_a e_b = sigma_k(a, b) e_(a XOR b), with sigma_k the loop of
    gororoba_quantum/cd_core.py cd_sign unrolled one doubling per level.
    Left and right multiplication by e_a are signed permutations, so the arc
    matrix of R_s, s the imaginary sum, has entry sigma_k(a, b) at row a XOR b,
    column a for b <> 0 and 0 on the diagonal. The cochain recursion of
    Albuquerque and Majid, Quasialgebra structure of the octonions,
    Corollary 4.3, gives (-1)^f(a, b) = sigma_k(b, a) at every level. *)

From Stdlib Require Import ZArith Lia Btauto.
Require Import CdImaginarySumConference.
Open Scope Z_scope.

Lemma low_bit_clear j x : (x < Nat.pow 2 j)%nat -> Nat.land x (Nat.pow 2 j) = O.
Proof.
  intro Hx. apply Nat.bits_inj_0. intro n. rewrite Nat.land_spec.
  destruct (Nat.eq_dec j n) as [<-|Hn].
  - destruct (Nat.eq_dec x 0) as [->|Hx0].
    + rewrite Nat.bits_0. reflexivity.
    + rewrite Nat.bits_above_log2; [reflexivity|]. apply Nat.log2_lt_pow2; lia.
  - rewrite Nat.pow2_bits_false by exact Hn. apply Bool.andb_false_r.
Qed.

Lemma add_high_bit j x : (x < Nat.pow 2 j)%nat -> (x + Nat.pow 2 j)%nat = Nat.lxor x (Nat.pow 2 j).
Proof. intro Hx. apply Nat.add_nocarry_lxor, low_bit_clear, Hx. Qed.

Lemma lxor_lt j x y : (x < Nat.pow 2 j)%nat -> (y < Nat.pow 2 j)%nat -> (Nat.lxor x y < Nat.pow 2 j)%nat.
Proof.
  intros Hx Hy. destruct (Nat.eq_dec (Nat.lxor x y) 0) as [->|H0].
  - apply Nat.neq_0_lt_0, Nat.pow_nonzero. lia.
  - apply Nat.log2_lt_pow2; [lia|].
    eapply Nat.le_lt_trans; [apply Nat.log2_lxor|].
    destruct j as [|j].
    + simpl in Hx, Hy. assert (x = O) as -> by lia. assert (y = O) as -> by lia. contradiction.
    + apply Nat.max_lub_lt.
      * destruct (Nat.eq_dec x 0) as [->|]; [rewrite Nat.log2_nonpos by lia; lia|]. apply Nat.log2_lt_pow2; [lia|exact Hx].
      * destruct (Nat.eq_dec y 0) as [->|]; [rewrite Nat.log2_nonpos by lia; lia|]. apply Nat.log2_lt_pow2; [lia|exact Hy].
Qed.

Fixpoint basis (k : nat) (a : nat) : cd k :=
  match k with
  | O => 1
  | S j => if Nat.ltb a (Nat.pow 2 j) then (basis j a, zero j) else (zero j, basis j (a - Nat.pow 2 j))
  end.

(** cd_core.cd_sign(2^k, p, q) unrolled one doubling per level, top bit first,
    with each branch of its loop in the same order. *)
Fixpoint sigma (k : nat) (p q : nat) : Z :=
  match k with
  | O => 1
  | S j =>
      let h := Nat.pow 2 j in
      if Nat.ltb p h then
        if Nat.ltb q h then sigma j p q else sigma j (q - h) p
      else if Nat.ltb q h then (if Nat.eqb q 0 then 1 else -1) * sigma j (p - h) q
      else if Nat.eqb (q - h) 0 then -1 else sigma j (q - h) (p - h)
  end.

(** The while loop of cd_core.cd_sign, the accumulated sign carried as an
    argument; levels counts the halvings left, half = 2^(levels - 1). *)
Fixpoint cd_sign_loop (levels : nat) (p q : nat) (sign : Z) : Z :=
  match levels with
  | O => sign
  | S j =>
      let half := Nat.pow 2 j in
      if Nat.ltb p half then
        if Nat.ltb q half then cd_sign_loop j p q sign else cd_sign_loop j (q - half) p sign
      else if Nat.ltb q half then cd_sign_loop j (p - half) q (if Nat.eqb q 0 then sign else - sign)
      else if Nat.eqb (q - half) 0 then - sign else cd_sign_loop j (q - half) (p - half) sign
  end.

Lemma cd_sign_loop_sigma k : forall p q sign, cd_sign_loop k p q sign = sign * sigma k p q.
Proof.
  induction k as [|j IH]; intros p q sign; simpl; [ring|].
  destruct (Nat.ltb p _), (Nat.ltb q _); rewrite ?IH; try ring; destruct (Nat.eqb _ 0); rewrite ?IH; ring.
Qed.

Definition unit_conj (a : nat) : Z := if Nat.eqb a 0 then 1 else -1.

Lemma conj_basis k : forall a, (a < Nat.pow 2 k)%nat -> conjugate k (basis k a) = scale k (unit_conj a) (basis k a).
Proof.
  unfold unit_conj. induction k as [|j IH]; intros a Ha; simpl in Ha |- *.
  - simpl in Ha. assert (a = O) as -> by lia. reflexivity.
  - destruct (Nat.ltb_spec a (Nat.pow 2 j)) as [Hl|Hl]; cbn [conjugate fst snd scale].
    + rewrite IH by exact Hl. rewrite !scale_zero. reflexivity.
    + rewrite conj_zero, scale_zero. replace (Nat.eqb a 0) with false by (symmetry; apply Nat.eqb_neq; pose proof (Nat.pow_nonzero 2 j); lia).
      reflexivity.
Qed.

Ltac bits := apply Nat.bits_inj; intro; rewrite ?Nat.lxor_spec; btauto.

Lemma lxor_high_r j x y : (x < Nat.pow 2 j)%nat -> (y < Nat.pow 2 j)%nat ->
  Nat.lxor x (y + Nat.pow 2 j) = (Nat.lxor y x + Nat.pow 2 j)%nat.
Proof.
  intros Hx Hy. rewrite (add_high_bit j y Hy), (add_high_bit j (Nat.lxor y x)) by (apply lxor_lt; assumption).
  bits.
Qed.

Lemma lxor_high_l j x y : (x < Nat.pow 2 j)%nat -> (y < Nat.pow 2 j)%nat ->
  Nat.lxor (x + Nat.pow 2 j) y = (Nat.lxor x y + Nat.pow 2 j)%nat.
Proof.
  intros Hx Hy. rewrite Nat.lxor_comm, (lxor_high_r j y x Hy Hx). reflexivity.
Qed.

Lemma lxor_high_lr j x y : (x < Nat.pow 2 j)%nat -> (y < Nat.pow 2 j)%nat ->
  Nat.lxor (x + Nat.pow 2 j) (y + Nat.pow 2 j) = Nat.lxor x y.
Proof.
  intros Hx Hy. rewrite (add_high_bit j x Hx), (add_high_bit j y Hy). bits.
Qed.

Lemma basis_low j c : (c < Nat.pow 2 j)%nat -> basis (S j) c = (basis j c, zero j).
Proof. intro Hc. simpl. rewrite (proj2 (Nat.ltb_lt _ _) Hc). reflexivity. Qed.

Lemma basis_high j c : (c < Nat.pow 2 j)%nat -> basis (S j) (c + Nat.pow 2 j) = (zero j, basis j c).
Proof.
  intro Hc. simpl. rewrite (proj2 (Nat.ltb_ge _ _)) by lia. rewrite Nat.add_sub. reflexivity.
Qed.

Lemma sigma_unfold j p q : sigma (S j) p q =
  if Nat.ltb p (Nat.pow 2 j) then
    if Nat.ltb q (Nat.pow 2 j) then sigma j p q else sigma j (q - Nat.pow 2 j) p
  else if Nat.ltb q (Nat.pow 2 j) then unit_conj q * sigma j (p - Nat.pow 2 j) q
  else if Nat.eqb (q - Nat.pow 2 j) 0 then -1 else sigma j (q - Nat.pow 2 j) (p - Nat.pow 2 j).
Proof. reflexivity. Qed.

Lemma sigma_zero_r k : forall p, sigma k p 0 = 1.
Proof.
  induction k as [|j IH]; intro p; rewrite ?sigma_unfold; [reflexivity|].
  pose proof (Nat.pow_nonzero 2 j ltac:(lia)).
  replace (Nat.ltb 0 (Nat.pow 2 j)) with true by (symmetry; apply Nat.ltb_lt; lia).
  destruct (Nat.ltb p (Nat.pow 2 j)); rewrite IH; reflexivity.
Qed.

Lemma sigma_zero_l k : forall q, sigma k 0 q = 1.
Proof.
  induction k as [|j IH]; intro q; rewrite ?sigma_unfold; [reflexivity|].
  pose proof (Nat.pow_nonzero 2 j ltac:(lia)).
  replace (Nat.ltb 0 (Nat.pow 2 j)) with true by (symmetry; apply Nat.ltb_lt; lia).
  destruct (Nat.ltb q (Nat.pow 2 j)); [apply IH|apply sigma_zero_r].
Qed.

Lemma split_high j a : (a < Nat.pow 2 (S j))%nat -> (Nat.pow 2 j <= a)%nat ->
  exists c, (c < Nat.pow 2 j)%nat /\ a = (c + Nat.pow 2 j)%nat.
Proof. intros Ha Hl. exists (a - Nat.pow 2 j)%nat. simpl in Ha. lia. Qed.

(** e_a e_b = sigma_k(a, b) e_(a XOR b) on the tower. *)
Theorem basis_mul k : forall a b, (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  mul k (basis k a) (basis k b) = scale k (sigma k a b) (basis k (Nat.lxor a b)).
Proof.
  induction k as [|j IH]; intros a b Ha Hb.
  - simpl in Ha, Hb. assert (a = O) as -> by lia. assert (b = O) as -> by lia. reflexivity.
  - destruct (mul_zero j) as [Zl Zr]. rewrite sigma_unfold.
    destruct (Nat.ltb_spec a (Nat.pow 2 j)) as [Hal|Hal];
      [rewrite (basis_low j a Hal)
      |destruct (split_high j a Ha Hal) as [a' [Ha' ->]]; rewrite Nat.add_sub, (basis_high j a' Ha')];
    (destruct (Nat.ltb_spec b (Nat.pow 2 j)) as [Hbl|Hbl];
      [rewrite (basis_low j b Hbl)
      |destruct (split_high j b Hb Hbl) as [b' [Hb' ->]]; rewrite Nat.add_sub, (basis_high j b' Hb')]).
    1: rewrite basis_low by (apply lxor_lt; assumption).
    2: rewrite lxor_high_r, basis_high by (try apply lxor_lt; assumption).
    3: rewrite lxor_high_l, basis_high by (try apply lxor_lt; assumption).
    4: rewrite lxor_high_lr, basis_low by (try apply lxor_lt; assumption).
    all: cbn [mul fst snd scale]; rewrite ?conj_zero, ?conj_basis by assumption;
      rewrite ?Zl, ?Zr, ?mul_scale_l, ?mul_scale_r, ?IH by assumption.
    4: rewrite (Nat.lxor_comm b' a'); unfold unit_conj; destruct (Nat.eqb_spec b' 0) as [->|];
      [rewrite sigma_zero_l|].
    all: f_equal; vec.
Qed.

Lemma sigma_ll j p q : (p < Nat.pow 2 j)%nat -> (q < Nat.pow 2 j)%nat -> sigma (S j) p q = sigma j p q.
Proof. intros Hp Hq. rewrite sigma_unfold, (proj2 (Nat.ltb_lt _ _) Hp), (proj2 (Nat.ltb_lt _ _) Hq). reflexivity. Qed.

Lemma sigma_lh j p q : (p < Nat.pow 2 j)%nat -> sigma (S j) p (q + Nat.pow 2 j) = sigma j q p.
Proof.
  intro Hp. rewrite sigma_unfold, (proj2 (Nat.ltb_lt _ _) Hp), (proj2 (Nat.ltb_ge _ _)) by lia.
  rewrite Nat.add_sub. reflexivity.
Qed.

Lemma sigma_hl j p q : (q < Nat.pow 2 j)%nat -> sigma (S j) (p + Nat.pow 2 j) q = unit_conj q * sigma j p q.
Proof.
  intro Hq. rewrite sigma_unfold, (proj2 (Nat.ltb_ge _ _)), (proj2 (Nat.ltb_lt _ _) Hq) by lia.
  rewrite Nat.add_sub. reflexivity.
Qed.

Lemma sigma_hh j p q :
  sigma (S j) (p + Nat.pow 2 j) (q + Nat.pow 2 j) = if Nat.eqb q 0 then -1 else sigma j q p.
Proof. rewrite sigma_unfold, !(proj2 (Nat.ltb_ge _ _)) by lia. rewrite !Nat.add_sub. reflexivity. Qed.

Lemma coord_low j x c : (c < Nat.pow 2 j)%nat -> coord (S j) x c = coord j (fst x) c.
Proof. intro Hc. simpl. rewrite (proj2 (Nat.ltb_lt _ _) Hc). reflexivity. Qed.

Lemma coord_high j x c : coord (S j) x (c + Nat.pow 2 j) = coord j (snd x) c.
Proof. simpl. rewrite (proj2 (Nat.ltb_ge _ _)) by lia. rewrite Nat.add_sub. reflexivity. Qed.

Lemma coord_conj k : forall x i, (i < Nat.pow 2 k)%nat -> coord k (conjugate k x) i = unit_conj i * coord k x i.
Proof.
  unfold unit_conj. induction k as [|j IH]; intros x i Hi.
  - simpl in Hi. assert (i = O) as -> by lia. symmetry. apply Z.mul_1_l.
  - destruct (Nat.ltb_spec i (Nat.pow 2 j)) as [Hl|Hl].
    + rewrite !coord_low by exact Hl. apply IH, Hl.
    + destruct (split_high j i Hi Hl) as [i' [_ ->]]. rewrite !coord_high. cbn [conjugate snd].
      rewrite coord_scale. replace (Nat.eqb (i' + Nat.pow 2 j) 0) with false
        by (symmetry; apply Nat.eqb_neq; pose proof (Nat.pow_nonzero 2 j); lia). ring.
Qed.

(** Left and right multiplication by a basis unit are signed permutations:
    (e_a y)_c = sigma_k(a, a XOR c) y_(a XOR c) and
    (y e_b)_c = sigma_k(c XOR b, b) y_(c XOR b). *)
Theorem basis_mul_coord k :
  (forall a y c, (a < Nat.pow 2 k)%nat -> (c < Nat.pow 2 k)%nat ->
     coord k (mul k (basis k a) y) c = sigma k a (Nat.lxor a c) * coord k y (Nat.lxor a c)) /\
  (forall b y c, (b < Nat.pow 2 k)%nat -> (c < Nat.pow 2 k)%nat ->
     coord k (mul k y (basis k b)) c = sigma k (Nat.lxor c b) b * coord k y (Nat.lxor c b)).
Proof.
  induction k as [|j [IHL IHR]].
  - split; intros u y c Hu Hc; simpl in Hu, Hc; assert (u = O) as -> by lia; assert (c = O) as -> by lia;
      exact (eq_trans (Z.mul_1_l y) (eq_sym (Z.mul_1_l y)))||exact (eq_trans (Z.mul_1_r y) (eq_sym (Z.mul_1_l y))).
  - destruct (mul_zero j) as [Zl Zr].
    split; intros u [y1 y2] c Hu Hc.
    all: destruct (Nat.ltb_spec u (Nat.pow 2 j)) as [Hul|Hul];
      [rewrite (basis_low j u Hul)
      |destruct (split_high j u Hu Hul) as [u' [Hu' ->]]; rewrite (basis_high j u' Hu')].
    all: destruct (Nat.ltb_spec c (Nat.pow 2 j)) as [Hcl|Hcl];
      [rewrite (coord_low j _ c Hcl)
      |destruct (split_high j c Hc Hcl) as [c' [Hc' ->]]; rewrite coord_high].
    all: cbn [mul fst snd]; rewrite ?conj_zero, ?conj_basis by assumption;
      rewrite ?Zl, ?Zr, ?mul_scale_l, ?mul_scale_r; autorewrite with coord.
    all: try rewrite IHL by assumption; try rewrite IHR by assumption; rewrite ?coord_conj by (apply lxor_lt; assumption).
    + rewrite coord_low, sigma_ll by (try apply lxor_lt; assumption). cbn [fst]. ring.
    + rewrite lxor_high_r, coord_high, sigma_lh by assumption. cbn [snd]. ring.
    + rewrite lxor_high_l, coord_high, sigma_hh by assumption. cbn [snd].
      rewrite (Nat.lxor_comm c u'). unfold unit_conj.
      destruct (Nat.eqb_spec (Nat.lxor u' c) 0) as [->|]; rewrite ?sigma_zero_l; ring.
    + rewrite lxor_high_lr, coord_low, sigma_hl by (try apply lxor_lt; assumption). cbn [fst]. ring.
    + rewrite coord_low, sigma_ll by (try apply lxor_lt; assumption). cbn [fst]. ring.
    + rewrite lxor_high_l, coord_high, sigma_hl by assumption. cbn [snd]. ring.
    + rewrite lxor_high_r, coord_high, sigma_hh by assumption. cbn [snd]. unfold unit_conj.
      destruct (Nat.eqb_spec u' 0) as [->|]; rewrite ?sigma_zero_l; ring.
    + rewrite lxor_high_lr, coord_low, sigma_lh by (try apply lxor_lt; assumption). cbn [fst].
      rewrite (Nat.lxor_comm c' u'). ring.
Qed.

Lemma coord_one k : forall i, (i < Nat.pow 2 k)%nat -> coord k (one k) i = if Nat.eqb i 0 then 1 else 0.
Proof.
  induction k as [|j IH]; intros i Hi.
  - simpl in Hi. assert (i = O) as -> by lia. reflexivity.
  - pose proof (Nat.pow_nonzero 2 j ltac:(lia)).
    destruct (Nat.ltb_spec i (Nat.pow 2 j)) as [Hl|Hl].
    + rewrite coord_low by exact Hl. apply IH, Hl.
    + destruct (split_high j i Hi Hl) as [i' [_ ->]]. rewrite coord_high, coord_zero.
      replace (Nat.eqb (i' + Nat.pow 2 j) 0) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity.
Qed.

Lemma coord_isum k : forall i, (i < Nat.pow 2 k)%nat -> coord k (isum k) i = if Nat.eqb i 0 then 0 else 1.
Proof.
  induction k as [|j IH]; intros i Hi.
  - simpl in Hi. assert (i = O) as -> by lia. reflexivity.
  - pose proof (Nat.pow_nonzero 2 j ltac:(lia)).
    destruct (Nat.ltb_spec i (Nat.pow 2 j)) as [Hl|Hl].
    + rewrite coord_low by exact Hl. apply IH, Hl.
    + destruct (split_high j i Hi Hl) as [i' [Hi' ->]]. rewrite coord_high. cbn [isum snd].
      rewrite coord_add, coord_one, IH by exact Hi'.
      replace (Nat.eqb (i' + Nat.pow 2 j) 0) with false by (symmetry; apply Nat.eqb_neq; lia).
      destruct (Nat.eqb i' 0); reflexivity.
Qed.

(** The arc matrix W_n of right multiplication by s in the standard basis:
    W_n[a XOR b, a] = sigma_k(a, b) for b <> 0 and W_n[a, a] = 0. *)
Theorem arc_entry k a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat -> b <> O ->
  coord k (mul k (basis k a) (isum k)) (Nat.lxor a b) = sigma k a b.
Proof.
  intros Ha Hb Hb0. destruct (basis_mul_coord k) as [L _].
  rewrite L by (try apply lxor_lt; assumption).
  replace (Nat.lxor a (Nat.lxor a b)) with b by bits.
  rewrite coord_isum by exact Hb. rewrite (proj2 (Nat.eqb_neq _ _) Hb0). ring.
Qed.

Theorem arc_diagonal k a : (a < Nat.pow 2 k)%nat -> coord k (mul k (basis k a) (isum k)) a = 0.
Proof.
  intro Ha. destruct (basis_mul_coord k) as [L _].
  rewrite L, Nat.lxor_nilpotent, coord_isum by (try apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  cbn [Nat.eqb]. ring.
Qed.

(** Albuquerque and Majid, Quasialgebra structure of the octonions, Corollary 4.3:
    a cochain F = (-1)^f on (Z_2)^k doubles to (Z_2)^(k+1) by
    f'((x, x'), (y, y')) = f(x, y)(1 - x') + f(y, x) x' + y' f(x, x) + x' y' (mod 2),
    the new generator on the highest index bit. Level 0 is the trivial group,
    and level 1 is the complex numbers with f(x, y) = xy. *)
Fixpoint am_exponent (k : nat) (x y : nat) : bool :=
  match k with
  | O => false
  | S j =>
      let h := Nat.pow 2 j in
      let xh := Nat.leb h x in
      let yh := Nat.leb h y in
      let xl := if xh then (x - h)%nat else x in
      let yl := if yh then (y - h)%nat else y in
      xorb (if xh then am_exponent j yl xl else am_exponent j xl yl)
        (xorb (andb yh (am_exponent j xl xl)) (andb xh yh))
  end.

Definition sign_of (e : bool) : Z := if e then -1 else 1.

Lemma am_complex x y : (x < 2)%nat -> (y < 2)%nat -> am_exponent 1 x y = andb (Nat.eqb x 1) (Nat.eqb y 1).
Proof. intros Hx Hy. destruct x as [|[|x]], y as [|[|y]]; try lia; reflexivity. Qed.

Lemma am_unfold j x y : am_exponent (S j) x y =
  let h := Nat.pow 2 j in
  let xh := Nat.leb h x in
  let yh := Nat.leb h y in
  let xl := if xh then (x - h)%nat else x in
  let yl := if yh then (y - h)%nat else y in
  xorb (if xh then am_exponent j yl xl else am_exponent j xl yl)
    (xorb (andb yh (am_exponent j xl xl)) (andb xh yh)).
Proof. reflexivity. Qed.

Lemma am_ll j x y : (x < Nat.pow 2 j)%nat -> (y < Nat.pow 2 j)%nat -> am_exponent (S j) x y = am_exponent j x y.
Proof.
  intros Hx Hy. rewrite am_unfold. cbv zeta.
  rewrite (proj2 (Nat.leb_gt _ _) Hx), (proj2 (Nat.leb_gt _ _) Hy). apply Bool.xorb_false_r.
Qed.

Lemma am_lh j x y : (x < Nat.pow 2 j)%nat ->
  am_exponent (S j) x (y + Nat.pow 2 j) = xorb (am_exponent j x y) (am_exponent j x x).
Proof.
  intro Hx. rewrite am_unfold. cbv zeta.
  rewrite (proj2 (Nat.leb_gt _ _) Hx), (proj2 (Nat.leb_le _ _)), Nat.add_sub by lia.
  cbn [andb]. rewrite Bool.xorb_false_r. reflexivity.
Qed.

Lemma am_hl j x y : (y < Nat.pow 2 j)%nat -> am_exponent (S j) (x + Nat.pow 2 j) y = am_exponent j y x.
Proof.
  intro Hy. rewrite am_unfold. cbv zeta.
  rewrite (proj2 (Nat.leb_gt _ _) Hy), (proj2 (Nat.leb_le _ _)), Nat.add_sub by lia.
  cbn [andb]. apply Bool.xorb_false_r.
Qed.

Lemma am_hh j x y : am_exponent (S j) (x + Nat.pow 2 j) (y + Nat.pow 2 j) =
  xorb (am_exponent j y x) (xorb (am_exponent j x x) true).
Proof.
  rewrite am_unfold. cbv zeta. rewrite !(proj2 (Nat.leb_le _ _)), !Nat.add_sub by lia. reflexivity.
Qed.

Lemma am_zero_l k : forall y, (y < Nat.pow 2 k)%nat -> am_exponent k 0 y = false.
Proof.
  induction k as [|j IH]; intros y Hy; [reflexivity|].
  pose proof (Nat.pow_nonzero 2 j ltac:(lia)) as Hh.
  destruct (Nat.ltb_spec y (Nat.pow 2 j)) as [Hl|Hl].
  - rewrite am_ll by lia. apply IH, Hl.
  - destruct (split_high j y Hy Hl) as [y' [Hy' ->]]. rewrite am_lh by lia. rewrite !IH by lia. reflexivity.
Qed.

Lemma am_zero_r k : forall x, (x < Nat.pow 2 k)%nat -> am_exponent k x 0 = false.
Proof.
  induction k as [|j IH]; intros x Hx; [reflexivity|].
  pose proof (Nat.pow_nonzero 2 j ltac:(lia)) as Hh.
  destruct (Nat.ltb_spec x (Nat.pow 2 j)) as [Hl|Hl].
  - rewrite am_ll by lia. apply IH, Hl.
  - destruct (split_high j x Hx Hl) as [x' [Hx' ->]]. rewrite am_hl by lia. apply am_zero_l, Hx'.
Qed.

(** F(x, x) = -1 on every unit other than the identity: e_x e_x = -1. *)
Lemma am_diagonal k : forall x, (x < Nat.pow 2 k)%nat -> am_exponent k x x = negb (Nat.eqb x 0).
Proof.
  induction k as [|j IH]; intros x Hx.
  - simpl in Hx. assert (x = O) as -> by lia. reflexivity.
  - pose proof (Nat.pow_nonzero 2 j ltac:(lia)) as Hh.
    destruct (Nat.ltb_spec x (Nat.pow 2 j)) as [Hl|Hl].
    + rewrite am_ll by lia. apply IH, Hl.
    + destruct (split_high j x Hx Hl) as [x' [_ ->]]. rewrite am_hh.
      replace (Nat.eqb (x' + Nat.pow 2 j) 0) with false by (symmetry; apply Nat.eqb_neq; lia).
      destruct (am_exponent j x' x'); reflexivity.
Qed.

(** The Corollary 4.3 cochain is the transpose of the tower sign at every level:
    (-1)^(f(a, b)) = sigma_k(b, a), so F_AM(a, b) = cd_sign(2^k, b, a). *)
Theorem am_sign k : forall a b, (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  sign_of (am_exponent k a b) = sigma k b a.
Proof.
  induction k as [|j IH]; intros a b Ha Hb; [reflexivity|].
  destruct (Nat.ltb_spec a (Nat.pow 2 j)) as [Hal|Hal];
    [|destruct (split_high j a Ha Hal) as [a' [Ha' ->]]];
  (destruct (Nat.ltb_spec b (Nat.pow 2 j)) as [Hbl|Hbl];
    [|destruct (split_high j b Hb Hbl) as [b' [Hb' ->]]]).
  - rewrite am_ll, sigma_ll by assumption. apply IH; assumption.
  - rewrite am_lh, sigma_hl, am_diagonal, <- IH by assumption. unfold sign_of, unit_conj.
    destruct (am_exponent j a b'), (Nat.eqb a 0); reflexivity.
  - rewrite am_hl, sigma_lh by assumption. apply IH; assumption.
  - rewrite am_hh, sigma_hh, am_diagonal by assumption. unfold sign_of.
    destruct (Nat.eqb_spec a' 0) as [->|].
    + rewrite am_zero_r by assumption. reflexivity.
    + rewrite <- IH by assumption. unfold sign_of. destruct (am_exponent j b' a'); reflexivity.
Qed.
