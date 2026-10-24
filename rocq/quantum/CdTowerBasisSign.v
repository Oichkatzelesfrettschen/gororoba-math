(** Basis products of the integer pair tower of CdImaginarySumConference.v.
    In the standard basis e_a, a < 2^k, the tower multiplies basis units as
    e_a e_b = sigma_k(a, b) e_(a XOR b), with sigma_k the loop of
    gororoba_quantum/cd_core.py cd_sign unrolled one doubling per level.
    Left and right multiplication by e_a are signed permutations, so the arc
    matrix of R_s, s the imaginary sum, has entry sigma_k(a, b) at row a XOR b,
    column a for b <> 0 and 0 on the diagonal. The cochain recursion of
    Albuquerque and Majid, Quasialgebra structure of the octonions,
    Corollary 4.3, gives (-1)^f(a, b) = sigma_k(b, a) at every level, and
    reproduces its Proposition 4.4 quaternion and octonion cochains and the
    Proposition 4.2 laws: F(x, x) = -1 off the identity and anticommuting
    distinct imaginary units. Multiplying twice by an imaginary unit negates
    every basis element on either side, a right multiplication matrix
    carries each coefficient on its own XOR diagonal, and alpha I + beta W_n
    is a scaled isometry. *)

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

(** Proposition 4.4 of the same paper, read with paper index i on index
    bit i - 1. (ii) is the quaternion level. (iii) is the octonion level
    with the cubic term x1 x2 y3, which Corollary 4.3 produces; the printed
    x2 x2 y3 differs from the recursion at x = 2, y = 4. *)
Definition bit (x i : nat) : bool := Nat.testbit x i.

Theorem am_quaternion x y : (x < 4)%nat -> (y < 4)%nat ->
  am_exponent 2 x y = xorb (andb (bit x 0) (bit y 0)) (andb (xorb (bit x 0) (bit x 1)) (bit y 1)).
Proof. intros Hx Hy. destruct x as [|[|[|[|x]]]], y as [|[|[|[|y]]]]; try lia; reflexivity. Qed.

Definition octonion_bilinear (x y : nat) : bool :=
  xorb (andb (bit x 0) (bit y 0))
    (xorb (andb (xorb (bit x 0) (bit x 1)) (bit y 1))
       (andb (xorb (xorb (bit x 0) (bit x 1)) (bit x 2)) (bit y 2))).

Definition octonion_exponent (cubic : bool) (x y : nat) : bool :=
  xorb (octonion_bilinear x y)
    (xorb (andb (andb (bit y 0) (bit x 1)) (bit x 2))
       (xorb (andb (andb (bit x 0) (bit y 1)) (bit x 2))
          (andb (andb cubic (bit x 1)) (bit y 2)))).

Theorem am_octonion x y : (x < 8)%nat -> (y < 8)%nat ->
  am_exponent 3 x y = octonion_exponent (bit x 0) x y.
Proof.
  intros Hx Hy.
  destruct x as [|[|[|[|[|[|[|[|x]]]]]]]], y as [|[|[|[|[|[|[|[|y]]]]]]]]; try lia; reflexivity.
Qed.

Theorem am_octonion_printed_differs : am_exponent 3 2 4 <> octonion_exponent (bit 2 1) 2 4.
Proof. discriminate. Qed.

(** Proposition 4.2 and Definition 3.2: F(x, x) = -1 off the identity, and
    distinct imaginary units anticommute while the identity commutes. *)
Lemma unit_neq_high j x : (x + Nat.pow 2 j <> 0)%nat.
Proof. pose proof (Nat.pow_nonzero 2 j ltac:(lia)). lia. Qed.

Theorem am_altercommutative k : forall a b, (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  xorb (am_exponent k a b) (am_exponent k b a) =
  andb (negb (Nat.eqb a 0)) (andb (negb (Nat.eqb b 0)) (negb (Nat.eqb a b))).
Proof.
  induction k as [|j IH]; intros a b Ha Hb.
  - simpl in Ha, Hb. assert (a = O) as -> by lia. assert (b = O) as -> by lia. reflexivity.
  - destruct (Nat.ltb_spec a (Nat.pow 2 j)) as [Hal|Hal];
      [|destruct (split_high j a Ha Hal) as [a' [Ha' ->]]];
    (destruct (Nat.ltb_spec b (Nat.pow 2 j)) as [Hbl|Hbl];
      [|destruct (split_high j b Hb Hbl) as [b' [Hb' ->]]]).
    + rewrite !am_ll by assumption. apply IH; assumption.
    + rewrite am_lh, am_hl, am_diagonal by assumption.
      rewrite (proj2 (Nat.eqb_neq _ _) (unit_neq_high j b')), (proj2 (Nat.eqb_neq a (b' + Nat.pow 2 j))) by lia.
      destruct (am_exponent j a b'), (Nat.eqb a 0); reflexivity.
    + rewrite am_hl, am_lh, am_diagonal by assumption.
      rewrite (proj2 (Nat.eqb_neq _ _) (unit_neq_high j a')), (proj2 (Nat.eqb_neq (a' + Nat.pow 2 j) b)) by lia.
      destruct (am_exponent j b a'), (Nat.eqb b 0); reflexivity.
    + rewrite !am_hh, !am_diagonal by assumption.
      rewrite !(proj2 (Nat.eqb_neq _ _) (unit_neq_high j _)).
      replace (Nat.eqb (a' + Nat.pow 2 j) (b' + Nat.pow 2 j)) with (Nat.eqb a' b')
        by (destruct (Nat.eqb_spec a' b'), (Nat.eqb_spec (a' + Nat.pow 2 j) (b' + Nat.pow 2 j)); lia).
      pose proof (IH a' b' Ha' Hb') as C. revert C.
      destruct (Nat.eqb_spec a' 0) as [->|Ha0], (Nat.eqb_spec b' 0) as [->|Hb0];
        rewrite ?am_zero_l, ?am_zero_r by lia; rewrite ?(Nat.eqb_sym 0);
        rewrite ?(proj2 (Nat.eqb_neq _ _) Ha0), ?(proj2 (Nat.eqb_neq _ _) Hb0); cbn [Nat.eqb negb andb xorb];
        repeat match goal with
        | |- context [am_exponent j ?x ?y] => destruct (am_exponent j x y)
        | |- context [Nat.eqb ?x ?y] => destruct (Nat.eqb x y)
        end; cbn; congruence.
Qed.

Theorem sigma_diagonal k a : (a < Nat.pow 2 k)%nat -> a <> O -> sigma k a a = -1.
Proof.
  intros Ha Ha0. rewrite <- am_sign, am_diagonal by exact Ha.
  rewrite (proj2 (Nat.eqb_neq _ _) Ha0). reflexivity.
Qed.

Theorem sigma_anticommute k a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  a <> O -> b <> O -> a <> b -> sigma k a b = - sigma k b a.
Proof.
  intros Ha Hb Ha0 Hb0 Hab. rewrite <- !am_sign by assumption.
  pose proof (am_altercommutative k b a Hb Ha) as C.
  rewrite (proj2 (Nat.eqb_neq _ _) Ha0), (proj2 (Nat.eqb_neq _ _) Hb0), (proj2 (Nat.eqb_neq b a)) in C by lia.
  unfold sign_of. destruct (am_exponent k b a), (am_exponent k a b); simpl in C; congruence || reflexivity.
Qed.

Lemma lxor_eqb_0 a b : Nat.eqb (Nat.lxor a b) 0 = Nat.eqb a b.
Proof.
  destruct (Nat.eqb_spec (Nat.lxor a b) 0) as [H|H], (Nat.eqb_spec a b) as [E|E]; try reflexivity.
  - exfalso. apply E, Nat.lxor_eq, H.
  - exfalso. apply H. subst. apply Nat.lxor_nilpotent.
Qed.

Lemma lxor_eqb_self a b : Nat.eqb a (Nat.lxor a b) = Nat.eqb b 0.
Proof.
  rewrite Nat.eqb_sym, <- (lxor_eqb_0 (Nat.lxor a b) a).
  replace (Nat.lxor (Nat.lxor a b) a) with b by bits. reflexivity.
Qed.

Lemma lxor_eqb_self_r a b : Nat.eqb b (Nat.lxor a b) = Nat.eqb a 0.
Proof. rewrite Nat.lxor_comm. apply lxor_eqb_self. Qed.

Ltac close_bool :=
  repeat match goal with |- context [am_exponent ?k ?x ?y] => destruct (am_exponent k x y) end;
  cbn; congruence.

(** e_a (e_a e_x) = -e_x off the identity: in exponents,
    f(x, a) + f(a XOR x, a) = [a <> 0]. *)
Theorem am_left_involution k : forall a x, (a < Nat.pow 2 k)%nat -> (x < Nat.pow 2 k)%nat ->
  xorb (am_exponent k x a) (am_exponent k (Nat.lxor a x) a) = negb (Nat.eqb a 0).
Proof.
  induction k as [|j IH]; intros a x Ha Hx.
  - simpl in Ha, Hx. assert (a = O) as -> by lia. assert (x = O) as -> by lia. reflexivity.
  - destruct (Nat.ltb_spec a (Nat.pow 2 j)) as [Hal|Hal];
      [|destruct (split_high j a Ha Hal) as [a' [Ha' ->]]];
    (destruct (Nat.ltb_spec x (Nat.pow 2 j)) as [Hxl|Hxl];
      [|destruct (split_high j x Hx Hxl) as [x' [Hx' ->]]]).
    + rewrite !am_ll by (try apply lxor_lt; assumption). apply IH; assumption.
    + rewrite lxor_high_r, (Nat.lxor_comm x' a), !am_hl by (try apply lxor_lt; assumption).
      pose proof (IH a x' Hal Hx') as L.
      pose proof (am_altercommutative j a x' Hal Hx') as C1.
      pose proof (am_altercommutative j a (Nat.lxor a x') Hal ltac:(apply lxor_lt; assumption)) as C2.
      rewrite lxor_eqb_0, lxor_eqb_self in C2. revert L C1 C2.
      destruct (Nat.eqb_spec a 0), (Nat.eqb_spec x' 0), (Nat.eqb_spec a x'); try (exfalso; lia); close_bool.
    + rewrite lxor_high_l, am_lh, am_hh, !am_diagonal by (try apply lxor_lt; assumption).
      rewrite (proj2 (Nat.eqb_neq _ _) (unit_neq_high j a')), lxor_eqb_0.
      pose proof (IH a' x Ha' Hxl) as L.
      pose proof (am_altercommutative j a' (Nat.lxor a' x) Ha' ltac:(apply lxor_lt; assumption)) as C.
      rewrite lxor_eqb_0, lxor_eqb_self in C. revert L C.
      destruct (Nat.eqb_spec a' 0), (Nat.eqb_spec x 0), (Nat.eqb_spec a' x); try (exfalso; lia); close_bool.
    + rewrite lxor_high_lr, am_hh, am_lh, !am_diagonal by (try apply lxor_lt; assumption).
      rewrite (proj2 (Nat.eqb_neq _ _) (unit_neq_high j a')), lxor_eqb_0.
      pose proof (IH a' x' Ha' Hx') as L.
      pose proof (am_altercommutative j a' x' Ha' Hx') as C. revert L C.
      destruct (Nat.eqb_spec a' 0), (Nat.eqb_spec x' 0), (Nat.eqb_spec a' x'); try (exfalso; lia); close_bool.
Qed.

(** Left and right multiplication by an imaginary unit square to -1 on the
    basis: e_a (e_a e_x) = -e_x and (e_x e_b) e_b = -e_x. *)
Theorem sigma_left_involution k a x : (a < Nat.pow 2 k)%nat -> (x < Nat.pow 2 k)%nat -> a <> O ->
  sigma k a x * sigma k a (Nat.lxor a x) = -1.
Proof.
  intros Ha Hx Ha0. rewrite <- !am_sign by (try apply lxor_lt; assumption).
  pose proof (am_left_involution k a x Ha Hx) as L. rewrite (proj2 (Nat.eqb_neq _ _) Ha0) in L.
  unfold sign_of. revert L. close_bool || (destruct (am_exponent k x a), (am_exponent k (Nat.lxor a x) a); cbn; congruence).
Qed.

Theorem sigma_right_involution k a b : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat -> b <> O ->
  sigma k a b * sigma k (Nat.lxor a b) b = -1.
Proof.
  intros Ha Hb Hb0. rewrite <- !am_sign by (try apply lxor_lt; assumption).
  pose proof (am_left_involution k b a Hb Ha) as L.
  pose proof (am_altercommutative k b a Hb Ha) as C1.
  pose proof (am_altercommutative k b (Nat.lxor a b) Hb ltac:(apply lxor_lt; assumption)) as C2.
  rewrite (Nat.lxor_comm b a) in L. rewrite lxor_eqb_0, lxor_eqb_self_r in C2.
  rewrite (proj2 (Nat.eqb_neq _ _) Hb0) in L, C1, C2.
  unfold sign_of. revert L C1 C2. destruct (Nat.eqb_spec a 0), (Nat.eqb_spec a b), (Nat.eqb_spec b a); try (exfalso; lia); close_bool.
Qed.

(** A right multiplication matrix R_v carries v_b on the XOR diagonal b:
    R_v[a XOR b, a] = (e_a v)_(a XOR b) = sigma_k(a, b) v_b, so every column
    recovers every coefficient. *)
Theorem right_mul_entry k a b v : (a < Nat.pow 2 k)%nat -> (b < Nat.pow 2 k)%nat ->
  coord k (mul k (basis k a) v) (Nat.lxor a b) = sigma k a b * coord k v b.
Proof.
  intros Ha Hb. destruct (basis_mul_coord k) as [L _].
  rewrite L by (try apply lxor_lt; assumption).
  replace (Nat.lxor a (Nat.lxor a b)) with b by bits. reflexivity.
Qed.

(** alpha I + beta W_n is a scaled isometry for all integers alpha, beta. *)
Theorem isum_scaled_isometry k alpha beta x y :
  dot k (add k (scale k alpha x) (scale k beta (mul k x (isum k))))
        (add k (scale k alpha y) (scale k beta (mul k y (isum k)))) =
  (alpha * alpha + (2 ^ Z.of_nat k - 1) * (beta * beta)) * dot k x y.
Proof.
  destruct (isum_skew k) as [_ SkR].
  rewrite !dot_add_l, !dot_add_r, !dot_scale_l, !dot_scale_r, isum_conference, (SkR x y). ring.
Qed.

Lemma pow2_ge_4 k : (2 <= k)%nat -> (4 <= Nat.pow 2 k)%nat.
Proof. intro Hk. change 4%nat with (Nat.pow 2 2). apply Nat.pow_le_mono_r; lia. Qed.

Lemma sigma_1_2 k : (2 <= k)%nat -> sigma k 1 2 = 1 /\ sigma k 2 1 = -1.
Proof.
  induction k as [|j IH]; intro Hk; [lia|].
  destruct (Nat.eq_dec j 1) as [->|Hj]; [split; reflexivity|].
  pose proof (pow2_ge_4 j ltac:(lia)). rewrite !sigma_ll by lia. apply IH. lia.
Qed.

(** Right and left multiplication by s differ on the coherent input
    e_0 + e_1 at coordinate 3 for every n >= 4: (e_0 + e_1) s has entry 2
    there and s (e_0 + e_1) has entry 0, while both operators share the Gram
    matrix of isum_conference. *)
Theorem convention_discriminator k : (2 <= k)%nat ->
  coord k (mul k (add k (basis k 0) (basis k 1)) (isum k)) 3 = 2 /\
  coord k (mul k (isum k) (add k (basis k 0) (basis k 1))) 3 = 0.
Proof.
  intro Hk. pose proof (pow2_ge_4 k Hk) as H4. destruct (sigma_1_2 k Hk) as [S12 S21].
  destruct (basis_mul_coord k) as [L R].
  rewrite mul_add_l, mul_add_r, !coord_add, (L 0%nat), (L 1%nat), (R 0%nat), (R 1%nat) by lia.
  change (Nat.lxor 0 3) with 3%nat. change (Nat.lxor 1 3) with 2%nat.
  change (Nat.lxor 3 0) with 3%nat. change (Nat.lxor 3 1) with 2%nat.
  rewrite !coord_isum by lia. cbn [Nat.eqb].
  rewrite sigma_zero_l, sigma_zero_r, S12, S21. split; reflexivity.
Qed.
