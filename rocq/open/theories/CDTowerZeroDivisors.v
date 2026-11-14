(** Zero divisors and one-sided inverses of the recursive real Cayley-Dickson tower.

    Statements at every order.  Four rest on CDTowerKernelSwap.v, the first
    two on tower_conj_left_zero (a z = 0 gives conj(a) z = 0) and the last
    two on the kernel swap tower_kernel_swap:

    - a z = 0 makes a and z orthogonal for the coordinate inner product;
    - a z = 0 with z nonzero makes a pure, re(a) = 0 (Biss, Dugger and
      Isaksen, arXiv:math/0511691, Lemma 9.4; Moreno, arXiv:q-alg/9710013,
      Corollary 1.6);
    - at order n + 1, a z = 0 with z nonzero makes a orthogonal to the unit
      (0, 1) adjoined by the last doubling as well (Biss, Dugger and Isaksen,
      Lemma 9.5; Moreno, Corollary 1.9);
    - a b = 1 exactly when b a = 1.

    Two use neither:

    - a conj(a) = conj(a) a = <a, a> 1, by induction on the order;
    - given a b = 1, a b' = 1 exactly when a (b' - b) = 0, so the right
      inverses of a are the coset of b by the kernel of z -> a z.

    The arguments use the reals in three places: the inner product is
    positive definite, a product of scalars vanishes only with a factor, and
    2 is nonzero.  No step uses associativity, alternativity or
    multiplicativity of the norm. *)

From Stdlib Require Import Reals Lra Lia PeanoNat.
From OpenGororoba Require Import RecursiveCDTower CDTowerKernelSwap.
Local Open Scope R_scope.

(** <x, 1> = re(x), and 1 is nonzero. *)

Lemma tower_inner_one_right order : forall value,
 tower_inner order value (tower_one order) = tower_real_part order value.
Proof.
 induction order as [|order induction_real]; intro value; simpl.
 - ring.
 - destruct value as [value_low value_high]. simpl. rewrite induction_real, tower_inner_zero_right. ring.
Qed.

Lemma tower_real_part_one order : tower_real_part order (tower_one order) = 1.
Proof. induction order as [|order induction_real]; simpl; [reflexivity | exact induction_real]. Qed.

Lemma tower_real_part_zero order : tower_real_part order (tower_zero order) = 0.
Proof. induction order as [|order induction_real]; simpl; [reflexivity | exact induction_real]. Qed.

Lemma tower_one_nonzero order : tower_one order <> tower_zero order.
Proof.
 intro equal. pose proof (f_equal (tower_real_part order) equal) as real_parts.
 rewrite tower_real_part_one, tower_real_part_zero in real_parts. lra.
Qed.

(** A scalar multiple vanishes only for a zero scalar or the zero vector. *)

Lemma tower_scale_zero_cases order factor value :
 tower_scale order factor value = tower_zero order -> factor = 0 \/ value = tower_zero order.
Proof.
 intro vanishing.
 pose proof (f_equal (fun scaled => tower_inner order scaled value) vanishing) as squared.
 cbv beta in squared. rewrite tower_inner_scale_left, tower_inner_zero_left in squared.
 destruct (Rmult_integral _ _ squared) as [factor_zero | norm_zero].
 - left. exact factor_zero.
 - right. apply tower_inner_self_zero. exact norm_zero.
Qed.

(** A zero-divisor pair is orthogonal: <a, z> = <conj(conj(a)) 1, z>
    = <1, conj(a) z> and conj(a) z = 0. *)

Theorem tower_zero_divisor_orthogonal order operand vector :
 tower_mul order operand vector = tower_zero order -> tower_inner order operand vector = 0.
Proof.
 intro vanishing. apply tower_conj_left_zero in vanishing.
 pose proof (tower_inner_adjoint_left order (tower_conj order operand) vector (tower_one order)) as adjoint.
 rewrite vanishing, tower_inner_zero_left, tower_conj_involution, tower_mul_one_right in adjoint.
 rewrite tower_inner_symmetric. symmetry. exact adjoint.
Qed.

(** Biss, Dugger and Isaksen, Lemma 9.4: a z = 0 with z nonzero gives
    re(a) = 0, because conj(a) z = 2 re(a) z - a z. *)

Theorem tower_zero_divisor_pure order operand vector :
 tower_mul order operand vector = tower_zero order -> vector <> tower_zero order ->
 tower_pure order operand.
Proof.
 intros vanishing nonzero. pose proof (tower_conj_left_zero order operand vector vanishing) as conjugated.
 rewrite tower_conj_mul_left_split, vanishing in conjugated. unfold tower_sub in conjugated.
 rewrite tower_neg_zero in conjugated.
 assert (scaled : tower_scale order (2 * tower_real_part order operand) vector = tower_zero order).
 { apply tower_extensionality. intro index.
   pose proof (f_equal (fun value => tower_coordinate order value index) conjugated) as coordinate.
   cbv beta in coordinate. rewrite tower_coordinate_add, !tower_coordinate_zero in coordinate.
   rewrite tower_coordinate_zero. lra. }
 destruct (tower_scale_zero_cases order _ vector scaled) as [real_zero | vector_zero].
 - unfold tower_pure. lra.
 - contradiction.
Qed.

Corollary tower_zero_divisor_pure_right order operand vector :
 tower_mul order operand vector = tower_zero order -> operand <> tower_zero order ->
 tower_pure order vector.
Proof.
 intros vanishing nonzero. apply (tower_zero_divisor_pure order vector operand); [| exact nonzero].
 apply tower_kernel_swap. exact vanishing.
Qed.

(** Biss, Dugger and Isaksen, Lemma 9.5.  The unit adjoined by the last
    doubling is (0, 1), and <x, (0, 1)> is the real part of the high half.
    For (a, b)(c, d) = 0 with a pure, (-conj(d), c)(b, a) = 0, so Lemma 9.4
    applied after the kernel swap makes b pure. *)

Definition tower_doubling_unit order : cd_tower (S order) := (tower_zero order, tower_one order).

Lemma tower_inner_doubling_unit order (value : cd_tower (S order)) :
 tower_inner (S order) value (tower_doubling_unit order) = tower_real_part order (snd value).
Proof.
 destruct value as [value_low value_high]. cbn [tower_inner tower_doubling_unit fst snd].
 rewrite tower_inner_zero_right, tower_inner_one_right. ring.
Qed.

Lemma tower_swap_zero_divisor order (a b c d : cd_tower order) :
 tower_mul (S order) (a, b) (c, d) = tower_zero (S order) -> tower_pure order a ->
 tower_mul (S order) (tower_neg order (tower_conj order d), c) (b, a) = tower_zero (S order).
Proof.
 intros vanishing pure. pose proof (tower_pure_conj_neg order a pure) as conjugate_a.
 pose proof (f_equal fst vanishing) as low. pose proof (f_equal snd vanishing) as high.
 cbn [tower_mul fst snd tower_zero] in low, high. cbn [tower_mul fst snd tower_zero]. f_equal.
 - unfold tower_sub in *.
   rewrite conjugate_a, !tower_mul_neg_left, tower_neg_involution, tower_add_comm. exact low.
 - pose proof (f_equal (tower_conj order) high) as conjugated.
   rewrite tower_conj_add, !tower_conj_antimorphism, tower_conj_involution, tower_conj_zero, conjugate_a,
     tower_mul_neg_left in conjugated.
   rewrite tower_mul_neg_right. exact conjugated.
Qed.

Lemma tower_swap_nonzero order (c d : cd_tower order) :
 (c, d) <> tower_zero (S order) -> (tower_neg order (tower_conj order d), c) <> tower_zero (S order).
Proof.
 intros nonzero equal. apply nonzero.
 pose proof (f_equal fst equal) as low. pose proof (f_equal snd equal) as high.
 cbn [fst snd tower_zero] in low, high. cbn [tower_zero]. f_equal; [exact high |].
 rewrite <- (tower_conj_involution order d), <- (tower_neg_involution order (tower_conj order d)), low,
   tower_neg_zero.
 apply tower_conj_zero.
Qed.

Theorem tower_zero_divisor_doubly_pure order (operand vector : cd_tower (S order)) :
 tower_mul (S order) operand vector = tower_zero (S order) -> vector <> tower_zero (S order) ->
 tower_inner (S order) operand (tower_one (S order)) = 0 /\
 tower_inner (S order) operand (tower_doubling_unit order) = 0.
Proof.
 intros vanishing nonzero. destruct operand as [a b], vector as [c d].
 pose proof (tower_zero_divisor_pure (S order) (a, b) (c, d) vanishing nonzero) as pure.
 unfold tower_pure in pure. cbn [tower_real_part fst] in pure.
 split.
 - rewrite tower_inner_one_right. exact pure.
 - rewrite tower_inner_doubling_unit. cbn [snd].
   exact (tower_zero_divisor_pure (S order) (b, a) _
            (tower_kernel_swap (S order) _ _ (tower_swap_zero_divisor order a b c d vanishing pure))
            (tower_swap_nonzero order c d nonzero)).
Qed.

Corollary tower_zero_divisor_doubly_pure_right order (operand vector : cd_tower (S order)) :
 tower_mul (S order) operand vector = tower_zero (S order) -> operand <> tower_zero (S order) ->
 tower_inner (S order) vector (tower_one (S order)) = 0 /\
 tower_inner (S order) vector (tower_doubling_unit order) = 0.
Proof.
 intros vanishing nonzero.
 exact (tower_zero_divisor_doubly_pure order vector operand (tower_kernel_swap (S order) _ _ vanishing) nonzero).
Qed.

(** a conj(a) = conj(a) a = <a, a> 1. *)

Lemma tower_mul_conj order : forall value,
 tower_mul order value (tower_conj order value) =
   tower_scale order (tower_inner order value value) (tower_one order) /\
 tower_mul order (tower_conj order value) value =
   tower_scale order (tower_inner order value value) (tower_one order).
Proof.
 induction order as [|order induction_norm]; intro value.
 - simpl. split; ring.
 - destruct value as [low high].
   destruct (induction_norm low) as [low_right low_left]. destruct (induction_norm high) as [high_right high_left].
   cbn [tower_mul tower_conj tower_inner tower_scale tower_one fst snd]. unfold tower_sub.
   rewrite ?tower_conj_neg, ?tower_conj_involution, ?tower_mul_neg_left, ?tower_mul_neg_right,
     ?tower_neg_involution, ?low_right, ?low_left, ?high_right, ?high_left.
   split; f_equal; tower_vector.
Qed.

Lemma tower_mul_conj_right order value :
 tower_mul order value (tower_conj order value) = tower_scale order (tower_inner order value value) (tower_one order).
Proof. apply tower_mul_conj. Qed.

Lemma tower_mul_conj_left order value :
 tower_mul order (tower_conj order value) value = tower_scale order (tower_inner order value value) (tower_one order).
Proof. apply tower_mul_conj. Qed.

(** A right inverse is a left inverse.  With N = <a, a>, a b = 1 gives
    a (N b - conj(a)) = 0, the kernel swap gives (N b - conj(a)) a = 0, and
    N is nonzero. *)

Theorem tower_right_inverse_is_left_inverse order operand inverse :
 tower_mul order operand inverse = tower_one order -> tower_mul order inverse operand = tower_one order.
Proof.
 intro right_inverse.
 assert (norm_nonzero : tower_inner order operand operand <> 0).
 { intro norm_zero. apply tower_inner_self_zero in norm_zero.
   rewrite norm_zero, tower_mul_zero_left in right_inverse.
   exact (tower_one_nonzero order (eq_sym right_inverse)). }
 assert (annihilated : tower_mul order operand
           (tower_sub order (tower_scale order (tower_inner order operand operand) inverse)
              (tower_conj order operand)) = tower_zero order).
 { unfold tower_sub.
   rewrite tower_mul_add_right, tower_mul_neg_right, tower_mul_scale_right, right_inverse, tower_mul_conj_right.
   apply tower_add_neg. }
 apply tower_kernel_swap in annihilated. unfold tower_sub in annihilated.
 rewrite tower_mul_add_left, tower_mul_neg_left, tower_mul_scale_left, tower_mul_conj_left in annihilated.
 assert (scaled : tower_scale order (tower_inner order operand operand)
           (tower_sub order (tower_mul order inverse operand) (tower_one order)) = tower_zero order).
 { apply tower_extensionality. intro index.
   pose proof (f_equal (fun value => tower_coordinate order value index) annihilated) as coordinate.
   cbv beta in coordinate. unfold tower_sub.
   rewrite tower_coordinate_add, tower_coordinate_neg, !tower_coordinate_scale, tower_coordinate_zero in coordinate.
   rewrite tower_coordinate_scale, tower_coordinate_add, tower_coordinate_neg, tower_coordinate_zero. lra. }
 destruct (tower_scale_zero_cases order _ _ scaled) as [norm_zero | difference_zero]; [contradiction |].
 apply tower_extensionality. intro index.
 pose proof (f_equal (fun value => tower_coordinate order value index) difference_zero) as coordinate.
 cbv beta in coordinate. unfold tower_sub in coordinate.
 rewrite tower_coordinate_add, tower_coordinate_neg, tower_coordinate_zero in coordinate. lra.
Qed.

Theorem tower_one_sided_inverse order operand inverse :
 tower_mul order operand inverse = tower_one order <-> tower_mul order inverse operand = tower_one order.
Proof.
 split; [apply tower_right_inverse_is_left_inverse |].
 intro left_inverse.
 pose proof (f_equal (tower_conj order) left_inverse) as conjugated.
 rewrite tower_conj_antimorphism, tower_conj_one in conjugated.
 apply tower_right_inverse_is_left_inverse in conjugated.
 pose proof (f_equal (tower_conj order) conjugated) as restored.
 rewrite tower_conj_antimorphism, !tower_conj_involution, tower_conj_one in restored. exact restored.
Qed.

(** The right inverses of a form a coset of the kernel of z -> a z.  Every
    nonzero a has the inverse conj(a) / <a, a> (tower_mul_conj), so a zero
    divisor has several right inverses, and the two-sided statement above
    holds for each of them. *)

Theorem tower_right_inverse_coset order operand inverse other :
 tower_mul order operand inverse = tower_one order ->
 (tower_mul order operand other = tower_one order <->
  tower_mul order operand (tower_sub order other inverse) = tower_zero order).
Proof.
 intro right_inverse. unfold tower_sub. rewrite tower_mul_add_right, tower_mul_neg_right, right_inverse. split.
 - intro other_inverse. rewrite other_inverse. apply tower_add_neg.
 - intro difference. apply tower_extensionality. intro index.
   pose proof (f_equal (fun value => tower_coordinate order value index) difference) as coordinate.
   cbv beta in coordinate. rewrite tower_coordinate_add, tower_coordinate_neg, tower_coordinate_zero in coordinate.
   lra.
Qed.

Print Assumptions tower_zero_divisor_orthogonal.
Print Assumptions tower_zero_divisor_pure.
Print Assumptions tower_zero_divisor_doubly_pure.
Print Assumptions tower_one_sided_inverse.
Print Assumptions tower_right_inverse_coset.
