(** The conjugate identities of the trace form: the Rocq bridge of the Lean module
    lean/GororobaMath/CayleyDickson/TraceForm.lean.

    Convention: the tower, product and conjugation of CdTowerDomain.v,
    (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)) and conj (a, b) = (conj a, -b), with the identity as the
    conjugation of the coefficients. The Lean tower has the same product and star; the Lean negation -x is
    scale k neg_one x, the Lean zero is zero k, and the Lean hypothesis star a = -a is pure k a.
    Tower.dot k is dot k and Tower.re k is re k.

    The functor TraceFormBridge restates the ordered-domain theorems of the Lean module at the coefficient ring D,
    TraceFormFieldBridge restates right_inverse_form at the ordered field F, and TraceFormRingBridge
    restates two_zero_commutative at the commutative ring D, each with the Rocq statement of its source theorem:

    - re_commutator is Tower.re_mul_comm.
    - re_associator is Tower.re_mul_assoc.
    - conj_mul_left is Tower.mul_star_mul_left.
    - conj_mul_right is Tower.mul_mul_star_right.
    - flexible is Tower.mul_mul_self_eq, with the hypothesis that 2 is left regular, which an ordered domain satisfies.
    - lemma_9_2 is Tower.mul_eq_zero_iff_star_mul_eq_zero.
    - purity_right is Tower.re_eq_zero_of_mul_eq_zero_rev.
    - lemma_9_5 is Tower.dot_one_eq_zero_and_dot_mk_zero_one_of_mul_eq_zero.
    - annihilator_orthogonal is Tower.dot_one_eq_zero_and_dot_mk_zero_one_of_mul_eq_zero_right.
    - right_inverse_affine is Tower.mul_dot_smul_sub_star_eq_zero.
    - right_inverse_form is Tower.exists_eq_inv_dot_smul_star_add.
    - two_zero_commutative is Tower.mul_comm_of_two_eq_zero.

    The Rocq statements are narrower than the Lean ones: the coefficients form an ordered domain whose conjugation is the identity
    (the signature OrderedDomain), where Lean takes a commutative ring with the identity as star, and for the order-dependent
    theorems the ordered section of its module.
    IntegerTraceFormBridge and IntegerTraceFormRingBridge instantiate the functors at the integers,
    and RealTraceFormFieldBridge instantiates the field functor at the real numbers. *)

Require Import CdTowerRing CdTowerDomain.

Module TraceFormBridge (D : OrderedDomain).
Module T := CdTower D.
Import T.

Theorem re_commutator k x y : re k (mul k x y) = re k (mul k y x).
Proof. apply T.re_commutator. Qed.

Theorem re_associator k x y z : re k (mul k (mul k x y) z) = re k (mul k x (mul k y z)).
Proof. apply T.re_associator. Qed.

Theorem conj_mul_left k x y : mul k x (mul k (conjugate k x) y) = mul k (conjugate k x) (mul k x y).
Proof. apply T.conj_mul_left. Qed.

Theorem conj_mul_right k x y : mul k (mul k x y) (conjugate k y) = mul k (mul k x (conjugate k y)) y.
Proof. apply T.conj_mul_right. Qed.

Theorem flexible k x y : mul k (mul k x y) x = mul k x (mul k y x).
Proof. apply T.flexible. Qed.

Theorem lemma_9_2 k x y :
  (mul k x y = zero k <-> mul k (conjugate k x) y = zero k) /\
  (mul k x y = zero k <-> mul k x (conjugate k y) = zero k).
Proof. apply T.lemma_9_2. Qed.

Theorem purity_right k a z :
  mul k z a = zero k -> a <> zero k -> z <> zero k -> re k a = D.zero /\ re k z = D.zero.
Proof. apply T.purity_right. Qed.

Theorem lemma_9_5 k (x y : cd (S k)) :
  mul (S k) x y = zero (S k) -> y <> zero (S k) ->
  dot (S k) x (one (S k)) = D.zero /\ dot (S k) x (i_unit k) = D.zero.
Proof. apply T.lemma_9_5. Qed.

Theorem annihilator_orthogonal k (x y : cd (S k)) :
  x <> zero (S k) -> mul (S k) x y = zero (S k) ->
  dot (S k) y (one (S k)) = D.zero /\ dot (S k) y (i_unit k) = D.zero.
Proof. apply T.annihilator_orthogonal. Qed.

Theorem right_inverse_affine k a b :
  mul k a b = one k ->
  mul k a (add k (scale k (dot k a a) b) (scale k neg_one (conjugate k a))) = zero k.
Proof. apply T.right_inverse_affine. Qed.

End TraceFormBridge.

Module TraceFormFieldBridge (F : OrderedField).
Module CF := CdTowerField F.
Import CF.

Theorem right_inverse_form k a b :
  T.mul k a b = T.one k ->
  exists w, T.mul k a w = T.zero k /\ b = T.add k (T.scale k (F.inv (T.dot k a a)) (T.conjugate k a)) w.
Proof. apply CF.right_inverse_form. Qed.

End TraceFormFieldBridge.

Module TraceFormRingBridge (D : CommutativeRing).
Module T := RingTower D.
Import T.

Theorem two_zero_commutative k x y : two = D.zero -> mul k x y = mul k y x.
Proof. apply T.two_zero_commutative. Qed.

End TraceFormRingBridge.

Module IntegerTraceFormBridge := TraceFormBridge ZDomain.
Module IntegerTraceFormRingBridge := TraceFormRingBridge ZDomain.
Module RealTraceFormFieldBridge := TraceFormFieldBridge RField.
