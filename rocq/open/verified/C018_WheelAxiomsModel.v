(** * C-018 successor: which of Carlstrom's wheel axioms the 3-element model satisfies.

    Source: J. Carlstrom, Wheels - on division by zero, Math. Struct. in
    Comp. Sci. 14 (2004) 143-184, Definition 1.1 (page 146).  A wheel is a
    structure (H, 0, 1, +, *, /) with 0 and 1 constants, + and * binary and
    / unary, such that (writing x/y for x * /y):

      (1) (H, 0, +) is a commutative monoid;
      (2) (H, 1, *, /) is a commutative monoid with involution /, that is
          //x = x and /(x y) = /y /x (Definition 2.1);
      (3) (x + y) z + 0 z = x z + y z;
      (4) x/y + z + 0 y = (x + y z)/y;
      (5) 0 * 0 = 0;
      (6) (x + 0 y) z = x z + 0 y;
      (7) /(x + 0 y) = /x + 0 y;
      (8) x + 0/0 = 0/0.

    The rule 0 x = 0 is not an axiom: zero-terms move but are not erased.

    Convention.  The model is the one of [C018_WheelsAxioms]: the
    elements [W0], [W1], [Wbot], with [wadd], [wmul] and [winv] imported
    from that file, and the constants 0 = [W0] and 1 = [W1].  [wheel_axioms]
    lists the axioms above as fourteen fields (commutative monoid laws of
    (1) and (2), the involution law and the reversal law of (2), then (3)
    to (8)); [wdiv x y] is [wmul x (winv y)] and [wbot] is [wdiv W0 W0].

    Results.
    - Satisfied: associativity, commutativity and identity of + and *
      (the commutative monoid parts of (1) and (2)), //x = x, and (5), (6),
      (7) ([model_holds]).
    - Violated: /(x y) = /y /x at x = W0, y = Wbot; (3) at x = W1, y = W1,
      z = Wbot; (4) at x = W0, y = W0, z = W1; (8) at x = W1
      ([model_fails]).  So the model is not a wheel ([model_not_wheel]).
    - [wmul] has [W0] as a two-sided absorber ([wmul_zero_absorbs]), which
      a wheel with more than one element excludes
      ([absorbing_zero_forces_trivial]); and [wbot] = [wdiv W0 W0] is [W0],
      not [Wbot] ([model_bottom_is_zero]).  The element [Wbot] absorbs
      under [wadd] ([wadd_bot_absorbs]) and does not absorb under [wmul]:
      [wmul W0 Wbot] is [W0] ([wmul_bot_not_absorbing]).

    Scope.  The file decides the axioms on this one model.  The original
    file proves seven of the fourteen fields, and its header calls them
    Carlstrom's axioms; this file shows that the model fails four of the
    fourteen.  It proves no statement about wheels in general, and none
    about the zero-divisor question of C-019. *)

From OpenGororobaVerified Require Import C018_WheelsAxioms.

#[universes(template=no)]
Record wheel_axioms {H : Type} (zero one : H) (add mul : H -> H -> H)
  (inv : H -> H) : Prop := {
  wa_add_assoc : forall x y z, add (add x y) z = add x (add y z);
  wa_add_comm : forall x y, add x y = add y x;
  wa_add_zero : forall x, add zero x = x;
  wa_mul_assoc : forall x y z, mul (mul x y) z = mul x (mul y z);
  wa_mul_comm : forall x y, mul x y = mul y x;
  wa_mul_one : forall x, mul one x = x;
  wa_inv_inv : forall x, inv (inv x) = x;
  wa_inv_mul : forall x y, inv (mul x y) = mul (inv y) (inv x);
  wa_distrib : forall x y z,
    add (mul (add x y) z) (mul zero z) = add (mul x z) (mul y z);
  wa_div_add : forall x y z,
    add (add (mul x (inv y)) z) (mul zero y) = mul (add x (mul y z)) (inv y);
  wa_zero_zero : mul zero zero = zero;
  wa_zero_mul : forall x y z,
    mul (add x (mul zero y)) z = add (mul x z) (mul zero y);
  wa_inv_add : forall x y,
    inv (add x (mul zero y)) = add (inv x) (mul zero y);
  wa_bot_add : forall x,
    add x (mul zero (inv zero)) = mul zero (inv zero)
}.

Definition wdiv (x y : wheel_elt) : wheel_elt := wmul x (winv y).
Definition wbot : wheel_elt := wdiv W0 W0.

Theorem model_holds :
  (forall x y z, wadd (wadd x y) z = wadd x (wadd y z)) /\
  (forall x y, wadd x y = wadd y x) /\
  (forall x, wadd W0 x = x) /\
  (forall x y z, wmul (wmul x y) z = wmul x (wmul y z)) /\
  (forall x y, wmul x y = wmul y x) /\
  (forall x, wmul W1 x = x) /\
  (forall x, winv (winv x) = x) /\
  wmul W0 W0 = W0 /\
  (forall x y z, wmul (wadd x (wmul W0 y)) z = wadd (wmul x z) (wmul W0 y)) /\
  (forall x y, winv (wadd x (wmul W0 y)) = wadd (winv x) (wmul W0 y)).
Proof.
  repeat split; try reflexivity;
    intros []; try intros []; try intros []; reflexivity.
Qed.

Theorem model_fails :
  winv (wmul W0 Wbot) <> wmul (winv Wbot) (winv W0) /\
  wadd (wmul (wadd W1 W1) Wbot) (wmul W0 Wbot)
    <> wadd (wmul W1 Wbot) (wmul W1 Wbot) /\
  wadd (wadd (wmul W0 (winv W0)) W1) (wmul W0 W0)
    <> wmul (wadd W0 (wmul W0 W1)) (winv W0) /\
  wadd W1 (wmul W0 (winv W0)) <> wmul W0 (winv W0).
Proof. repeat split; discriminate. Qed.

Theorem model_not_wheel :
  ~ wheel_axioms W0 W1 wadd wmul winv.
Proof.
  intros H.
  destruct model_fails as [F1 _]. apply F1.
  exact (wa_inv_mul _ _ _ _ _ H W0 Wbot).
Qed.

Theorem model_not_wheel_distributivity :
  ~ (forall x y z,
      wadd (wmul (wadd x y) z) (wmul W0 z) = wadd (wmul x z) (wmul y z)).
Proof.
  intros H. destruct model_fails as [_ [F _]]. apply F. exact (H W1 W1 Wbot).
Qed.

Theorem model_not_wheel_div_add :
  ~ (forall x y z,
      wadd (wadd (wmul x (winv y)) z) (wmul W0 y)
      = wmul (wadd x (wmul y z)) (winv y)).
Proof.
  intros H. destruct model_fails as [_ [_ [F _]]]. apply F. exact (H W0 W0 W1).
Qed.

Theorem model_not_wheel_bot_add :
  ~ (forall x, wadd x (wmul W0 (winv W0)) = wmul W0 (winv W0)).
Proof.
  intros H. destruct model_fails as [_ [_ [_ F]]]. apply F. exact (H W1).
Qed.

Theorem model_not_wheel_inv_mul :
  ~ (forall x y, winv (wmul x y) = wmul (winv y) (winv x)).
Proof.
  intros H. destruct model_fails as [F _]. apply F. exact (H W0 Wbot).
Qed.

Theorem wmul_zero_absorbs : forall x, wmul W0 x = W0 /\ wmul x W0 = W0.
Proof. intros []; split; reflexivity. Qed.

(** In any structure that satisfies (8) with an absorbing zero, every
    element is zero: 0/0 = 0 * /0 = 0, so x + 0 = 0. *)
Theorem absorbing_zero_forces_trivial :
  forall {H : Type} (zero : H) (add mul : H -> H -> H) (inv : H -> H),
    (forall x, add x zero = x) ->
    (forall x, mul zero x = zero) ->
    (forall x, add x (mul zero (inv zero)) = mul zero (inv zero)) ->
    forall x, x = zero.
Proof.
  intros H zero add mul inv Hid Habs Hbot x.
  specialize (Hbot x). rewrite Habs, Hid in Hbot. exact Hbot.
Qed.

Theorem model_bottom_is_zero : wbot = W0 /\ wbot <> Wbot.
Proof. split; [reflexivity | discriminate]. Qed.

Theorem wadd_bot_absorbs : forall x, wadd Wbot x = Wbot /\ wadd x Wbot = Wbot.
Proof. intros []; split; reflexivity. Qed.

Theorem wmul_bot_not_absorbing : wmul W0 Wbot <> Wbot.
Proof. discriminate. Qed.
