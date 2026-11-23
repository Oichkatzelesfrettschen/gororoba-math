(** An ideal holds the eight W8 forms f(z), f(z') exactly when it holds their real and imaginary parts: the
    instance bridge of the Lean theorem Ideal.add_mul_mem_and_sub_mul_mem_iff of
    lean/GororobaMath/CayleyDickson/Ideals.lean at the forms of CdTwistedProduct.v.

    Convention: D is a commutative ring with an element i, i i = -1, and an inverse of 2 (TwistedRing); X k is
    the coordinate k of the 32 coordinates, the twisted coordinates are z_k = X k + i X (16 + k) and
    z'_k = X k - i X (16 + k), and an ideal is a predicate closed under sums and multiples (is_ideal).

    Substituted values: S := D, i := D.i with hi := D.i_squared, h2 := the unit 2 with inverse D.inv2, and the
    theorem applied to four pairs (re, im): (X 0, X 16), (X 8, X 24), (eq_uv_re, eq_uv_im) and
    (eq_w_re, eq_w_im), whose sums re + i im and differences re - i im are the eight forms of the left side by
    eq_uv_twisted, eq_uv_twisted_conjugate, eq_w_twisted and eq_w_twisted_conjugate of the functor Twisted.

    The Rocq statement is narrower than the Lean one: the ideal is a predicate with the two closure laws, where
    Lean takes an Ideal of the ring. *)

Require Import CdTwistedProduct.

Module TwistedProductBridge (D : TwistedRing).
Module T := Twisted D.

Theorem W8_ideal_exchange (X : nat -> D.t) (I : D.t -> Prop) :
  T.is_ideal I ->
  (I (D.add (X 0) (D.mul D.i (X 16))) /\ I (D.sub (X 0) (D.mul D.i (X 16))) /\
   I (D.add (X 8) (D.mul D.i (X 24))) /\ I (D.sub (X 8) (D.mul D.i (X 24))) /\
   I (T.eq_uv (T.zeta X)) /\ I (T.eq_uv (T.zeta_conjugate X)) /\
   I (T.eq_w (T.zeta X)) /\ I (T.eq_w (T.zeta_conjugate X))) <->
  (I (X 0) /\ I (X 16) /\ I (X 8) /\ I (X 24) /\
   I (T.eq_uv_re X) /\ I (T.eq_uv_im X) /\ I (T.eq_w_re X) /\ I (T.eq_w_im X)).
Proof. exact (T.W8_ideal_exchange X I). Qed.

End TwistedProductBridge.
