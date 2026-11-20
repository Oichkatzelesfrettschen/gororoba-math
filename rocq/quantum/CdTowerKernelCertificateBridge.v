(** The kernel of left multiplication as a free module on certified vectors: the Rocq bridge of the Lean module
    lean/GororobaMath/CayleyDickson/KernelCertificate.lean.

    Convention: the tower, product and conjugation of CdTowerRing.v,
    (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)) and conj (a, b) = (conj a, -b), with the identity as the
    conjugation of the coefficients. The Lean tower has the same product and star.

    The functor KernelCertificateBridge restates kernel_free_basis of the functor KernelCertificate at the
    ring homomorphism H from A to B, with the hypotheses of its section as arguments in their order:
    the vectors annihilate the source element y and the splitting of d times a basis element.
    The duality of the functionals with the vectors at d is not a hypothesis of this theorem: it is the hypothesis of the
    independence theorem combination_zero_coefficients of CdTowerKernelCertificate.v. The conclusion is that, when h(d) has an
    inverse in B, an element z lies in the kernel of left multiplication by the image of y exactly when z is the
    combination of the vectors with the coefficients inverse times the pairing of the functionals with z. This is
    Tower.ker_mulLeft_basis_of_certificate at a ring in which d is a unit.

    Substituted values: R := B for the target ring with the unit d replaced by h(d) and its inverse, the vectors v and functionals g the Rocq lists vectors and functionals below n, and back the Rocq list back.

    The Rocq statement is narrower than the Lean one: it states that the kernel is spanned by the vectors, by the explicit
    combination formula, where Lean states a Basis of the kernel submodule, whose independence is the separate
    theorem combination_zero_coefficients, the families are indexed by natural numbers below n, where Lean takes
    Fin n, and the hypotheses live over a source ring A and are transported along H, where Lean takes one ring.
    IntegerKernelCertificateBridge instantiates the functor at the identity of the integers. *)

Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange CdTowerKernelCertificate CdTowerDomain.

Module KernelCertificateBridge (A B : CommutativeRing) (H : RingHom A B).
Module KC := KernelCertificate A B H.
Import KC KC.BC.

Theorem kernel_free_basis k n (y : TA.cd k) (d : A.t) (back functionals vectors : nat -> TA.cd k)
  (vectors_annihilated : forall j, (j < n)%nat -> TA.mul k y (vectors j) = TA.zero k)
  (splitting_on_basis : forall i, (i < Nat.pow 2 k)%nat ->
    TA.scale k d (SA.basis k i) =
    TA.add k (source_map k back (TA.mul k y (SA.basis k i))) (source_comb k n functionals vectors (SA.basis k i)))
  (inverse : B.t) (inverse_law : B.mul (H.h d) inverse = B.one) :
  forall z,
  TB.mul k (tmap k y) z = TB.zero k <->
  z = SB.tsum k n (fun j => TB.scale k (B.mul inverse (target_pair k (tmap k (functionals j)) z)) (tmap k (vectors j))).
Proof.
  exact (KC.kernel_free_basis k n y d back functionals vectors vectors_annihilated splitting_on_basis
    inverse inverse_law).
Qed.

End KernelCertificateBridge.

Module IntegerToIntegerHom := IntegerHom ZDomain.
Module IntegerKernelCertificateBridge := KernelCertificateBridge IntegerRing ZDomain IntegerToIntegerHom.
