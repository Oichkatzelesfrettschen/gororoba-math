(** The kernel of left multiplication by the W8 point of level 5 as a free module on 8 certified vectors: the
    instance bridge of the Lean theorem Tower.ker_mulLeft_basis_of_certificate of
    lean/GororobaMath/CayleyDickson/KernelCertificate.lean at the tables of CdTowerCanonicalKernels.v.

    Convention: the tower, product and conjugation of CdTowerRing.v,
    (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)) and conj (a, b) = (conj a, -b), with the identity as the
    conjugation of the coefficients. The Lean tower has the same product and star.

    Substituted values: R := D, a commutative ring that receives the integers by the homomorphism h of
    IntegerHom, k := 5, n := 8, y := the image of W8_point, v j := the image of W8_vectors j,
    g j := the pairing with the image of W8_functionals j, back := the map of W8_back, and d := h(2), a unit of D
    by the hypothesis that names its inverse. The hypotheses hv, hg and hs of the Lean theorem are the lemmas
    W8_vectors_annihilated, W8_functionals_dual and W8_splitting_on_basis of CanonicalKernels, each decided by
    evaluation over the integers and carried to D by the base change of CdTowerKernelCertificate.v.

    The Lean conclusion is a basis of the kernel whose members are the vectors. The functor
    CanonicalKernelsBridge states it as two theorems: W8_kernel_free_basis, an element lies in the kernel
    exactly when it is the combination of the 8 vectors with the coefficients inverse times the pairings, and
    W8_combination_zero_coefficients, a combination of the 8 vectors that vanishes has every coefficient
    annihilated by h(2), hence zero where h(2) has an inverse.

    The Rocq statement is narrower than the Lean one: it states spanning by the explicit combination formula
    and independence as separate theorems where Lean states one Basis of the kernel submodule, and the
    families are indexed by natural numbers below 8 where Lean takes Fin 8. *)

From Stdlib Require Import BinInt.
Require Import CdTowerRing CdTowerRingBasis CdTowerRingBaseChange CdTowerKernelCertificate.
Require Import CdTowerCanonicalKernels.

Module CanonicalKernelsBridge (D : CommutativeRing).
Module CK := CanonicalKernels D.
Import CK CK.KC CK.KC.BC.

Theorem W8_kernel_free_basis (inverse : D.t) : D.mul (CK.H.h 2%Z) inverse = D.one -> forall z,
  TB.mul 5 (tmap 5 W8_point) z = TB.zero 5 <->
  z = SB.tsum 5 8 (fun j => TB.scale 5 (D.mul inverse (target_pair 5 (tmap 5 (W8_functionals j)) z))
                                  (tmap 5 (W8_vectors j))).
Proof. exact (CK.W8_kernel_free_basis inverse). Qed.

Theorem W8_combination_zero_coefficients (a : nat -> D.t) :
  SB.tsum 5 8 (fun j => TB.scale 5 (a j) (tmap 5 (W8_vectors j))) = TB.zero 5 ->
  forall l, (l < 8)%nat -> D.mul (CK.H.h 2%Z) (a l) = D.zero.
Proof. exact (CK.W8_combination_zero_coefficients a). Qed.

End CanonicalKernelsBridge.
