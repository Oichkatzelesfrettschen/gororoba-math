(** The columns of the 24 x 6 arc matrix of point 1 of the W8 to N- fiber are independent: the instance bridge of
    the Lean theorem Matrix.linearIndependent_cols_of_mul_eq_smul_one of
    lean/GororobaMath/CayleyDickson/Certificates.lean at the tables of A5W8ArcMatrixRanks.v.

    Convention: a matrix is a table of rows over the Gaussian integers, read through the entry function
    LC.entry of MatrixLeftInverseCertificate.v and carried to a commutative ring D by a ring homomorphism H;
    a column relation is a family a of coefficients of D, indexed below the column count, whose combination of
    the columns vanishes in every row (LC.relation).

    Substituted values: S := D, m := the 24 rows, n := the 6 columns, M := the image of
    w8_nm_linear_point1_matrix, L := the image of the sparse table w8_nm_linear_point1_left,
    d := h(w8_nm_linear_point1_d). The hypothesis h : L * M = d • 1 of the Lean theorem is the lemma
    w8_nm_linear_point1_left_inverse, decided by evaluation over the Gaussian integers, and hd, that d is left
    regular, is the first hypothesis below.

    The Rocq statement is narrower than the Lean one: it states that every column relation has zero
    coefficients, with the columns indexed by natural numbers below 6, where Lean states LinearIndependent of
    the column family. *)

Require Import CdTowerRing CdTowerRingBaseChange GaussianIntegerHom MatrixLeftInverseCertificate.
Require Import A5W8ArcMatrixRanks.

Module W8ArcMatrixRanksBridge (D : CommutativeRing) (H : RingHom GaussianIntegers D).
Module R := W8ArcMatrixRanks D H.
Import W8ArcTables.

Theorem w8_nm_linear_point1_columns_independent (a : nat -> D.t) :
  (forall x, D.mul (H.h w8_nm_linear_point1_d) x = D.zero -> x = D.zero) ->
  R.LC.relation 24 6 (R.LC.entry w8_nm_linear_point1_matrix) a -> forall l, (l < 6)%nat -> a l = D.zero.
Proof. exact (R.w8_nm_linear_point1_columns_independent a). Qed.

End W8ArcMatrixRanksBridge.
