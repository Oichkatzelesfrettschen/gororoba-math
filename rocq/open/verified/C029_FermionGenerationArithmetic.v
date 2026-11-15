(** * C-029: S3 order arithmetic and two non-closure computations.

    Convention: octonions are CDOct = (CDQuat, CDQuat) and sedenions are
    CDSed = (CDOct, CDOct) with the Cayley-Dickson product sed_mul of
    Sedenion.v.  The three maps from the octonions into the sedenions are
    the low-half embedding x |-> (x, 0), the high-half embedding
    x |-> (0, x) and the diagonal embedding x |-> (x, x).

    PROVED:
    - the order of S3 is 3! = 6, and 6 = 3 * 2 (orbit size times
      stabilizer size);
    - sed_mul of the high-half unit with itself is the low-half element
      -1, and sed_mul of the diagonal unit with itself is the high-half
      element 2.

    The last two computations show that the images of the high-half and
    diagonal embeddings are not closed under sed_mul, so they are not
    subalgebras of the sedenions; only the low-half image is closed
    (C028_lo_subalgebra_closed).  No theorem here counts octonionic
    subalgebras, relates S3 to them, or relates the number 3 to fermion
    generations. *)

From Stdlib Require Import Arith.
From OpenGororoba Require Import Prelude CayleyDicksonAlgebra Sedenion.

(** S3 has order 3! = 6. *)
Theorem C029_s3_order : (1 * 2 * 3 = 6)%nat.
Proof. reflexivity. Qed.

(** Orbit size 3 times stabilizer size 2 equals the group order 6. *)
Theorem C029_orbit_stabilizer : (6 = 3 * 2)%nat.
Proof. reflexivity. Qed.

(** * Embeddings of the octonions into the sedenions. *)

Definition sed_embed_hi (x : CDOct) : CDSed := mkSed oct_zero x.

Definition sed_embed_diag (x : CDOct) : CDSed := mkSed x x.

Open Scope R_scope.

(** The octonion unit 1 and the octonions -1 and 2 as multiples of it. *)
Definition oct_unit : CDOct := mkOct (mkQuat 1 0 0 0) quat_zero.
Definition oct_minus_one : CDOct := mkOct (mkQuat (-1) 0 0 0) quat_zero.
Definition oct_two : CDOct := mkOct (mkQuat 2 0 0 0) quat_zero.

(** (0, 1) * (0, 1) = (-1, 0): the square of the high-half unit lies in the
    low half. *)
Theorem C029_hi_unit_square :
  sed_mul (sed_embed_hi oct_unit) (sed_embed_hi oct_unit) =
  mkSed oct_minus_one oct_zero.
Proof.
  cbv [sed_embed_hi oct_unit oct_minus_one sed_mul oct_mul oct_conj oct_zero
       quat_mul quat_add quat_neg quat_conj quat_zero
       sed_lo sed_hi oct_lo oct_hi qa qb qc qd].
  f_equal; f_equal; f_equal; ring.
Qed.

(** (1, 1) * (1, 1) = (0, 2): the square of the diagonal unit lies in the
    high half. *)
Theorem C029_diag_unit_square :
  sed_mul (sed_embed_diag oct_unit) (sed_embed_diag oct_unit) =
  mkSed oct_zero oct_two.
Proof.
  cbv [sed_embed_diag oct_unit oct_two sed_mul oct_mul oct_conj oct_zero
       quat_mul quat_add quat_neg quat_conj quat_zero
       sed_lo sed_hi oct_lo oct_hi qa qb qc qd].
  f_equal; f_equal; f_equal; ring.
Qed.
