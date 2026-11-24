(** * C-1630: the basis-associator coefficient tensor of the 16-dimensional
    Cayley-Dickson algebra, and the uniform associator baseline.

    Convention.  Basis elements are e_0, ..., e_15 with e_0 = 1.  The product
    is e_p * e_q = sed_sign p q * e_{p XOR q}, where [sed_sign] of
    [C1467_XORSignCocycle] is the literal 16 x 16 table whose rows
    [sed_sign_table_correct] binds to the bounded Cayley-Dickson recurrence
    [cd_sign_fuel 5 16], which reads as the sign recurrence of [cd_sign]
    of gororoba_quantum/cd_core.py; ci/compare_box_kite_census.sh runs this
    table against cd_core.py.  Indices are natural numbers whose bits
    are the XOR labels.  For basis elements the two association orders land
    on the same component e_{i XOR j XOR k}:
      (e_i e_j) e_k = lsign i j k * e_{i XOR j XOR k},
      e_i (e_j e_k) = rsign i j k * e_{i XOR j XOR k},
    with lsign i j k = s(i,j) s(i XOR j, k) and
    rsign i j k = s(j,k) s(i, j XOR k).  The associator coefficient is
    [acoef] = lsign - rsign, and [omega] = lsign * rsign is -1 exactly
    where the triple fails to associate (the [omega] of
    scripts/box_kite_census.py in gororoba-quantum, the product of
    triple_sign of cd_core.py; ci/compare_box_kite_census.sh compares
    [lsign] and [rsign] with triple_sign on the 4096 ordered triples and
    rejects a mutated [rsign]).

    Rows answered.
    - gororoba-open C-1630: [acoef_values] (every coefficient in
      {-2, 0, +2}), [acoef_census] (2248 zeros, 924 of +2, 924 of -2 over
      the 4096 ordered triples), [acoef_component_counts] (the scalar e_0
      receives 0 nonzero terms, e_8 receives 168, each other imaginary
      component 120), [quaternion_tensor_vanishes] and
      [octonion_tensor_balanced] (the tensor restricted to indices below 4
      vanishes; restricted to indices below 8 it has 168 nonzero terms, 84
      of each sign).  [sign_restrict_level3] and [sign_restrict_level2]
      bind the restricted table to the level-3 and level-2 recurrences.
    - gororoba-quantum docs/evidence/box_kite_census/README.md line 55
      (associator uniform baseline): [omega_values], [omega_negative_count]
      (1848 of the 4096 ordered triples have omega = -1),
      [uniform_baseline] (the mean of omega is 25/256) and
      [p_control_one] (1848/4096 = 231/512).

    All results are decided by evaluation; counts above 5000 are in N. *)

From Stdlib Require Import Arith PeanoNat Bool List ZArith QArith.
From OpenGororobaVerified Require Import C1467_XORSignCocycle.
Import ListNotations.

Open Scope Z_scope.

Definition lsign (i j k : nat) : Z :=
  sed_sign i j * sed_sign (Nat.lxor i j) k.

Definition rsign (i j k : nat) : Z :=
  sed_sign j k * sed_sign i (Nat.lxor j k).

Definition acoef (i j k : nat) : Z := lsign i j k - rsign i j k.

Definition omega (i j k : nat) : Z := lsign i j k * rsign i j k.

Definition xor3 (i j k : nat) : nat := Nat.lxor (Nat.lxor i j) k.

Definition cnt {A : Type} (f : A -> bool) (l : list A) : N :=
  fold_left (fun a x => if f x then N.succ a else a) l 0%N.

Definition triples_below (m : nat) : list (nat * nat * nat) :=
  flat_map (fun i => flat_map (fun j => map (fun k => (i, j, k)) (seq 0 m))
                              (seq 0 m)) (seq 0 m).

Definition triples : list (nat * nat * nat) := triples_below 16.

Definition nonzero_at (t : nat * nat * nat) : bool :=
  let '(i, j, k) := t in negb (Z.eqb (acoef i j k) 0).

(** The ordered triples are the 16^3 = 4096 of the domain. *)
Theorem triples_count : cnt (fun _ => true) triples = 4096%N.
Proof. vm_compute. reflexivity. Qed.

Theorem acoef_values :
  forallb (fun t => let '(i, j, k) := t in
             Z.eqb (acoef i j k) (-2) || Z.eqb (acoef i j k) 0
             || Z.eqb (acoef i j k) 2) triples = true.
Proof. vm_compute. reflexivity. Qed.

(** (zeros, +2, -2) over the 4096 ordered triples. *)
Theorem acoef_census :
  (cnt (fun t => let '(i, j, k) := t in Z.eqb (acoef i j k) 0) triples,
   cnt (fun t => let '(i, j, k) := t in Z.eqb (acoef i j k) 2) triples,
   cnt (fun t => let '(i, j, k) := t in Z.eqb (acoef i j k) (-2)) triples)
  = (2248%N, 924%N, 924%N).
Proof. vm_compute. reflexivity. Qed.

(** Nonzero terms landing on e_n, for n = 0, ..., 15. *)
Definition component_counts : list N :=
  map (fun n => cnt (fun t => let '(i, j, k) := t in
                       Nat.eqb (xor3 i j k) n && nonzero_at t) triples)
      (seq 0 16).

Theorem acoef_component_counts :
  component_counts =
  [0; 120; 120; 120; 120; 120; 120; 120; 168; 120; 120; 120; 120; 120; 120; 120]%N.
Proof. vm_compute. reflexivity. Qed.

(** Restriction of the level-4 table to the first 2^m labels is the
    level-m table. *)
Theorem sign_restrict_level3 :
  forallb (fun i => forallb (fun j =>
      Z.eqb (sed_sign i j) (cd_sign_fuel 4 8 i j)) (seq 0 8)) (seq 0 8) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem sign_restrict_level2 :
  forallb (fun i => forallb (fun j =>
      Z.eqb (sed_sign i j) (cd_sign_fuel 3 4 i j)) (seq 0 4)) (seq 0 4) = true.
Proof. vm_compute. reflexivity. Qed.

Theorem quaternion_tensor_vanishes :
  cnt nonzero_at (triples_below 4) = 0%N.
Proof. vm_compute. reflexivity. Qed.

Theorem octonion_tensor_balanced :
  (cnt nonzero_at (triples_below 8),
   cnt (fun t => let '(i, j, k) := t in Z.eqb (acoef i j k) 2)
       (triples_below 8),
   cnt (fun t => let '(i, j, k) := t in Z.eqb (acoef i j k) (-2))
       (triples_below 8))
  = (168%N, 84%N, 84%N).
Proof. vm_compute. reflexivity. Qed.

(** Uniform associator baseline. *)
Theorem omega_values :
  forallb (fun t => let '(i, j, k) := t in
             Z.eqb (omega i j k) 1 || Z.eqb (omega i j k) (-1)) triples = true.
Proof. vm_compute. reflexivity. Qed.

Theorem omega_negative_count :
  cnt (fun t => let '(i, j, k) := t in Z.eqb (omega i j k) (-1)) triples
  = 1848%N.
Proof. vm_compute. reflexivity. Qed.

Definition omega_sum : Z :=
  fold_left (fun a t => let '(i, j, k) := t in a + omega i j k) triples 0.

Theorem omega_sum_value : omega_sum = 400.
Proof. vm_compute. reflexivity. Qed.

Open Scope Q_scope.

(** The mean of omega over the 4096 ordered triples is 25/256. *)
Theorem uniform_baseline : (omega_sum # 4096) == 25 # 256.
Proof. vm_compute. reflexivity. Qed.

(** The fraction of triples with omega = -1 is 231/512. *)
Theorem p_control_one :
  (Z.of_N (cnt (fun t => let '(i, j, k) := t in Z.eqb (omega i j k) (-1))
               triples) # 4096) == 231 # 512.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions acoef_values.
Print Assumptions acoef_census.
Print Assumptions acoef_component_counts.
Print Assumptions quaternion_tensor_vanishes.
Print Assumptions octonion_tensor_balanced.
Print Assumptions omega_negative_count.
Print Assumptions uniform_baseline.
Print Assumptions p_control_one.
