(** One sign function in four Rocq spellings. CdTowerBasisSign.sigma (the
    quantum tree, Z-valued, top bit first) equals
    OpenGororoba.M3IsAssociator.cd_sign_fuel at dimension 2^k for every
    fuel and every index pair, by induction on k: the two recursions take
    the same four top-bit branches with the same arguments, so no index
    bound enters. It equals OpenGororobaVerified.C1474_FuelAdequacy.cd_sign_fuel
    (the function StiefelWitnessInvertible.v reads) whenever the fuel exceeds
    k, since that spelling returns 0 on empty fuel. Through numeric_cube_sign
    of the open tree, the Boolean law sign_exponent on cube_decode p and
    cube_decode q is sigma k p q for p, q < 2^k, and through
    cd_sign_returns_sigma of the quantum tree the Python-subset semantics of
    cd_core.cd_sign returns that same value. The tables at levels 3 to 5 are
    printed for comparison with cd_core.cd_sign and Lean Tower.sign. *)

From Stdlib Require Import ZArith Lia List Bool.
From OpenGororoba Require M3IsAssociator SchreierSignCode CDSignNumericCorrespondence CDAssociatorDoubling.
From OpenGororobaVerified Require C1474_FuelAdequacy.
Require CdTowerBasisSign CdSignPythonSemantics.

Locate Library CdTowerBasisSign.
Locate Library OpenGororoba.M3IsAssociator.
Locate Library OpenGororobaVerified.C1474_FuelAdequacy.

Abbreviation sigma := CdTowerBasisSign.sigma.
Abbreviation open_fuel_sign := OpenGororoba.M3IsAssociator.cd_sign_fuel.
Abbreviation verified_fuel_sign := OpenGororobaVerified.C1474_FuelAdequacy.cd_sign_fuel.
Definition open_cube_sign (k p q : nat) : Z :=
  (OpenGororoba.CDAssociatorDoubling.phase_sign
     (OpenGororoba.SchreierSignCode.sign_exponent k
        (OpenGororoba.CDSignNumericCorrespondence.cube_decode k p)
        (OpenGororoba.CDSignNumericCorrespondence.cube_decode k q))).

Lemma half_power j : Nat.div (Nat.pow 2 (S j)) 2 = Nat.pow 2 j.
Proof. rewrite Nat.pow_succ_r', Nat.mul_comm. apply Nat.div_mul. lia. Qed.

(** The open fuel spelling returns 1 on empty fuel, so equality needs
    fuel at least k, the bound of numeric_cube_sign. *)
Theorem open_fuel_sign_sigma k : forall fuel p q, (k <= fuel)%nat ->
  open_fuel_sign fuel (Nat.pow 2 k) p q = sigma k p q.
Proof.
  induction k as [|j IH]; intros fuel p q enough.
  - destruct fuel; reflexivity.
  - destruct fuel as [|fuel]; [lia|].
    cbn [OpenGororoba.M3IsAssociator.cd_sign_fuel]. rewrite half_power, CdTowerBasisSign.sigma_unfold.
    replace (Nat.eqb (Nat.pow 2 j) 0) with false
      by (symmetry; apply Nat.eqb_neq; apply Nat.pow_nonzero; lia).
    unfold CdTowerBasisSign.unit_conj.
    destruct (Nat.ltb p (Nat.pow 2 j)), (Nat.ltb q (Nat.pow 2 j)); cbn [andb negb];
      try destruct (Nat.eqb q 0); try destruct (Nat.eqb (q - Nat.pow 2 j) 0);
      rewrite ?IH by lia; try reflexivity; ring.
Qed.

Theorem verified_fuel_sign_sigma k : forall fuel p q, (k < fuel)%nat ->
  verified_fuel_sign fuel (Nat.pow 2 k) p q = sigma k p q.
Proof.
  induction k as [|j IH]; intros fuel p q enough.
  - destruct fuel as [|fuel]; [lia|]. reflexivity.
  - destruct fuel as [|fuel]; [lia|].
    assert (dimension : Nat.pow 2 (S j) = S (S (Nat.pow 2 (S j) - 2))).
    { pose proof (Nat.pow_le_mono_r 2 1 (S j) ltac:(lia) ltac:(lia)). simpl in *. lia. }
    cbn [OpenGororobaVerified.C1474_FuelAdequacy.cd_sign_fuel].
    rewrite dimension. cbv zeta. rewrite <- dimension, half_power, CdTowerBasisSign.sigma_unfold.
    unfold CdTowerBasisSign.unit_conj.
    destruct (Nat.ltb p (Nat.pow 2 j)), (Nat.ltb q (Nat.pow 2 j));
      try destruct (Nat.eqb q 0); try destruct (Nat.eqb (q - Nat.pow 2 j) 0);
      rewrite ?IH by lia; try reflexivity; ring.
Qed.

Theorem open_cube_sign_sigma k p q : (p < Nat.pow 2 k)%nat -> (q < Nat.pow 2 k)%nat ->
  open_cube_sign k p q = sigma k p q.
Proof.
  intros Hp Hq. unfold open_cube_sign. rewrite <- (open_fuel_sign_sigma k k p q (le_n k)).
  rewrite <- (OpenGororoba.CDSignNumericCorrespondence.cube_encode_decode k p Hp) at 2.
  rewrite <- (OpenGororoba.CDSignNumericCorrespondence.cube_encode_decode k q Hq) at 2.
  symmetry. apply OpenGororoba.CDSignNumericCorrespondence.numeric_cube_sign. lia.
Qed.

(** The Python-subset semantics of cd_core.cd_sign returns the open sign. *)
Theorem python_cd_sign_returns_open_sign k p q fuel : (k + 7 <= fuel)%nat ->
  (p < Nat.pow 2 k)%nat -> (q < Nat.pow 2 k)%nat ->
  CdSignPythonSemantics.run fuel CdSignPythonSemantics.cd_sign_ast
    (Z.of_nat (Nat.pow 2 k) :: Z.of_nat p :: Z.of_nat q :: nil) =
  CdSignPythonSemantics.Returned (open_cube_sign k p q).
Proof.
  intros Hf Hp Hq. rewrite open_cube_sign_sigma by assumption.
  apply CdSignPythonSemantics.cd_sign_returns_sigma; assumption.
Qed.

Print Assumptions open_fuel_sign_sigma.
Print Assumptions verified_fuel_sign_sigma.
Print Assumptions open_cube_sign_sigma.
Print Assumptions python_cd_sign_returns_open_sign.

(** Tables, row p and column q, for the comparison with Python and Lean. *)
Definition table (f : nat -> nat -> Z) (k : nat) : list (list Z) :=
  map (fun p => map (fun q => f p q) (seq 0 (Nat.pow 2 k))) (seq 0 (Nat.pow 2 k)).

Definition tables_agree (k : nat) : bool :=
  let reference := table (sigma k) k in
  let same other := forallb (fun pair => forallb (fun entry => Z.eqb (fst entry) (snd entry))
                       (combine (fst pair) (snd pair))) (combine reference other) in
  same (table (fun p q => open_cube_sign k p q) k) &&
  same (table (open_fuel_sign k (Nat.pow 2 k)) k) &&
  same (table (verified_fuel_sign (S k) (Nat.pow 2 k)) k).

Example tables_agree_three_to_six : tables_agree 3 && tables_agree 4 && tables_agree 5 && tables_agree 6 = true.
Proof. vm_compute. reflexivity. Qed.

Open Scope Z_scope.
Set Printing Depth 1000000.
Eval vm_compute in table (sigma 3) 3.
Eval vm_compute in table (sigma 4) 4.
Eval vm_compute in table (sigma 5) 5.
Eval vm_compute in table (fun p q => open_cube_sign 3 p q) 3.
Eval vm_compute in table (fun p q => open_cube_sign 4 p q) 4.
Eval vm_compute in table (fun p q => open_cube_sign 5 p q) 5.
