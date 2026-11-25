(** Balanced accumulation: divide and conquer over the job list, pointwise merge of the halves. *)
From Stdlib Require Import ZArith List NArith Bool.
Require Import HilbertCellCertificate K2CofactorCertificate.
Import ListNotations.
Open Scope Z_scope.

Require Import K2FactoredBenchBase.

Fixpoint tmerge (a b : tr) : tr :=
  match a, b with
  | TL, _ => b
  | _, TL => a
  | TN l1 v1 r1, TN l2 v2 r2 => TN (tmerge l1 l2) (v1 + v2) (tmerge r1 r2)
  end.

Definition leaf (j : positive * Z) : tr := tadd TL (fst j) (snd j).

Fixpoint dc (d : nat) (js : list (positive * Z)) : tr * list (positive * Z) :=
  match d with
  | O => match js with [] => (TL, []) | j :: js' => (leaf j, js') end
  | S d' =>
    let (t1, r1) := dc d' js in
    let (t2, r2) := dc d' r1 in
    (tmerge t1 t2, r2)
  end.

Lemma bench_bal : tall 32029 (fst (dc 16 jobs)) = true.
Proof. vm_compute. reflexivity. Qed.
