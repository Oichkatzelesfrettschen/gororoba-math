(** Current accumulation: left-nested fold_left of the insertions. *)
From Stdlib Require Import ZArith List NArith Bool.
Require Import HilbertCellCertificate K2CofactorCertificate.
Import ListNotations.
Open Scope Z_scope.

Require Import K2FactoredBenchBase.
Lemma bench_left : tall 32029 (addall TL jobs) = true.
Proof. vm_compute. reflexivity. Qed.
