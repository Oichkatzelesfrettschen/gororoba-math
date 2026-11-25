(** Chunked accumulation: the trie is walked completely after each chunk of insertions. *)
From Stdlib Require Import ZArith List NArith Bool.
Require Import HilbertCellCertificate K2CofactorCertificate.
Import ListNotations.
Open Scope Z_scope.

Require Import K2FactoredBenchBase.

Fixpoint go (cs : list (list (positive * Z))) (t : tr) : tr :=
  match cs with
  | [] => t
  | c :: cs' =>
    let t' := addall t c in
    match tall 32029 t' with true => go cs' t' | false => go cs' t' end
  end.

Lemma bench_forced : tall 32029 (go chunks TL) = true.
Proof. vm_compute. reflexivity. Qed.
