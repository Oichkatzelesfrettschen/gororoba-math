(** Insertion jobs of the accumulation benchmark: 65,536 (key, value) pairs into 4,096 keys, each key hit
    sixteen times with values that sum to zero, in sixteen chunks of 4,096 jobs. *)

From Stdlib Require Import ZArith List NArith Bool.
Require Import HilbertCellCertificate K2CofactorCertificate.
Import ListNotations.
Open Scope Z_scope.

Definition D16 : list nat := seq 0 16.

Definition vals : list Z := [1;2;3;4;5;6;7;8;-1;-2;-3;-4;-5;-6;-7;-8].

Definition chunk_of (v : Z) : list (positive * Z) :=
  flat_map (fun a => flat_map (fun b => map (fun c => (enc [a;b;c;0;0;0;0;0]%nat, v)) D16) D16) D16.

Definition chunks : list (list (positive * Z)) := map chunk_of vals.

Definition jobs : list (positive * Z) := flat_map (fun c => c) chunks.

Definition addall (t : tr) (js : list (positive * Z)) : tr :=
  fold_left (fun t j => tadd t (fst j) (snd j)) js t.
