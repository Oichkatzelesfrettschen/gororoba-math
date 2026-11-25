(** Product counts of the factored check of quadric 8: the sizes of each stage of [check_factored]. *)

From Stdlib Require Import ZArith List NArith.
Require Import HilbertCellCertificate K2CofactorCertificate K2CofactorFactored K2CofactorE8barVBHeader.
Require Import K2CofactorE8barVBf08.
Import ListNotations.
Open Scope Z_scope.

Definition cert8 : kcert :=
  decode_cert 16 8 (length k2_J + 8 * tri (length k2_G)) k2_data_08.
Definition cofs8 := k_cofs cert8.
Definition cJ8 := firstn (length k2_J) cofs8.
Definition Bc8 : list poly :=
  stage1 8 (seq 0 8) (chunk (tri (length k2_G)) 8 (skipn (length k2_J) cofs8)) (repeat [] (tri (length k2_G))).
Definition Bs8 := map (norm_poly 32029) Bc8.
Definition hs8 := hlist 32029 8 k2_G Bs8.
Definition f8 := subst_q 8 k2_G (nth 7 k2_quadrics []).
Definition sum (l : list nat) : nat := fold_left Nat.add l 0%nat.

(* stage 0: u f (u has one term) and the J part *)
Eval vm_compute in (length (k_u cert8), length f8).
Eval vm_compute in sum (map (fun c => length c) cJ8).
Eval vm_compute in sum (map (fun jc => (length (fst jc) * length (snd jc))%nat) (combine cJ8 k2_J)).
(* stage 1: unnormalized and normalized B, products of the sums H_g *)
Eval vm_compute in (sum (map (fun c => length c) Bc8), sum (map (fun c => length c) Bs8)).
Eval vm_compute in
  sum (map (fun g => let k := length g in k) (map (fun h => pmul h (one_poly 8)) k2_G)).
Eval vm_compute in map (fun gh => length (snd gh)) hs8.
Eval vm_compute in (sum (map (fun gh => (length (fst gh) * length (snd gh))%nat) hs8)).
(* stage 1 products: |Gone_h| * |B| over the groups *)
Eval vm_compute in
  (fix go (G : list poly) (Bs : list poly) : nat :=
     match G with
     | [] => 0%nat
     | g :: G' =>
       (sum (map (fun hb => (length (fst hb) * length (snd hb))%nat)
         (combine (map (fun h => pmul h (one_poly 8)) G) (firstn (length G) Bs))) + go G' (skipn (length G) Bs))%nat
     end) k2_G Bs8.
