(** Text tables of the two Rocq sign functions that SignBridge.v proves equal:
    CdTowerBasisSign.sigma of rocq/quantum and open_cube_sign of SignBridge.v,
    which reads the sign law of rocq/open. Row p and column q hold the sign
    of e_p * e_q at level k, in the layout of lean/audit/SignTable.lean:
    2^k lines of 2^k space-separated entries 1 or -1, the entry ? marking a
    value other than 1 or -1. ci/compare_signs.sh appends, for each level K,
    the lines `Eval vm_compute in sigma_text K.` and
    `Eval vm_compute in open_text K.` to a copy of this file, compiles the
    copy against a compiled build tree of rocq/ and compares the printed
    strings with the Lean and Python tables. The gate admits under rocq/
    only project-listed sources, so this source stays under ci/. *)

From Stdlib Require Import ZArith List String Ascii.
Require SignBridge.

Local Open Scope string_scope.

Definition sign_text (s : Z) : string :=
  if Z.eqb s 1 then "1" else if Z.eqb s (-1) then "-1" else "?".

Definition newline : string := String (Ascii.ascii_of_nat 10) EmptyString.

Definition table_text (t : list (list Z)) : string :=
  String.concat newline (map (fun row => String.concat " " (map sign_text row)) t).

Definition sigma_text (k : nat) : string :=
  table_text (SignBridge.table (SignBridge.sigma k) k).

Definition open_text (k : nat) : string :=
  table_text (SignBridge.table (fun p q => SignBridge.open_cube_sign k p q) k).
