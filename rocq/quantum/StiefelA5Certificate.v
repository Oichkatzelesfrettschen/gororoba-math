(** The Pfaffian identity Pf A(z, t) = -(z.t) Q(z) G(z) for the bordered A_5 matrix, as a certificate.

    Convention: the product of A_4 is the doubling (a, b)(c, d) = (ac - conj(d) b, da + b conj(c)) of
    CdTowerRing.v, computed here on coordinate lists by cdmul; sgn16 a b is the e_a coefficient of
    e_(a xor b) e_b. cdmul is a computing device only: StiefelA5Transport.v ties the matrix it builds to the
    tower product, so no statement rests on cdmul agreeing with another implementation.
    A(z, t) is the 16 x 16 matrix with A 0 b = -t_b, A a 0 = t_a and A a b = sgn16 a b z_(a xor b)
    for a, b >= 1, a <> b; z_k is polynomial variable k (k = 1..15) and t_k is variable 15 + k.
    Q = z.z, U = z_1..z_7 squared, V = z_9..z_15 squared, W = (z_1..z_7).(z_9..z_15),
    Delta = U V - W^2, G = Q^2 - 4 Delta, all complex bilinear sums.

    Polynomials are Ring_polynom.Pol over Z. table is a memo of Pfaffians keyed by index list; allcheck
    verifies every stored entry against its first-index expansion over stored entries and the root
    entry against -(z.t) Q G. certificate_ok evaluates allcheck by vm_compute (measured 2026-11-23:
    29 s for the table build on one core). *)

From Stdlib Require Import ZArith List Ring_polynom Ring_theory InitialRing PeanoNat Lia FMapPositive.
Import ListNotations.
Import ListNotations.
Local Open Scope Z_scope.

Definition ZP := Pol Z.
Definition padd : ZP -> ZP -> ZP := Padd 0 Z.add Z.eqb.
Definition pmul : ZP -> ZP -> ZP := Pmul 0 1 Z.add Z.mul Z.eqb.
Definition popp : ZP -> ZP := Popp Z.opp.
Definition pc (c : Z) : ZP := Pc c.
Definition pX (j : positive) : ZP := mk_X 0 1 j.
Definition peq : ZP -> ZP -> bool := Peq Z.eqb.

(* Cayley-Dickson product on coordinate lists of length 2^k, cd_core doubling. *)
Fixpoint cdmul (k : nat) (x y : list Z) : list Z :=
  match k with
  | O => [hd 0 x * hd 0 y]
  | S j =>
      let h := Nat.pow 2 j in
      let a := firstn h x in let b := skipn h x in
      let c := firstn h y in let d := skipn h y in
      let conj v := match v with [] => [] | v0 :: vr => v0 :: map Z.opp vr end in
      let add u w := map (fun p => fst p + snd p) (combine u w) in
      let sub u w := map (fun p => fst p - snd p) (combine u w) in
      sub (cdmul j a c) (cdmul j (conj d) b) ++ add (cdmul j d a) (cdmul j b (conj c))
  end.

Definition ebasis (n p : nat) : list Z := map (fun q => if Nat.eqb q p then 1 else 0) (seq 0 n).
Definition sgn16 (a b : nat) : Z := nth a (cdmul 4 (ebasis 16 (Nat.lxor a b)) (ebasis 16 b)) 0.

(* A(z, t): z_k is variable k (k = 1..15), t_k is variable 15 + k. *)
Definition Amat (a b : nat) : ZP :=
  if Nat.eqb a b then pc 0 else
  if Nat.eqb a 0 then popp (pX (Pos.of_nat (15 + b))) else
  if Nat.eqb b 0 then pX (Pos.of_nat (15 + a)) else
  pmul (pc (sgn16 a b)) (pX (Pos.of_nat (Nat.lxor a b))).

Fixpoint sumP (n : nat) (f : nat -> ZP) : ZP :=
  match n with O => pc 0 | S m => padd (sumP m f) (f m) end.
Definition sgnP (k : nat) : ZP := if Nat.even k then pc 1 else pc (-1).
Fixpoint rem_at {A} (k : nat) (l : list A) {struct l} : list A :=
  match l with [] => [] | x :: r => match k with O => r | S k' => x :: rem_at k' r end end.
Fixpoint pfP (M : nat -> nat -> ZP) (n : nat) (l : list nat) : ZP :=
  match l with
  | [] => pc 1
  | x :: r => match n with O => pc 0 | S n' =>
      sumP (length r) (fun k => pmul (pmul (sgnP k) (M x (nth k r O))) (pfP M n' (rem_at k r))) end
  end.

Definition zv (k : nat) : ZP := pX (Pos.of_nat k).
Definition tv (k : nat) : ZP := pX (Pos.of_nat (15 + k)).
Definition dotP (f g : nat -> ZP) (lo hi : nat) : ZP := sumP (hi - lo) (fun m => pmul (f (lo + m)%nat) (g (lo + m)%nat)).
Definition QP := dotP zv zv 1 16.
Definition UP := dotP zv zv 1 8.
Definition VP := dotP zv zv 9 16.
Definition WP := dotP zv (fun k => zv (k + 8)%nat) 1 8.
Definition DeltaP := padd (pmul UP VP) (popp (pmul WP WP)).
Definition GP := padd (pmul QP QP) (pmul (pc (-4)) DeltaP).
Definition ztP := dotP zv tv 1 16.
Definition rhs := popp (pmul ztP (pmul QP GP)).


Definition idx : list nat := seq 0 16.

Module PM := PositiveMap.
Fixpoint keyl (l : list nat) : positive :=
  match l with [] => 1%positive | x :: r => Pos.add (keyl r) (Pos.of_nat (Nat.pow 2 x)) end.

Fixpoint memo (n : nat) (l : list nat) (m : PM.t (list nat * ZP)) : ZP * PM.t (list nat * ZP) :=
  match PM.find (keyl l) m with
  | Some (_, p) => (p, m)
  | None =>
    match l with
    | [] => (pc 1, PM.add (keyl l) (l, pc 1) m)
    | x :: r =>
      match n with
      | O => (pc 0, m)
      | S n' =>
        let fix go (k : nat) (acc : ZP) (m : PM.t (list nat * ZP)) : ZP * PM.t (list nat * ZP) :=
          match k with
          | O => (acc, m)
          | S k' => let j := (length r - k)%nat in
                    let (p, m') := memo n' (rem_at j r) m in
                    go k' (padd acc (pmul (pmul (sgnP j) (Amat x (nth j r O))) p)) m'
          end in
        let (p, m') := go (length r) (pc 0) m in (p, PM.add (keyl l) (l, p) m')
      end
    end
  end.

Section Check.
Variable tbl : PM.t (list nat * ZP).

Definition lookup (l : list nat) : option ZP :=
  match PM.find (keyl l) tbl with
  | Some (l', p) => if list_eq_dec Nat.eq_dec l l' then Some p else None
  | None => None
  end.

Fixpoint children (x : nat) (r : list nat) (k : nat) : option ZP :=
  match k with
  | O => Some (pc 0)
  | S k' =>
      match children x r k', lookup (rem_at k' r) with
      | Some acc, Some q => Some (padd acc (pmul (pmul (sgnP k') (Amat x (nth k' r O))) q))
      | _, _ => None
      end
  end.

Definition entry_ok (l : list nat) (p : ZP) : bool :=
  match l with
  | [] => peq p (pc 1)
  | x :: r => match children x r (length r) with Some s => peq p s | None => false end
  end.

Definition check_table : bool :=
  forallb (fun e => entry_ok (fst (snd e)) (snd (snd e))) (PM.elements tbl) &&
  match lookup idx with Some p => peq p rhs | None => false end.
End Check.

Definition table : PM.t (list nat * ZP) := snd (memo 16 idx (PM.empty _)).

Lemma certificate_ok : check_table table = true.
Proof. vm_compute. reflexivity. Qed.
