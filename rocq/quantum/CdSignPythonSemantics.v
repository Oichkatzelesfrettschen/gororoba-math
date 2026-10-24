(** A big-step semantics of the Python subset that cd_core.cd_sign uses, run
    on that function's syntax tree. scripts/cd_sign_rocq_ast.py reads
    gororoba_quantum/cd_core.py with ast.parse and writes cd_sign_ast below,
    one constructor per ast node; tests/scripts/test_cd_sign_rocq_ast.py
    fails when the two differ. Values are Python ints as integers, with
    False and True as 0 and 1 (Python Language Reference 3.2, "numbers.Integral":
    Booleans behave like the values 0 and 1). An expression evaluates to
    Some value or None when it raises; a statement block ends Normal, with a
    Return value, by raising, or out of fuel. The calls _dimension and
    _index carry the meaning of their cd_core bodies on int arguments:
    _dimension raises unless dim >= 1 and dim & (dim - 1) = 0, and _index
    raises unless 0 <= index < dim and returns index. The theorems read
    exact-int arguments: _dimension rejects every dim whose type is not
    exactly int, bool and int subclasses included, before any operator runs
    on it, and _index hands any __index__ object on as an exact int through
    operator.index, so every call that reaches the loop runs int's own
    operators on ints; the pytest contract pins both guard bodies and
    checks these clauses.

    cd_sign_returns_sigma: for every k and p, q < 2^k, cd_sign(2^k, p, q)
    returns sigma_k(p, q), the tower sign of CdTowerBasisSign.v, through
    cd_sign_loop_sigma. cd_sign_raises_dimension and cd_sign_raises_index:
    an int argument triple whose guard fails raises. cd_sign_spec combines
    them for every int dim, p and q, with dimension_guard_pow showing that
    the dimension guard admits exactly the powers of two.
    cd_sign_mutant_differs: the syntax tree with the q != 0 guard of the
    high-low branch removed returns -1 at e_1 e_0, where sigma_1(1, 0) = 1. *)

From Stdlib Require Import ZArith Lia String List.
Require Import CdImaginarySumConference CdTowerBasisSign.
Open Scope string_scope.
Open Scope list_scope.

(** The proofs case-split on syntax and never induct over it. *)
Local Unset Elimination Schemes.

Inductive binop := Sub | RShift.
Inductive unaryop := Not | USub.
Inductive boolop := And.
Inductive cmpop := Eq | NotEq | Lt | LtE | Gt | GtE.

Inductive expr :=
| Name (id : string)
| Constant (value : Z)
| BinOp (left : expr) (op : binop) (right : expr)
| UnaryOp (op : unaryop) (operand : expr)
| BoolOp (op : boolop) (values : list expr)
| Compare (left : expr) (op : cmpop) (right : expr)
| Call (func : string) (args : list expr).

Inductive stmt :=
| Expr (value : expr)
| Assign (target : string) (value : expr)
| AugAssign (target : string) (op : binop) (value : expr)
| If (test : expr) (body orelse : list stmt)
| While (test : expr) (body : list stmt)
| Pass
| Return (value : expr).

Record FunctionDef := mkFunctionDef { params : list string; body : list stmt }.

(** Local variables: an unbound name raises UnboundLocalError (None). *)
Definition env := string -> option Z.
Definition empty : env := fun _ => None.
Definition upd (e : env) (x : string) (v : Z) : env := fun y => if String.eqb y x then Some v else e y.

(** Truth value of an int (Language Reference 6.11): zero is false. *)
Definition truthy (v : Z) : bool := negb (Z.eqb v 0).
Definition of_bool (b : bool) : Z := if b then 1%Z else 0%Z.

(** Subtraction (6.7) and right shift, floor division by 2^b (6.8); a negative
    shift count raises ValueError (Library Reference, "Bitwise Operations on Integer Types"). *)
Definition binop_eval (op : binop) (a b : Z) : option Z :=
  match op with
  | Sub => Some (a - b)%Z
  | RShift => if Z.ltb b 0 then None else Some (Z.shiftr a b)
  end.

(** not (6.11) returns a bool; unary minus (6.6) negates. *)
Definition unaryop_eval (op : unaryop) (a : Z) : Z :=
  match op with
  | Not => of_bool (negb (truthy a))
  | USub => (- a)%Z
  end.

(** Value comparisons of ints (6.10.1) return a bool. *)
Definition cmpop_eval (op : cmpop) (a b : Z) : bool :=
  match op with
  | Eq => Z.eqb a b
  | NotEq => negb (Z.eqb a b)
  | Lt => Z.ltb a b
  | LtE => Z.leb a b
  | Gt => Z.ltb b a
  | GtE => Z.leb b a
  end.

(** The guards of cd_core._dimension and cd_core._index on int arguments. *)
Definition dimension_guard (dim : Z) : bool := andb (Z.leb 1 dim) (Z.eqb (Z.land dim (dim - 1)) 0).
Definition index_guard (dim index : Z) : bool := andb (Z.leb 0 index) (Z.ltb index dim).
Arguments dimension_guard : simpl never.
Arguments index_guard : simpl never.

(** _dimension returns None, read as 0 since the call statement discards it; any other callee raises. *)
Definition builtin (f : string) (args : list Z) : option Z :=
  if String.eqb f "_dimension" then
    match args with
    | dim :: nil => if dimension_guard dim then Some 0%Z else None
    | _ => None
    end
  else if String.eqb f "_index" then
    match args with
    | dim :: index :: nil => if index_guard dim index then Some index else None
    | _ => None
    end
  else None.

(** Operands evaluate left to right; x and y returns x when x is false and y otherwise (6.11). *)
Fixpoint eval (e : env) (x : expr) : option Z :=
  match x with
  | Name i => e i
  | Constant v => Some v
  | BinOp l op r =>
      match eval e l with
      | Some a => match eval e r with Some b => binop_eval op a b | None => None end
      | None => None
      end
  | UnaryOp op a => match eval e a with Some v => Some (unaryop_eval op v) | None => None end
  | BoolOp And vs =>
      (fix conj (vs : list expr) : option Z :=
         match vs with
         | nil => None
         | v :: r =>
             match r with
             | nil => eval e v
             | _ :: _ => match eval e v with Some a => if truthy a then conj r else Some a | None => None end
             end
         end) vs
  | Compare l op r =>
      match eval e l with
      | Some a => match eval e r with Some b => Some (of_bool (cmpop_eval op a b)) | None => None end
      | None => None
      end
  | Call f args =>
      match (fix values (args : list expr) : option (list Z) :=
               match args with
               | nil => Some nil
               | a :: r =>
                   match eval e a with
                   | Some v => match values r with Some vs => Some (v :: vs) | None => None end
                   | None => None
                   end
               end) args with
      | Some vs => builtin f vs
      | None => None
      end
  end.

Inductive outcome := Normal (e : env) | Returned (v : Z) | Raised | OutOfFuel.

(** Statements run in order (Language Reference 7 and 8). A nested block and
    each further while iteration spend one unit of fuel. *)
Fixpoint exec (fuel : nat) (b : list stmt) (e : env) {struct fuel} : outcome :=
  match fuel with
  | O => OutOfFuel
  | S f =>
      (fix block (b : list stmt) (e : env) : outcome :=
         match b with
         | nil => Normal e
         | s :: r =>
             match s with
             | Expr x => match eval e x with Some _ => block r e | None => Raised end
             | Assign t x => match eval e x with Some v => block r (upd e t v) | None => Raised end
             | AugAssign t op x =>
                 match e t with
                 | Some a =>
                     match eval e x with
                     | Some c => match binop_eval op a c with Some v => block r (upd e t v) | None => Raised end
                     | None => Raised
                     end
                 | None => Raised
                 end
             | If c t1 t2 =>
                 match eval e c with
                 | Some v => match exec f (if truthy v then t1 else t2) e with Normal e' => block r e' | o => o end
                 | None => Raised
                 end
             | While c w =>
                 match eval e c with
                 | Some v =>
                     if truthy v then match exec f w e with Normal e' => exec f (s :: r) e' | o => o end
                     else block r e
                 | None => Raised
                 end
             | Pass => block r e
             | Return x => match eval e x with Some v => Returned v | None => Raised end
             end
         end) b e
  end.

(** A call binds the positional parameters in a fresh local scope; an arity mismatch raises TypeError. *)
Fixpoint bind (ps : list string) (args : list Z) (e : env) : option env :=
  match ps, args with
  | nil, nil => Some e
  | x :: ps', v :: args' => bind ps' args' (upd e x v)
  | _, _ => None
  end.

Definition run (fuel : nat) (fd : FunctionDef) (args : list Z) : outcome :=
  match bind (params fd) args empty with Some e => exec fuel (body fd) e | None => Raised end.

(* BEGIN cd_sign_ast: generated by scripts/cd_sign_rocq_ast.py *)
Definition cd_sign_ast : FunctionDef :=
  mkFunctionDef ("dim" :: "p" :: "q" :: nil)
  (Expr (Call "_dimension" ((Name "dim") :: nil)) ::
  Assign "p" (Call "_index" ((Name "dim") :: (Name "p") :: nil)) ::
  Assign "q" (Call "_index" ((Name "dim") :: (Name "q") :: nil)) ::
  Assign "sign" (Constant 1%Z) ::
  Assign "half" (BinOp (Name "dim") RShift (Constant 1%Z)) ::
  While (Compare (Name "half") Gt (Constant 0%Z))
    (Assign "p_hi" (Compare (Name "p") GtE (Name "half")) ::
    Assign "q_hi" (Compare (Name "q") GtE (Name "half")) ::
    If (BoolOp And ((UnaryOp Not (Name "p_hi")) :: (UnaryOp Not (Name "q_hi")) :: nil))
      (Pass ::
      nil)
      (If (BoolOp And ((UnaryOp Not (Name "p_hi")) :: (Name "q_hi") :: nil))
        (Assign "qh" (BinOp (Name "q") Sub (Name "half")) ::
        Assign "q" (Name "p") ::
        Assign "p" (Name "qh") ::
        nil)
        (If (BoolOp And ((Name "p_hi") :: (UnaryOp Not (Name "q_hi")) :: nil))
          (AugAssign "p" Sub (Name "half") ::
          If (Compare (Name "q") NotEq (Constant 0%Z))
            (Assign "sign" (UnaryOp USub (Name "sign")) ::
            nil)
            nil ::
          nil)
          (Assign "qh" (BinOp (Name "q") Sub (Name "half")) ::
          Assign "ph" (BinOp (Name "p") Sub (Name "half")) ::
          If (Compare (Name "qh") Eq (Constant 0%Z))
            (Return (UnaryOp USub (Name "sign")) ::
            nil)
            nil ::
          Assign "p" (Name "qh") ::
          Assign "q" (Name "ph") ::
          nil) ::
        nil) ::
      nil) ::
    AugAssign "half" RShift (Constant 1%Z) ::
    nil) ::
  Return (Name "sign") ::
  nil).
(* END cd_sign_ast *)

(* BEGIN cd_sign_mutant_ast: generated by scripts/cd_sign_rocq_ast.py *)
Definition cd_sign_mutant_ast : FunctionDef :=
  mkFunctionDef ("dim" :: "p" :: "q" :: nil)
  (Expr (Call "_dimension" ((Name "dim") :: nil)) ::
  Assign "p" (Call "_index" ((Name "dim") :: (Name "p") :: nil)) ::
  Assign "q" (Call "_index" ((Name "dim") :: (Name "q") :: nil)) ::
  Assign "sign" (Constant 1%Z) ::
  Assign "half" (BinOp (Name "dim") RShift (Constant 1%Z)) ::
  While (Compare (Name "half") Gt (Constant 0%Z))
    (Assign "p_hi" (Compare (Name "p") GtE (Name "half")) ::
    Assign "q_hi" (Compare (Name "q") GtE (Name "half")) ::
    If (BoolOp And ((UnaryOp Not (Name "p_hi")) :: (UnaryOp Not (Name "q_hi")) :: nil))
      (Pass ::
      nil)
      (If (BoolOp And ((UnaryOp Not (Name "p_hi")) :: (Name "q_hi") :: nil))
        (Assign "qh" (BinOp (Name "q") Sub (Name "half")) ::
        Assign "q" (Name "p") ::
        Assign "p" (Name "qh") ::
        nil)
        (If (BoolOp And ((Name "p_hi") :: (UnaryOp Not (Name "q_hi")) :: nil))
          (AugAssign "p" Sub (Name "half") ::
          Assign "sign" (UnaryOp USub (Name "sign")) ::
          nil)
          (Assign "qh" (BinOp (Name "q") Sub (Name "half")) ::
          Assign "ph" (BinOp (Name "p") Sub (Name "half")) ::
          If (Compare (Name "qh") Eq (Constant 0%Z))
            (Return (UnaryOp USub (Name "sign")) ::
            nil)
            nil ::
          Assign "p" (Name "qh") ::
          Assign "q" (Name "ph") ::
          nil) ::
        nil) ::
      nil) ::
    AugAssign "half" RShift (Constant 1%Z) ::
    nil) ::
  Return (Name "sign") ::
  nil).
(* END cd_sign_mutant_ast *)

Open Scope nat_scope.

(** The while statement and the return after it. *)
Definition loop_stmt := nth 5 (body cd_sign_ast) Pass.
Definition loop_body := match loop_stmt with While _ w => w | _ => nil end.
Definition loop_stmts := skipn 5 (body cd_sign_ast).
Lemma loop_unfold f e : exec (S f) loop_stmts e =
  match match e "half" with Some h => Some (of_bool (Z.ltb 0 h)) | None => None end with
  | Some v =>
      if truthy v then match exec f loop_body e with Normal e' => exec f loop_stmts e' | o => o end
      else match e "sign" with Some v => Returned v | None => Raised end
  | None => Raised end.
Proof. reflexivity. Qed.

(** The value of half when L levels remain: 2^(L-1), and 0 once the loop ends. *)
Definition half_val (L : nat) : Z := match L with O => 0%Z | S j => Z.of_nat (Nat.pow 2 j) end.

Lemma leb_nat a b : Z.leb (Z.of_nat a) (Z.of_nat b) = Nat.leb a b.
Proof. destruct (Nat.leb_spec a b), (Z.leb_spec (Z.of_nat a) (Z.of_nat b)); lia. Qed.
Lemma half_shift j : Z.shiftr (Z.of_nat (Nat.pow 2 j)) 1 = half_val j.
Proof.
  rewrite Z.shiftr_div_pow2 by lia. destruct j as [|j]; [reflexivity|]. simpl half_val.
  rewrite Nat.pow_succ_r', Nat2Z.inj_mul. change (2 ^ 1)%Z with 2%Z. rewrite Z.mul_comm, Z.div_mul; lia.
Qed.

(** Evaluate the next statements, reading p, q, sign and half from the hypotheses. *)
Ltac lookups Hp Hq Hs Hh := repeat (unfold upd; simpl; rewrite ?Hp, ?Hq, ?Hs, ?Hh; simpl).

(** One iteration with half = 2^j either returns the value of cd_sign_loop or
    leaves the state one level down that cd_sign_loop recurses on. *)
Lemma body_step j p q s e f : 5 <= f -> p < Nat.pow 2 (S j) -> q < Nat.pow 2 (S j) ->
  e "p" = Some (Z.of_nat p) -> e "q" = Some (Z.of_nat q) -> e "sign" = Some s -> e "half" = Some (Z.of_nat (Nat.pow 2 j)) ->
  match exec f loop_body e with
  | Normal e' => exists p' q' s', p' < Nat.pow 2 j /\ q' < Nat.pow 2 j /\
      e' "p" = Some (Z.of_nat p') /\ e' "q" = Some (Z.of_nat q') /\ e' "sign" = Some s' /\ e' "half" = Some (half_val j) /\
      cd_sign_loop (S j) p q s = cd_sign_loop j p' q' s'
  | Returned v => cd_sign_loop (S j) p q s = v
  | _ => False
  end.
Proof.
  intros Hf Hp Hq Ep Eq Es Eh. do 5 (destruct f as [|f]; [lia|]). simpl in Hp, Hq.
  unfold loop_body, loop_stmt. simpl. rewrite Eh, Ep. simpl. lookups Ep Eq Es Eh.
  rewrite !leb_nat. simpl cd_sign_loop.
  destruct (Nat.ltb_spec p (Nat.pow 2 j)) as [Lp|Lp], (Nat.ltb_spec q (Nat.pow 2 j)) as [Lq|Lq].
  - replace (Nat.leb (Nat.pow 2 j) p) with false by (symmetry; apply Nat.leb_gt; lia).
    replace (Nat.leb (Nat.pow 2 j) q) with false by (symmetry; apply Nat.leb_gt; lia).
    lookups Ep Eq Es Eh. exists p, q, s. rewrite half_shift. repeat split; auto.
  - replace (Nat.leb (Nat.pow 2 j) p) with false by (symmetry; apply Nat.leb_gt; lia).
    replace (Nat.leb (Nat.pow 2 j) q) with true by (symmetry; apply Nat.leb_le; lia).
    lookups Ep Eq Es Eh. exists (q - Nat.pow 2 j), p, s. rewrite half_shift.
    repeat split; try reflexivity; try lia. f_equal. rewrite Nat2Z.inj_sub by lia. reflexivity.
  - replace (Nat.leb (Nat.pow 2 j) p) with true by (symmetry; apply Nat.leb_le; lia).
    replace (Nat.leb (Nat.pow 2 j) q) with false by (symmetry; apply Nat.leb_gt; lia).
    destruct q as [|q'].
    + lookups Ep Eq Es Eh. exists (p - Nat.pow 2 j), 0, s. rewrite half_shift.
      repeat split; try reflexivity; try lia. f_equal. rewrite Nat2Z.inj_sub by lia. reflexivity.
    + lookups Ep Eq Es Eh. exists (p - Nat.pow 2 j), (S q'), (- s)%Z. rewrite half_shift.
      repeat split; try reflexivity; try lia. f_equal. rewrite Nat2Z.inj_sub by lia. reflexivity.
  - replace (Nat.leb (Nat.pow 2 j) p) with true by (symmetry; apply Nat.leb_le; lia).
    replace (Nat.leb (Nat.pow 2 j) q) with true by (symmetry; apply Nat.leb_le; lia).
    destruct (Nat.le_exists_sub (Nat.pow 2 j) p Lp) as [p' [-> _]].
    destruct (Nat.le_exists_sub (Nat.pow 2 j) q Lq) as [q' [-> _]].
    lookups Ep Eq Es Eh. rewrite !Nat2Z.inj_add, !Z.add_simpl_r, !Nat.add_sub.
    destruct q' as [|q'].
    + lookups Ep Eq Es Eh. reflexivity.
    + lookups Ep Eq Es Eh. exists (S q'), p', s. rewrite half_shift.
      repeat split; try reflexivity; lia.
Qed.

(** The loop with L levels left computes cd_sign_loop L. *)
Lemma loop_spec L : forall fuel p q s e, L + 6 <= fuel -> p < Nat.pow 2 L -> q < Nat.pow 2 L ->
  e "p" = Some (Z.of_nat p) -> e "q" = Some (Z.of_nat q) -> e "sign" = Some s -> e "half" = Some (half_val L) ->
  exec fuel loop_stmts e = Returned (cd_sign_loop L p q s).
Proof.
  induction L as [|j IH]; intros fuel p q s e Hf Hp Hq Ep Eq Es Eh; (destruct fuel as [|f]; [lia|]);
    rewrite loop_unfold, Eh; simpl half_val; cbv iota.
  - change (truthy (of_bool (Z.ltb 0 0))) with false. cbv iota. rewrite Es. reflexivity.
  - pose proof (Nat.pow_nonzero 2 j ltac:(lia)) as H0.
    replace (Z.ltb 0 (Z.of_nat (Nat.pow 2 j))) with true by (symmetry; apply Z.ltb_lt; lia).
    change (truthy (of_bool true)) with true. cbv iota.
    pose proof (body_step j p q s e f ltac:(lia) Hp Hq Ep Eq Es Eh) as B.
    destruct (exec f loop_body e) as [e'|v| |]; cbv iota; [|congruence|contradiction|contradiction].
    destruct B as [p' [q' [s' [Hp' [Hq' [Ep' [Eq' [Es' [Eh' L]]]]]]]]]. rewrite L. apply IH; auto. lia.
Qed.

Lemma dimension_pow k : dimension_guard (Z.of_nat (Nat.pow 2 k)) = true.
Proof.
  unfold dimension_guard. rewrite Nat2Z.inj_pow. change (Z.of_nat 2) with 2%Z.
  pose proof (Z.pow_pos_nonneg 2 (Z.of_nat k) ltac:(lia) ltac:(lia)) as H.
  replace (2 ^ Z.of_nat k - 1)%Z with (Z.ones (Z.of_nat k)) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones, Z.mod_same by lia. apply andb_true_intro. split; [apply Z.leb_le; lia|reflexivity].
Qed.

Lemma index_pow k i : i < Nat.pow 2 k -> index_guard (Z.of_nat (Nat.pow 2 k)) (Z.of_nat i) = true.
Proof. intro Hi. unfold index_guard. apply andb_true_intro. split; [apply Z.leb_le|apply Z.ltb_lt]; lia. Qed.

(** The statements before the while loop: the guards, sign = 1 and half = dim >> 1. *)
Lemma cd_sign_prefix f dim p q : run (S f) cd_sign_ast (dim :: p :: q :: nil) =
  match builtin "_dimension" (dim :: nil) with
  | Some _ =>
      match builtin "_index" (dim :: p :: nil) with
      | Some p' =>
          match builtin "_index" (dim :: q :: nil) with
          | Some q' =>
              exec (S f) loop_stmts
                (upd (upd (upd (upd (upd (upd (upd empty "dim" dim) "p" p) "q" q) "p" p') "q" q') "sign" 1)
                   "half" (Z.shiftr dim 1))
          | None => Raised
          end
      | None => Raised
      end
  | None => Raised
  end.
Proof. reflexivity. Qed.

Lemma builtin_dimension dim : builtin "_dimension" (dim :: nil) = if dimension_guard dim then Some 0%Z else None.
Proof. reflexivity. Qed.

Lemma builtin_index dim i : builtin "_index" (dim :: i :: nil) = if index_guard dim i then Some i else None.
Proof. reflexivity. Qed.

(** cd_core.cd_sign(2^k, p, q) returns sigma_k(p, q) for every k and p, q < 2^k. *)
Theorem cd_sign_returns_sigma k p q fuel : k + 7 <= fuel -> p < Nat.pow 2 k -> q < Nat.pow 2 k ->
  run fuel cd_sign_ast (Z.of_nat (Nat.pow 2 k) :: Z.of_nat p :: Z.of_nat q :: nil) = Returned (sigma k p q).
Proof.
  intros Hf Hp Hq. destruct fuel as [|f]; [lia|].
  rewrite cd_sign_prefix, builtin_dimension, !builtin_index, dimension_pow, !index_pow by assumption.
  rewrite half_shift, (loop_spec k (S f) p q 1%Z) by (reflexivity || lia). rewrite cd_sign_loop_sigma, Z.mul_1_l. reflexivity.
Qed.

(** An int dimension that is not a positive power of two raises ValueError. *)
Theorem cd_sign_raises_dimension fuel dim p q : 1 <= fuel -> dimension_guard dim = false ->
  run fuel cd_sign_ast (dim :: p :: q :: nil) = Raised.
Proof. intros Hf G. destruct fuel as [|f]; [lia|]. rewrite cd_sign_prefix, builtin_dimension, G. reflexivity. Qed.

(** With a valid dimension, an index outside 0 <= index < dim raises ValueError. *)
Theorem cd_sign_raises_index fuel dim p q : 1 <= fuel -> dimension_guard dim = true ->
  index_guard dim p = false \/ index_guard dim q = false -> run fuel cd_sign_ast (dim :: p :: q :: nil) = Raised.
Proof.
  intros Hf G I. destruct fuel as [|f]; [lia|]. rewrite cd_sign_prefix, builtin_dimension, !builtin_index, G.
  destruct I as [I|I]; rewrite I; [reflexivity|]. destruct (index_guard dim p); reflexivity.
Qed.

(** Without the q != 0 guard of the high-low branch, e_1 e_0 at dimension 2
    returns -1, while sigma_1(1, 0) = 1 and cd_sign returns 1. *)
Theorem cd_sign_mutant_differs :
  run 8 cd_sign_mutant_ast (2 :: 1 :: 0 :: nil)%Z = Returned (-1)%Z /\ sigma 1 1 0 = 1%Z /\
  run 8 cd_sign_ast (2 :: 1 :: 0 :: nil)%Z = Returned 1%Z.
Proof. repeat split; reflexivity. Qed.

(** The dimension guard accepts exactly the powers of two: with b the top bit
    of dim, dim - 1 keeps bit b unless dim = 2^b. *)
Lemma dimension_guard_pow dim : dimension_guard dim = true -> dim = Z.of_nat (Nat.pow 2 (Z.to_nat (Z.log2 dim))).
Proof.
  unfold dimension_guard. intro G. apply andb_prop in G as [G1 G2]. apply Z.leb_le in G1. apply Z.eqb_eq in G2.
  rewrite Nat2Z.inj_pow, Z2Nat.id by apply Z.log2_nonneg. change (Z.of_nat 2) with 2%Z.
  destruct (Z.log2_spec dim ltac:(lia)) as [Lo Hi]. rewrite Z.pow_succ_r in Hi by apply Z.log2_nonneg.
  destruct (Z.eq_dec dim (2 ^ Z.log2 dim)) as [E|E]; [exact E|exfalso].
  assert (Z.log2 (dim - 1) = Z.log2 dim) as L.
  { apply Z.log2_unique; [apply Z.log2_nonneg|]. rewrite Z.pow_succ_r by apply Z.log2_nonneg. lia. }
  pose proof (Z.bit_log2 dim ltac:(lia)) as B1. pose proof (Z.bit_log2 (dim - 1) ltac:(lia)) as B2. rewrite L in B2.
  pose proof (Z.land_spec dim (dim - 1) (Z.log2 dim)) as B. rewrite B1, B2, G2, Z.bits_0 in B. discriminate.
Qed.

(** For every int dim, p and q, cd_core.cd_sign(dim, p, q) returns sigma_k(p, q)
    with dim = 2^k when its guards pass and raises ValueError otherwise. *)
Theorem cd_sign_spec dim p q fuel : Z.to_nat (Z.log2 dim) + 7 <= fuel ->
  run fuel cd_sign_ast (dim :: p :: q :: nil) =
  if andb (dimension_guard dim) (andb (index_guard dim p) (index_guard dim q))
  then Returned (sigma (Z.to_nat (Z.log2 dim)) (Z.to_nat p) (Z.to_nat q)) else Raised.
Proof.
  intro Hf. destruct (dimension_guard dim) eqn:G; [|simpl; apply cd_sign_raises_dimension; [lia|exact G]].
  destruct (index_guard dim p) eqn:Ip; [destruct (index_guard dim q) eqn:Iq|];
    simpl; try (apply cd_sign_raises_index; [lia|exact G|tauto]).
  unfold index_guard in Ip, Iq. apply andb_prop in Ip as [Ip1 Ip2]. apply andb_prop in Iq as [Iq1 Iq2].
  apply Z.leb_le in Ip1, Iq1. apply Z.ltb_lt in Ip2, Iq2.
  pose proof (dimension_guard_pow dim G) as D. remember (Z.to_nat (Z.log2 dim)) as k.
  replace (dim :: p :: q :: nil) with (Z.of_nat (Nat.pow 2 k) :: Z.of_nat (Z.to_nat p) :: Z.of_nat (Z.to_nat q) :: nil)
    by (rewrite !Z2Nat.id by lia; rewrite <- D; reflexivity).
  apply cd_sign_returns_sigma; [lia| |]; apply Nat2Z.inj_lt; rewrite <- D, Z2Nat.id; lia.
Qed.
