(** A translation-validation boundary for the integer subset used by cd_sign.

    [py] is a generic tree of CPython AST node tags, named fields and values.
    The Python producer only serializes ast.iter_fields: it does not decide
    which Python construct means which target constructor. A kernel-checked
    certificate compares its executable view with the target quotation.

    [source_eval] and [source_exec] interpret raw node tags directly. They do
    not call the target evaluator or translate the tree before executing it.
    The preservation theorems below relate this independent interpreter to
    CdSignPythonSemantics, including short circuiting, exceptions, statement
    order and loop fuel. This is a theorem about an explicitly specified
    integer abstraction of Python, not about the CPython C implementation.
    Parsing/source-byte binding and the integer guard contracts remain
    external boundaries. Module execution, annotations and decorators are
    not given Python semantics here; a function view refuses decorators and
    default/variadic parameters and observes annotations only as metadata. *)

From Stdlib Require Import ZArith String Ascii List Bool.
Require Import CdSignPythonSemantics.
Module T := CdSignPythonSemantics.
Open Scope string_scope.
Open Scope list_scope.

(** Binary lists make the raw representation a first-order tree, so its
    equality decision checks every tag, field name, context and atom. *)
Inductive py :=
| PNode (tag : string) (fields : py)
| PField (key : string) (value : py)
| PList (items : py)
| PCons (head tail : py)
| PNil
| PStr (value : string)
| PInt (value : Z)
| PBool (value : bool)
| PNone.

Declare Scope py_scope.
Delimit Scope py_scope with py.
Notation "[ ]" := PNil : py_scope.
Notation "[ x ; .. ; y ]" := (PCons x .. (PCons y PNil) ..) : py_scope.
Open Scope py_scope.

Definition field := PField.
Definition node0 (name : string) : py := PNode name [].
Definition load_name (name : string) : py :=
  PNode "Name" [field "id" (PStr name); field "ctx" (node0 "Load")].
Definition store_name (name : string) : py :=
  PNode "Name" [field "id" (PStr name); field "ctx" (node0 "Store")].

Fixpoint utf8 (bytes : list nat) : string :=
  match bytes with
  | nil => EmptyString
  | b :: rest => String (Ascii.ascii_of_nat b) (utf8 rest)
  end.

Fixpoint py_eq_dec (a b : py) : {a = b} + {a <> b}.
Proof. decide equality; try apply string_dec; try apply Z.eq_dec; decide equality. Defined.

Definition py_eqb (a b : py) : bool := if py_eq_dec a b then true else false.

Lemma py_eqb_true a b : py_eqb a b = true -> a = b.
Proof. unfold py_eqb; destruct (py_eq_dec a b); congruence. Qed.

Fixpoint pmap {A : Type} (f : A -> py) (xs : list A) : py :=
  match xs with nil => [] | x :: rest => PCons (f x) (pmap f rest) end.

Definition quote_binop (op : T.binop) : py :=
  node0 (match op with T.Sub => "Sub" | T.RShift => "RShift" end).
Definition quote_unaryop (op : T.unaryop) : py :=
  node0 (match op with T.Not => "Not" | T.USub => "USub" end).
Definition quote_cmpop (op : T.cmpop) : py :=
  node0 (match op with T.Eq => "Eq" | T.NotEq => "NotEq" | T.Lt => "Lt"
                     | T.LtE => "LtE" | T.Gt => "Gt" | T.GtE => "GtE" end).

Fixpoint quote_expr (x : T.expr) : py :=
  match x with
  | T.Name name => load_name name
  | T.Constant z => PNode "Constant" [field "value" (PInt z); field "kind" PNone]
  | T.BinOp l op r =>
      PNode "BinOp" [field "left" (quote_expr l); field "op" (quote_binop op); field "right" (quote_expr r)]
  | T.UnaryOp op x => PNode "UnaryOp" [field "op" (quote_unaryop op); field "operand" (quote_expr x)]
  | T.BoolOp T.And xs => PNode "BoolOp" [field "op" (node0 "And"); field "values" (PList (pmap quote_expr xs))]
  | T.Compare l op r =>
      PNode "Compare" [field "left" (quote_expr l); field "ops" (PList [quote_cmpop op]);
                       field "comparators" (PList [quote_expr r])]
  | T.Call name args =>
      PNode "Call" [field "func" (load_name name); field "args" (PList (pmap quote_expr args));
                    field "keywords" (PList [])]
  end.

Fixpoint quote_stmt (s : T.stmt) : py :=
  match s with
  | T.Expr x => PNode "Expr" [field "value" (quote_expr x)]
  | T.Assign name x =>
      PNode "Assign" [field "targets" (PList [store_name name]); field "value" (quote_expr x);
                      field "type_comment" PNone]
  | T.AugAssign name op x =>
      PNode "AugAssign" [field "target" (store_name name); field "op" (quote_binop op);
                         field "value" (quote_expr x)]
  | T.If test yes no =>
      PNode "If" [field "test" (quote_expr test); field "body" (PList (pmap quote_stmt yes));
                  field "orelse" (PList (pmap quote_stmt no))]
  | T.While test body =>
      PNode "While" [field "test" (quote_expr test); field "body" (PList (pmap quote_stmt body));
                     field "orelse" (PList [])]
  | T.Pass => node0 "Pass"
  | T.Return x => PNode "Return" [field "value" (quote_expr x)]
  end.

(** Integer primitive operations. The source interpreter dispatches on raw
    operator tags; its arithmetic contracts are the same mathematical Z
    contracts used by the existing target semantics. *)
Definition source_binop (op : py) (a b : Z) : option Z :=
  match op with
  | PNode "Sub" [] => Some (a - b)%Z
  | PNode "RShift" [] => if Z.ltb b 0 then None else Some (Z.shiftr a b)
  | _ => None
  end.

Definition source_unaryop (op : py) (a : Z) : option Z :=
  match op with
  | PNode "Not" [] => Some (T.of_bool (negb (T.truthy a)))
  | PNode "USub" [] => Some (- a)%Z
  | _ => None
  end.

Definition source_cmpop (op : py) (a b : Z) : option Z :=
  match op with
  | PNode "Eq" [] => Some (T.of_bool (Z.eqb a b))
  | PNode "NotEq" [] => Some (T.of_bool (negb (Z.eqb a b)))
  | PNode "Lt" [] => Some (T.of_bool (Z.ltb a b))
  | PNode "LtE" [] => Some (T.of_bool (Z.leb a b))
  | PNode "Gt" [] => Some (T.of_bool (Z.ltb b a))
  | PNode "GtE" [] => Some (T.of_bool (Z.leb b a))
  | _ => None
  end.

Fixpoint source_eval (e : T.env) (x : py) : option Z :=
  match x with
  | PNode "Name" [PField "id" (PStr name); PField "ctx" (PNode "Load" [])] => e name
  | PNode "Constant" [PField "value" (PInt z); PField "kind" PNone] => Some z
  | PNode "BinOp" [PField "left" l; PField "op" op; PField "right" r] =>
      match source_eval e l with
      | Some a => match source_eval e r with Some b => source_binop op a b | None => None end
      | None => None
      end
  | PNode "UnaryOp" [PField "op" op; PField "operand" x] =>
      match source_eval e x with Some a => source_unaryop op a | None => None end
  | PNode "BoolOp" [PField "op" (PNode "And" []); PField "values" (PList xs)] =>
      (fix conjunction (xs : py) : option Z :=
         match xs with
         | PCons x rest =>
             match rest with
             | PNil => source_eval e x
             | PCons _ _ =>
                 match source_eval e x with
                 | Some a => if T.truthy a then conjunction rest else Some a
                 | None => None
                 end
             | _ => None
             end
         | _ => None
         end) xs
  | PNode "Compare" [PField "left" l; PField "ops" (PList [op]); PField "comparators" (PList [r])] =>
      match source_eval e l with
      | Some a => match source_eval e r with Some b => source_cmpop op a b | None => None end
      | None => None
      end
  | PNode "Call" [PField "func" (PNode "Name" [PField "id" (PStr name); PField "ctx" (PNode "Load" [])]);
                  PField "args" (PList args); PField "keywords" (PList [])] =>
      match (fix values (args : py) : option (list Z) :=
               match args with
               | PNil => Some nil
               | PCons a rest =>
                   match source_eval e a with
                   | Some v => match values rest with Some vs => Some (v :: vs) | None => None end
                   | None => None
                   end
               | _ => None
               end) args with
      | Some vs => T.builtin name vs
      | None => None
      end
  | _ => None
  end.

(** Named versions of the local list evaluators, used only to state their
    induction invariants. They are definitionally equal to those local fixes. *)
Definition source_conjunction (e : T.env) : py -> option Z :=
  fix conjunction (xs : py) : option Z :=
  match xs with
  | PCons x rest =>
      match rest with
      | PNil => source_eval e x
      | PCons _ _ => match source_eval e x with
                     | Some a => if T.truthy a then conjunction rest else Some a
                     | None => None end
      | _ => None
      end
  | _ => None
  end.

Definition target_conjunction (e : T.env) : list T.expr -> option Z :=
  fix conjunction (xs : list T.expr) : option Z :=
  match xs with
  | nil => None
  | x :: rest =>
      match rest with
      | nil => T.eval e x
      | _ :: _ => match T.eval e x with
                  | Some a => if T.truthy a then conjunction rest else Some a
                  | None => None end
      end
  end.

Definition source_arguments (e : T.env) : py -> option (list Z) :=
  fix values (xs : py) : option (list Z) :=
  match xs with
  | PNil => Some nil
  | PCons x rest =>
      match source_eval e x with
      | Some a => match values rest with Some vs => Some (a :: vs) | None => None end
      | None => None end
  | _ => None
  end.

Definition target_arguments (e : T.env) : list T.expr -> option (list Z) :=
  fix values (xs : list T.expr) : option (list Z) :=
  match xs with
  | nil => Some nil
  | x :: rest =>
      match T.eval e x with
      | Some a => match values rest with Some vs => Some (a :: vs) | None => None end
      | None => None end
  end.

Fixpoint source_exec (fuel : nat) (body : py) (e : T.env) {struct fuel} : T.outcome :=
  match fuel with
  | O => T.OutOfFuel
  | S f =>
      (fix block (body : py) (e : T.env) : T.outcome :=
         match body with
         | PNil => T.Normal e
         | PCons s rest =>
             match s with
             | PNode "Expr" [PField "value" x] =>
                 match source_eval e x with Some _ => block rest e | None => T.Raised end
             | PNode "Assign" [PField "targets" (PList [PNode "Name"
                                 [PField "id" (PStr name); PField "ctx" (PNode "Store" [])]]);
                                PField "value" x; PField "type_comment" PNone] =>
                 match source_eval e x with Some v => block rest (T.upd e name v) | None => T.Raised end
             | PNode "AugAssign" [PField "target" (PNode "Name"
                                    [PField "id" (PStr name); PField "ctx" (PNode "Store" [])]);
                                   PField "op" op; PField "value" x] =>
                 match e name with
                 | Some a => match source_eval e x with
                             | Some b => match source_binop op a b with
                                         | Some v => block rest (T.upd e name v) | None => T.Raised end
                             | None => T.Raised end
                 | None => T.Raised
                 end
             | PNode "If" [PField "test" test; PField "body" (PList yes); PField "orelse" (PList no)] =>
                 match source_eval e test with
                 | Some v => match source_exec f (if T.truthy v then yes else no) e with
                             | T.Normal e' => block rest e' | o => o end
                 | None => T.Raised end
             | PNode "While" [PField "test" test; PField "body" (PList loop); PField "orelse" (PList [])] =>
                 match source_eval e test with
                 | Some v => if T.truthy v then
                               match source_exec f loop e with
                               | T.Normal e' => source_exec f (PCons s rest) e' | o => o end
                             else block rest e
                 | None => T.Raised end
             | PNode "Pass" [] => block rest e
             | PNode "Return" [PField "value" x] =>
                 match source_eval e x with Some v => T.Returned v | None => T.Raised end
             | _ => T.Raised
             end
         | _ => T.Raised
         end) body e
  end.

(** A nested induction principle supplies the expression-list hypotheses
    omitted by the default principle for this target syntax. *)
Section ExpressionInduction.
  Variable P : T.expr -> Prop.
  Variable Hname : forall id, P (T.Name id).
  Variable Hconstant : forall z, P (T.Constant z).
  Variable Hbin : forall l op r, P l -> P r -> P (T.BinOp l op r).
  Variable Hunary : forall op x, P x -> P (T.UnaryOp op x).
  Variable Hbool : forall op xs, Forall P xs -> P (T.BoolOp op xs).
  Variable Hcompare : forall l op r, P l -> P r -> P (T.Compare l op r).
  Variable Hcall : forall name args, Forall P args -> P (T.Call name args).
  Fixpoint expression_induction (x : T.expr) : P x :=
    match x with
    | T.Name id => Hname id
    | T.Constant z => Hconstant z
    | T.BinOp l op r => Hbin l op r (expression_induction l) (expression_induction r)
    | T.UnaryOp op x => Hunary op x (expression_induction x)
    | T.BoolOp op xs => Hbool op xs
        ((fix all (xs : list T.expr) : Forall P xs :=
            match xs with
            | nil => Forall_nil _
            | x :: rest => Forall_cons x (expression_induction x) (all rest)
            end) xs)
    | T.Compare l op r => Hcompare l op r (expression_induction l) (expression_induction r)
    | T.Call name args => Hcall name args
        ((fix all (xs : list T.expr) : Forall P xs :=
            match xs with
            | nil => Forall_nil _
            | x :: rest => Forall_cons x (expression_induction x) (all rest)
            end) args)
    end.
End ExpressionInduction.

Theorem expression_semantic_preservation whole e : source_eval e (quote_expr whole) = T.eval e whole.
Proof.
  revert e.
  refine (expression_induction (fun x => forall e, source_eval e (quote_expr x) = T.eval e x)
    _ _ _ _ _ _ _ whole).
  - intros name e. reflexivity.
  - intros z e. reflexivity.
  - intros l op r IHl IHr e. cbn [quote_expr source_eval T.eval field].
    rewrite IHl, IHr. destruct (T.eval e l), (T.eval e r); try reflexivity. destruct op; reflexivity.
  - intros op x IH e. cbn [quote_expr source_eval T.eval field].
    rewrite IH. destruct (T.eval e x); try reflexivity. destruct op; reflexivity.
  - intros op xs H e. destruct op.
    change (source_conjunction e (pmap quote_expr xs) = target_conjunction e xs).
    induction H as [|a rest Ha Hrest IH]; [reflexivity|].
    destruct rest as [|b rest]; cbn [pmap source_conjunction target_conjunction]; rewrite Ha; [reflexivity|].
    destruct (T.eval e a) as [v|]; [destruct (T.truthy v)|]; auto.
  - intros l op r IHl IHr e. cbn [quote_expr source_eval T.eval field].
    rewrite IHl, IHr. destruct (T.eval e l), (T.eval e r); try reflexivity. destruct op; reflexivity.
  - intros name args H e.
    change ((match source_arguments e (pmap quote_expr args) with Some vs => T.builtin name vs | None => None end) =
            (match target_arguments e args with Some vs => T.builtin name vs | None => None end)).
    assert (V : source_arguments e (pmap quote_expr args) = target_arguments e args).
    { induction H as [|a rest Ha Hrest IH]; [reflexivity|].
      cbn [pmap source_arguments target_arguments]. rewrite Ha, IH. reflexivity. }
    rewrite V. reflexivity.
Qed.

Theorem block_semantic_preservation fuel : forall body e,
  source_exec fuel (pmap quote_stmt body) e = T.exec fuel body e.
Proof.
  induction fuel as [|f IH]; intros body e; [reflexivity|].
  revert e. induction body as [|s rest IHrest]; intro e; [reflexivity|].
  destruct s as [value|target value|target op value|test yes no|test loop| |value];
    cbn [pmap quote_stmt source_exec T.exec store_name field node0];
    rewrite ?expression_semantic_preservation.
  - destruct (T.eval e value) as [v|]; [apply IHrest|reflexivity].
  - destruct (T.eval e value) as [v|]; [apply IHrest|reflexivity].
  - destruct (e target) as [a|]; [|reflexivity].
    destruct (T.eval e value) as [b|]; [|reflexivity].
    destruct op; cbn [quote_binop source_binop T.binop_eval node0].
    + apply IHrest.
    + destruct (Z.ltb b 0); [reflexivity|apply IHrest].
  - destruct (T.eval e test) as [v|]; [|reflexivity].
    destruct (T.truthy v); rewrite IH; destruct (T.exec f _ e) as [e'|returned| |];
      try reflexivity; apply IHrest.
  - destruct (T.eval e test) as [v|]; [|reflexivity].
    destruct (T.truthy v); [|apply IHrest]. rewrite IH.
    destruct (T.exec f loop e) as [e'|returned| |]; [|reflexivity|reflexivity|reflexivity].
    exact (IH (T.While test loop :: rest) e').
  - apply IHrest.
  - destruct (T.eval e value); reflexivity.
Qed.

(** A function call observes only its positional names and executable body.
    The leading string expression is __doc__, not an executed integer
    expression. Annotations remain in the raw certificate, but the theorem
    is about invocation after function definition, not annotation evaluation. *)
Fixpoint argument_names (args : py) : option (list string) :=
  match args with
  | PNil => Some nil
  | PCons (PNode "arg" [PField "arg" (PStr name); PField "annotation" _; PField "type_comment" PNone]) rest =>
      match argument_names rest with Some names => Some (name :: names) | None => None end
  | _ => None
  end.

Definition positional_names (args : py) : option (list string) :=
  match args with
  | PNode "arguments" [PField "posonlyargs" (PList []); PField "args" (PList names); PField "vararg" PNone;
                       PField "kwonlyargs" (PList []); PField "kw_defaults" (PList []);
                       PField "kwarg" PNone; PField "defaults" (PList [])] => argument_names names
  | _ => None
  end.

Definition executable_body (body : py) : py :=
  match body with
  | PCons (PNode "Expr" [PField "value" (PNode "Constant" [PField "value" (PStr _); PField "kind" PNone])]) rest
      => rest
  | _ => body
  end.

Definition function_view (raw : py) : option (list string * py) :=
  match raw with
  | PNode "FunctionDef" [PField "name" (PStr _); PField "args" args; PField "body" (PList body);
                         PField "decorator_list" (PList []); PField "returns" _;
                         PField "type_comment" PNone; PField "type_params" (PList [])] =>
      match positional_names args with
      | Some names => Some (names, executable_body body)
      | None => None
      end
  | _ => None
  end.

Definition function_certificate (raw : py) (target : T.FunctionDef) : bool :=
  match function_view raw with
  | Some (names, body) =>
      py_eqb (PList (pmap PStr names)) (PList (pmap PStr (T.params target))) &&
      py_eqb body (pmap quote_stmt (T.body target))
  | None => false
  end.

Lemma pmap_names_injective a b : pmap PStr a = pmap PStr b -> a = b.
Proof.
  revert b. induction a as [|x xs IH]; intros [|y ys] H; cbn in H; try discriminate; [reflexivity|].
  inversion H; f_equal; auto.
Qed.

Theorem function_certificate_sound raw target : function_certificate raw target = true ->
  function_view raw = Some (T.params target, pmap quote_stmt (T.body target)).
Proof.
  unfold function_certificate. destruct (function_view raw) as [[names body]|] eqn:H; [|discriminate].
  intro B. apply andb_true_iff in B as [N S]. apply py_eqb_true in N. apply py_eqb_true in S.
  inversion N. apply pmap_names_injective in H1. subst. reflexivity.
Qed.

Definition source_run (fuel : nat) (raw : py) (args : list Z) : T.outcome :=
  match function_view raw with
  | Some (names, body) =>
      match T.bind names args T.empty with
      | Some e => source_exec fuel body e
      | None => T.Raised
      end
  | None => T.Raised
  end.

Theorem function_semantic_preservation raw target fuel args :
  function_certificate raw target = true -> source_run fuel raw args = T.run fuel target args.
Proof.
  intro H. unfold source_run, T.run. rewrite (function_certificate_sound raw target H).
  destruct (T.bind (T.params target) args T.empty); [apply block_semantic_preservation|reflexivity].
Qed.
