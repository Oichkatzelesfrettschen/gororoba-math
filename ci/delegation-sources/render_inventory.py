#!/usr/bin/env python3
"""Render a source of rocq/delegation from a confine statement inventory.

Usage: render_inventory.py INVENTORY N >rocq/delegation/InventoryN.v

INVENTORY is confine_theorems_N.v of gororoba-open
(curated/01_theory_frameworks): Theorem statements, each of the form
has_right S O A -> reachable_delegation S O A, with no proofs. The rendering
keeps the bytes of every statement, in order, inside a functor over a rights
relation and follows each with its proof. The functor then pairs every
right with the theorem stated about it (the list stated, which typechecks
only when each theorem is about its right), and the source proves the rights
of that list equal to chain_table 16 N of Model.v. A statement ends in a
newline in the rendering, also the last one of an inventory that ends
without one.
Writes the rendering to standard output and nothing else. Exit status: 0
rendered, 1 the inventory holds a line that is no such statement, 2 usage.
"""

import re
import sys

STATEMENT = re.compile(
    r'Theorem (confine_\w+) :\s+has_right "([^"\\]*)" "([^"\\]*)" (\w+) ->\s+'
    r'reachable_delegation "([^"\\]*)" "([^"\\]*)" (\w+)\.(\n|\Z)'
)
ACTIONS = ("Send", "Receive", "Map", "Grant")
PROOF = "Proof. exact (rd_direct _ _ _). Qed.\n"


def fail(message):
    print(f"render_inventory: {message}", file=sys.stderr)
    raise SystemExit(1)


def parse(text):
    bodies, rows, names, position = [], [], set(), 0
    while position < len(text):
        match = STATEMENT.match(text, position)
        if match is None:
            fail(f"no statement at byte {position}")
        name, subject, target, action, subject2, target2, action2, _ = match.groups()
        if (subject, target, action) != (subject2, target2, action2):
            fail(f"{name} relates two different rights")
        if action not in ACTIONS:
            fail(f"{name} names the action {action}")
        if name in names:
            fail(f"{name} is stated twice")
        names.add(name)
        body = match.group(0)
        bodies.append(body if body.endswith("\n") else body + "\n")
        rows.append((name, subject, target, action))
        position = match.end()
    if not rows:
        fail("the inventory holds no statement")
    return bodies, rows


def render(bodies, rows, size):
    stated = ";\n   ".join(
        f'exist Stated ("{subject}", "{target}", {action}) {name}' for name, subject, target, action in rows
    )
    statements = "".join(body + PROOF for body in bodies)
    return f"""(* Rendered by ci/delegation-sources/render_inventory.py from
   curated/01_theory_frameworks/confine_theorems_{size}.v of gororoba-open;
   a change goes through the generator. Inventory holds the statements of
   that file, each with its proof, for every rights relation, and stated
   pairs each right with the theorem about it. inventory is the list of
   those rights, and inventory_is_chain_table identifies it with
   chain_table 16 {size} of Model.v, the chain of {size} threads with an
   arena every 16. *)

From Stdlib Require Import String List.
From GororobaDelegation Require Import Model.
Import ListNotations.

Open Scope string_scope.

Module Inventory (R : RIGHTS).
Module D := Reachability R.
Import R D.

{statements}
(* A right together with a proof of the statement about it. *)
Definition Stated (r : string * string * Action) : Prop :=
  has_right (fst (fst r)) (snd (fst r)) (snd r) ->
  reachable_delegation (fst (fst r)) (snd (fst r)) (snd r).

Definition stated : list (sig Stated) :=
  [{stated}].

End Inventory.

Module Size <: SIZE.
  Definition period := 16.
  Definition n := {size}.
End Size.

Module System := Chain Size.
Module Statements := Inventory System.R.

(* The rights of the statements, in order. *)
Definition inventory : list (string * string * Action) :=
  map (@proj1_sig _ _) Statements.stated.

Lemma inventory_is_chain_table : inventory = chain_table 16 {size}.
Proof. vm_compute. reflexivity. Qed.

(* Each right an inventory statement names is held in the chain. *)
Lemma inventory_held :
  Forall (fun r => chain_right 16 {size} (fst (fst r)) (snd (fst r)) (snd r))
    inventory.
Proof.
  rewrite inventory_is_chain_table. apply chain_table_held. discriminate.
Qed.

(* So the conclusion of each inventory statement holds outright. *)
Lemma inventory_reachable :
  Forall (fun r => System.D.reachable_delegation
                     (fst (fst r)) (snd (fst r)) (snd r))
    inventory.
Proof.
  rewrite inventory_is_chain_table. apply System.chain_table_reachable.
  discriminate.
Qed.
"""


def main(argv):
    if len(argv) != 3 or not argv[2].isdigit():
        print(__doc__, file=sys.stderr)
        raise SystemExit(2)
    with open(argv[1], encoding="ascii", newline="") as handle:
        bodies, rows = parse(handle.read())
    sys.stdout.write(render(bodies, rows, int(argv[2])))


if __name__ == "__main__":
    main(sys.argv)
