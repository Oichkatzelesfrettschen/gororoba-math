#!/usr/bin/env python3
"""Render a source of rocq/delegation from a confine statement inventory.

Usage: render_inventory.py INVENTORY N >rocq/delegation/InventoryN.v

INVENTORY is confine_theorems_N.v of gororoba-open
(curated/01_theory_frameworks): Theorem statements, each of the form
has_right S O A -> reachable_delegation S O A, with no proofs. The rendering
keeps the bytes of every statement, in order, inside a functor over a rights
relation and follows each with its proof; it then lists the rights the
statements name and proves that list equal to chain_table N of Model.v.
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
    rows, names, position = [], set(), 0
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
        rows.append((body if body.endswith("\n") else body + "\n", subject, target, action))
        position = match.end()
    if not rows:
        fail("the inventory holds no statement")
    return rows


def render(rows, size):
    held = ";\n   ".join(f'("{subject}", "{target}", {action})' for _, subject, target, action in rows)
    statements = "".join(body + PROOF for body, _, _, _ in rows)
    return f"""(* Rendered by ci/delegation-sources/render_inventory.py from
   curated/01_theory_frameworks/confine_theorems_{size}.v of gororoba-open;
   a change goes through the generator. Inventory holds the statements of
   that file, each with its proof, for every rights relation. inventory
   lists the rights they name, and inventory_is_chain_table identifies it
   with chain_table {size} of Model.v. *)

From Stdlib Require Import String List.
From GororobaDelegation Require Import Model.
Import ListNotations.

Open Scope string_scope.

Module Inventory (R : RIGHTS).
Module D := Reachability R.
Import R D.

{statements}
End Inventory.

Definition inventory : list (string * string * Action) :=
  [{held}].

Lemma inventory_is_chain_table : inventory = chain_table {size}.
Proof. vm_compute. reflexivity. Qed.

Module Size <: SIZE.
  Definition n := {size}.
End Size.

Module System := Chain Size.
Module Statements := Inventory System.R.

(* Each right an inventory statement names is held in the chain. *)
Theorem inventory_held :
  Forall (fun r => chain_right {size} (fst (fst r)) (snd (fst r)) (snd r))
    inventory.
Proof. rewrite inventory_is_chain_table. apply chain_table_held. Qed.

(* So the conclusion of each inventory statement holds outright. *)
Theorem inventory_reachable :
  Forall (fun r => System.D.reachable_delegation
                     (fst (fst r)) (snd (fst r)) (snd r))
    inventory.
Proof.
  rewrite inventory_is_chain_table. exact System.chain_table_reachable.
Qed.
"""


def main(argv):
    if len(argv) != 3 or not argv[2].isdigit():
        print(__doc__, file=sys.stderr)
        raise SystemExit(2)
    with open(argv[1], encoding="ascii", newline="") as handle:
        rows = parse(handle.read())
    sys.stdout.write(render(rows, int(argv[2])))


if __name__ == "__main__":
    main(sys.argv)
