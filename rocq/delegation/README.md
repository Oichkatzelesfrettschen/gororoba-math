# rocq/delegation

A model of delegation of rights between named subjects, and the three
statement inventories of gororoba-open rendered with their proofs. Logical
root `GororobaDelegation`; compiled with `-w +default`; no axiom
(`kernel-assumptions.txt` is empty).

## What is trivially true and what carries content

The inventories (`confine_theorems_512.v`, `_1024.v`, `_2048.v` under
`curated/01_theory_frameworks/` of gororoba-open; 2,590, 5,182 and 10,366
statements) state, for one right at a time,
`has_right S O A -> reachable_delegation S O A`. In any semantics where a
held right is reachable, that is one constructor. The 18,138 proofs in
`Inventory512.v`, `Inventory1024.v` and `Inventory2048.v` are each
`exact (rd_direct _ _ _)`, they hold for every rights relation (the functor
`Inventory` takes one as its argument), and they hold equally in the three
semantics below. They establish that the statements are well formed over the
model and nothing about any particular system.

The content is in four places:

- `inventory_is_chain_table` (each inventory source): the rights the
  statements name, in order, are `chain_table 16 N`, computed by the kernel.
  This identifies which system the inventories enumerate. The list
  `stated` inside the functor pairs each right with the theorem about it
  and typechecks only when the theorem is about that right; `inventory` is
  the list of those rights, and `ci/check_rocq.sh` requires as many entries
  as theorems.
- `chain_table_spec` (`Model.v`): for a period `p <> 0` the table lists
  exactly the rights `chain_right p n` holds.
- `chain_reachable_iff`: in that system thread `i` reaches exactly the
  rights held by the threads `j >= i`; `chain_arena_iff` is the exact form
  for an arena.
- The theorems that separate the semantics (next section).

`inventory_held` and `inventory_reachable` then discharge the hypothesis of
every inventory statement in the chain.

## Three semantics of a delegation step

A subject that holds `Grant` on an object delegates through that object's
owner. `Reachability` (a functor over the rights and owner relations)
defines:

| Relation | A step conveys | A conveyed `Grant` conveys again |
|---|---|---|
| `reachable_delegation` | whatever the owner reaches | yes |
| `restricted_delegation P` | what the owner reaches, for actions satisfying `P` | only if `P Grant` |
| `single_delegation` | what the owner holds | no |

`restricted_reachable`, `unrestricted_iff` and `single_reachable` order
them, for every rights relation. Two further facts hold for every rights
relation: `restricted_iff` (a right is reachable under `P` exactly when it
is held, or its action satisfies `P` and the closure reaches it, so a
restriction acts on the action alone) and `reached_grant_delegates` (in
the closure a reached `Grant` delegates as a held one does). On the chain the reachable sets are, for every size and period:

| Theorem | Thread `i` reaches `(o, a)` exactly when |
|---|---|
| `chain_reachable_iff` | some thread `j >= i` holds it |
| `chain_restricted_iff` | `i` holds it, or `P a` and some `j > i` holds it |
| `chain_single_iff` | `i` or `i + 1` holds it |

The theorem that changes with the answer to "does `Grant` delegate
`Grant`": `chain_grant_iff` (closure: `Grant` on the object of thread `j`
is reachable from `i` exactly when `i < j < n`) against
`chain_restricted_grant` (with `P a := a <> Grant`: exactly when
`j = i + 1 < n`). By `restricted_iff` the restriction changes nothing for
the other actions, and `chain_single_weaker` exhibits a right
two threads up that the closure reaches and one step does not.

## One statement for every size and period

`chain_right p n` has the arena period `p` and the size `n` as parameters,
and the functor `Chain` proves every theorem above for an arbitrary
`SIZE` (a `period` and an `n`, with no side condition; only the table
lemmas need `p <> 0`). The three inventories are the instances
`period := 16` and `n := 512, 1024, 2048` (`Module System := Chain Size` in
each inventory source). `chain_confined_thread` (`i <= j` for a reachable
thread object) and `chain_confined_arena` (`Map` only, and `i <= p k`) are
the confinement corollaries.

## Is the chain the intended system

Claim: the inventories were written to describe the chain with period 16.

- Evidence for: `inventory_is_chain_table` holds for all three (equality of
  ordered lists of 2,590, 5,182 and 10,366 triples), which is
  `5 n - 2 + n / 16` at these three sizes, each a multiple of 16.
- What the inventories do not determine: they list rights and never an
  owner. The owner relation here (object `Thread i` names subject
  `Thread_i`) is this tree's reading of the two spellings. They also never
  state that a right is absent, so the closed-world reading (a right not
  listed is not held) is an assumption of `chain_right`.
- Falsifiers: (1) a generator or specification of the inventories that
  names a right outside `chain_table 16 N`, another owner relation, or
  another delegation rule; (2) an inventory of another size from the same
  origin that differs from `chain_table 16 N`.
- Search made (gororoba-open, all refs, 2026-11-15, `git log --all
  --name-only -S` for `reachable_delegation` and for `arena_`): the
  inventories and a model file that declares `has_right` and
  `reachable_delegation` as parameters arrive in the initial commit
  63598e85 together with `bin/coq_prepare_confine.py`, which rewrites
  `Theorem` to `Axiom` so the files typecheck, and a `make coq` target that
  compiles the result. No commit holds a generator of the statements, and no
  tracked file outside the ten names a thread or an arena. One origin record
  speaks of the semantics: the roadmap of that commit
  (`docs/ULTRA_ROADMAP.md`, section F) lists as open "Decide the actual
  semantics for `has_right` / `reachable_delegation`" and "Prove a minimal
  non-trivial theorem end-to-end (no axioms)"; later commits carry the same
  two lines through registry files, and the current tree holds neither. So
  the origin fixed no semantics: the owner relation, the closure and the
  closed-world reading are decisions of this tree, the claim that the chain
  was intended is unfalsified, and no origin record confirms it.

## Relation to the literature

Read on 2026-11-15, at the pages cited, in the versions named; a statement
about a paper below rests on those pages only, and every page cited was
opened in the PDF.

- Lipton and Snyder, "A Linear Time Algorithm for Deciding Subject
  Security", Yale Research Report 72, June 1976 (the report version; the
  JACM 1977 and FOCS 1976 texts were not read). Rule 1 (section I, p. 3):
  "Intuitively x takes the ability to do alpha to z from y." The holder
  pulls. Section I, p. 2: "if the rules R only allowed the addition of
  edges, then these problems would be easily solved by known methods"; the
  rules that add vertices make the problem hard.
- Bishop and Snyder, "The Transfer of Information and Authority in a
  Protection System", Yale report YALE/DCS/rr-166 (the report version of
  the SOSP 1979 paper). Section 4, p. 16: take reads "x takes (alpha to z)
  from y" (x holds t over y), grant reads "x grants (alpha to z) to y"
  (x holds g over y). Theorem 4.1 (p. 19) characterizes `can.share` over
  the rules take, grant, create and remove.
- Harrison, Ruzzo and Ullman, "On Protection in Operating Systems", SOSP
  1975 (the conference version; the CACM 1976 text was not read). Theorem 1
  (section IV, p. 21): safety is decidable for mono-operational systems.
  Theorem 2 (section V, p. 22): "It is undecidable whether a given
  configuration of a given protection system is safe for a given generic
  right."
- Lampson, "A Note on the Confinement Problem", CACM 16(10), 1973. The
  abstract (p. 1) defines confinement as keeping a program from
  transmitting "information to any other program except its caller"; the
  note states conditions and no theorem.
- Elkaduwe, Klein and Elphinstone, "Verified Protection Model of the seL4
  Microkernel", NICTA technical report (the report version of the VSTTE
  2008 paper; pp. 1-8 and 11-17 read). Section 3.2, p. 6: "The take rule of
  take-grant is not employed by the seL4 kernel. All authority propagations
  are grant operations." Theorem 1 (section 6, p. 15), machine-checked in
  Isabelle/HOL by the paper's account: entities that are not connected
  never leak authority to each other, where connected is a symmetric
  closure.
- Miller, Yee and Shapiro, "Capability Myths Demolished", SRL-2003-02
  (pp. 1 and 4-7 read). Under "Achieving Confinement", p. 5: "no capability
  transfer can introduce a new connection between two objects that were not
  already connected by some path".

What the comparison shows:

- Direction. The step of this model (the holder of `Grant` on an object
  reaches what the object's owner reaches) has the direction of the take
  rule of Lipton-Snyder and Bishop-Snyder: authority flows to the holder.
  The action is spelled `Grant` because the inventories spell it so; in
  the vocabulary of those papers it is the take right. seL4's rule and the
  delegation of Miller et al. flow the other way.
- Re-delegation. In the take-grant rules the transferred label may contain
  the transfer right (Bishop-Snyder, Figure 4, p. 18: "a takes (g to b)
  from d"), which is the choice `reachable_delegation` makes. The
  restrictions on those pages are chosen per act (a subset of the label in
  take-grant; the rights mask of seL4's grant, p. 8; "other than own" in
  the CONFER command of Harrison et al., p. 16). A filter applied to every
  step, as `restricted_delegation P`, and a one-step rule, as
  `single_delegation`, do not appear on the pages read.
- Theorem. `chain_reachable_iff` is not an instance of Bishop-Snyder
  Theorem 4.1. That theorem's rules include create, under which the
  direction of the arcs along a path does not matter (Lipton-Snyder,
  Lemma 3, p. 11: "the directionality and labels along a connected path
  are unimportant"), so on the same chain `can.share` also holds from a
  higher thread to a lower one, which `chain_confined_thread` excludes.
  This model is the closure under the take rule alone on a fixed graph: the
  edge-only case that Lipton and Snyder set aside as easy. Its directed
  bound holds because the model has no create and no grant rule. (The
  application of Theorem 4.1 to the chain is an inference from the
  definitions on pp. 17 and 19, not a statement of the paper.)
- Confinement. The word names different things. Lampson's confinement is
  about information channels and has no counterpart here. The bound of
  Miller et al. and Theorem 1 of Elkaduwe et al. are connectivity bounds on
  authority in systems with creation; `chain_confined_thread` is a bound of
  that kind on one static graph, sharper (directed, with a converse) and
  far narrower (no creation, no removal, no grant rule, no de facto flow).

Novelty, bounded by those pages: `chain_reachable_iff` and its corollaries
restate closure reachability under a take-style rule on a special graph and
claim nothing new about protection systems. Not addressed on the pages
read: the every-step filter and the one-step rule with their exact
reachable sets on the chain, the chain family with an arena period, and a
Rocq statement of a directed characterization with its converse. Whether
those appear elsewhere in the literature was not searched beyond these six
works.

## Sources and checks

- `Model.v` is written by hand. The three inventory sources are rendered by
  `ci/delegation-sources/render_inventory.py`; a change goes through it.
- `GOROROBA_OPEN=PATH sh ci/check_delegation_sources.sh` (on demand) renders
  them again from the gororoba-open checkout, whose three inventories it
  pins by sha256, and requires the statements of each rendered source to be
  the bytes of the inventory with one final newline added (each inventory
  ends without one).
- `ci/check_rocq.sh` compiles the tree, scans it for admissions and compares
  the kernel checker's axiom report with the empty ledger.
