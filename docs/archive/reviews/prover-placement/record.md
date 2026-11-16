# Review: AGENTS.md prover placement and dual proofs of headline results (pull request 45)

## Brief

A read-only reviewer received the pull request (first head 7f722f1) and six claims to justify or falsify: the
count of Rocq sources cited by sha256 (389 of 410), the Rocq-only receipt evidence of gororoba-open, the absence of a
Cayley-Dickson development in Mathlib v4.35.0 and the associativity of MathComp's rings, the extraction and
floating-point routes, the consistency of the new text with the rest of AGENTS.md, and that the ordered list gives
every kind of result exactly one home.

## Reviewer: codex (gpt-daybreak-blue, high), on 7f722f1

| # | Finding | Severity | Reconciliation |
|---|---|---|---|
| 1 | The digest census holds: 410 tracked Rocq sources, 389 cited | P3 | Confirmed; the same count was made independently before the PR. |
| 2 | gororoba-open runs no prover and admits Rocq 9.3.0 evidence (theorem_replay.rs:1, 16, 472; proofs.yml:8; Makefile:329) | P3 | Confirmed; no change. |
| 3 | Mathlib holds no CD or octonion development; MathComp's semiring mixin requires mulrA (rings_modules_and_algebras.v:585) | P3 | Confirmed: `mulrA : associative mul` sits at lines 588 and 609 of mathcomp/algebra/algebraic_hierarchy/rings_modules_and_algebras.v in MathComp 2.6.0; the statement moves from hypothesis to documented. |
| 4 | The extraction routes are supported; "relate" must not read as verified compilation | P3 | Accepted: the revision says the routes tie code to Gallina terms "within the trusted base that the extraction skill records". |
| 5 | The headline set is unbounded: the Rocq-trees section names the delegation inventories (18,144 generated statements), and the Lean-table definition of a headline theorem differs | P1 | Accepted. The revision defines a headline result as a row of ci/headline-results.tsv (28 Lean theorems from the README table, partner owed, tracked by issue 46), excludes the generated inventories, makes the rule bind new rows from 2026-11-16 on, and makes the challenge-module bullet read the same registry. |
| 6 | The ordered list leaves a fixed-algebra symbolic theorem without a home and sends a ring-general certificate to two | P1 | Accepted. The revision places on two axes (statement, evidence) with a rule for fixed-algebra statements, and joins a claim on both axes by an instance bridge that names the Lean theorem and the substituted values. |

The reviewer also proposed the structural statement that theorem generality and evidence binding are independent
axes; the revision adopts it.

## Advisor, on 28ccb05

The Advisor confirmed findings 1 to 5 as reconciled, and 3 after the MathComp line was opened. For finding 4 it asked
that Flocq stand apart from the extraction routes and that the Skills section name the extraction skill. It judged
finding 6 only partly fixed: the Statement item still sent a fixed-level count decided by evaluation to both
provers. It also found three regressions against the text the PR replaced: the phrase "the same claim, read through
each side's convention docstring" was gone, as was "a result already in either tree stays where it is", and the
text carried a date. It asked for a README pointer to the registry and for matching existing Rocq proofs as the
first step of issue 46. Each is fixed in the commit after 28ccb05: a fixed-level instance of a Lean theorem stays
beside it, a row may record a narrower partner, both phrases return, the date goes, Flocq has its own sentence, and
the Skills section and README.md name the extraction skill and the registry.

The Advisor also noted an interaction with pull request 42, which adds five NonAssociative theorems to the README
table and new Rocq analysis successors. Pull request 42 merges first; this pull request then adds the five rows to
the registry.

## Brief (path-free copy)

Read the workspace AGENTS.md and the repository AGENTS.md first; work read-only. Claims: (1) 389 of 410 tracked
Rocq sources are cited by sha256 in gororoba-open or gororoba-quantum; (2) gororoba-open runs no prover and admits
Rocq kernel replay evidence only; (3) Mathlib v4.35.0 has no Cayley-Dickson or octonion development and MathComp's
rings are associative; (4) CertiRocq exists for Rocq 9.1 only, Flocq models IEEE 754, Lean's compiled code has no
proof tying it to the kernel term; (5) the new text is consistent with the rest of AGENTS.md and the README defines a
checkable headline set; (6) the ordered list gives every kind of result one home. Questions: is the concrete-data
clause decidable, is the dual-proof workload bounded, and what structural statement is missing.
