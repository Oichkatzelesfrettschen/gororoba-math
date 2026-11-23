# Brief: pull request 94 of gororoba-math, Rocq instance bridges of three fixed-level certificates

Read first: the workspace `AGENTS.md`, the sections "Reviews and merges detail" and "Comments, commits and pull-request detail" of `workspace/reference.md` in gororoba-infrastructure, then `AGENTS.md` of this repository ("Statements and proofs", "Rocq sources"). Work read-only: change no file; never commit, push, stash, submit to a provider or start a cloud resource; spawn no subagents. Run no Lean, Lake, Rocq, opam, Python batch or test suite on the review host; the measured build results are listed below as claims with their evidence class. Keep within 25 minutes.

Material: branch `rocq/fixed-level-instance-bridges`, read through `git diff origin/main...HEAD` and the files in place. The findings ledger is `docs/evidence/a5-exceptional-fibers/ledger.tsv` of gororoba-quantum (rows by id).

The red-team seats received the same brief with one added paragraph: assume each claim is wrong, look for the cheapest refutation (a counterexample at a small level or ring, a vacuous hypothesis, a statement weaker than its docstring, a ledger status that overstates), report only refutations tied to a line or a computation by hand, and say plainly when an attack fails.

## Claims under review (each is a claim, not a fact; justify or falsify it)

1. Each of rocq/quantum/CdTowerCanonicalKernelsBridge.v, A5W8ArcMatrixRanksBridge.v and CdTwistedProductBridge.v is an instance bridge in the sense of AGENTS.md ("Statements and proofs"): its comment names the Lean theorem by path and name and the substituted values, and its statement is the substituted proposition, with each narrowing stated. The Lean theorems are in lean/GororobaMath/CayleyDickson/KernelCertificate.lean, Certificates.lean and Ideals.lean. Status: hypothesis. Falsifier: a substitution in a header that the Lean statement does not admit (a hypothesis of the Lean theorem with no Rocq counterpart named, a wrong parameter), or a Rocq statement that differs from the theorem of the source it restates.
2. The three files compile under `-w all,+default` and their theorems are closed under the global context. Status: measured (Rocq 9.3.0, x86_64: `rocq c` exit 0 for each; `Print Assumptions` at Zmod7 and Zmod5 prints "Closed under the global context"; the hosted `rocq` workflow, which runs ci/check_rocq.sh, is green on the head). Falsifier: an axiom or Admitted reachable from a bridge theorem.
3. The four rows added to ci/rocq-warnings/allowed.tsv are the warnings the three files print, each a name ci/rocq-warnings/causes.tsv lists, in sorted order. Status: measured. Falsifier: a missing or surplus row.
4. Findings row A5-500 may read `proved` in ci/claims/ledger.tsv: G2DerivationBridge.derivation_dimension_certificate of rocq/quantum/CdTowerG2DerivationBridge.v with the listed spanning theorems states the whole claim of the row (read the row in the gororoba-quantum ledger). Row A5-453 stays `partial` with derivations_independent added. Status: hypothesis. Falsifier: a clause of A5-500 (for example the form F = sum r_t D_t where 6 is a nonzero divisor, or the free-module statement) that no listed declaration states under ci/claims/README.md.
5. docs/plans/lean-generalizations.md and .tsv rows 118, 120 and 121 describe the bridges accurately.
6. No source that a retained record cites by sha256 changed bytes (the three bridges are new files; _RocqProject, allowed.tsv, the ledger and the plan are the only edits).

## Questions to answer

- Defects: code, claims and records, with file:line.
- Is the two-theorem form of the W8 kernel bridge (spanning formula and independence) a fair reading of the Lean Basis statement, and does the header say so correctly?
- Does the functor of each bridge take the same module arguments as the source functor, so that an instance of the bridge is an instance of the source theorem?

Report ranked by consequence, every finding tied to a file:line, a command with its output, or a theorem name, each marked proved, computed, measured or hypothesis, with a severity P1 to P3. Print the report as your answer, under 150 lines.
