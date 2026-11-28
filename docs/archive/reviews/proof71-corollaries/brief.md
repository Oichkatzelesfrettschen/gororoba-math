# Brief: review of gororoba-math branch lean/partial-row-corollaries (head 577abfab8)

Read first: AGENTS.md, then gororoba-math AGENTS.md ("Statements and proofs", "Proof hygiene") and ci/claims/README.md. Work read-only: change no file; never commit, push or stash; spawn no subagents; run only git and read commands, each under 10 minutes (no lake build: the build host runs no jobs). Print the whole report as your final answer.

Material: worktree .; read `git diff origin/main...HEAD`. Three new Lean modules under lean/GororobaMath/CayleyDickson/ (AssociatorPhaseNonzero.lean, SquareZero.lean, AnticommutingAssociator.lean), their imports in lean/GororobaMath.lean, and three rewritten rows A5-622, A5-649, A5-661 of ci/claims/ledger.tsv with the README count line. The source of each row is gororoba-quantum (checkout gororoba-quantum) at commit 6d2cdac90, docs/evidence/a5-exceptional-fibers/ledger.tsv; read it with `git -C gororoba-quantum show 6d2cdac90:docs/evidence/a5-exceptional-fibers/ledger.tsv`.

Evidence so far (measured on an aarch64 lab host, Lean 4.35.0, Mathlib v4.35.0): the three modules build with `lake build --wfail`; `#print axioms` of each new theorem lists only propext, Classical.choice and Quot.sound (associator_add_associator_swap_of_anticomm: propext alone); `lake env leanchecker` replays each module, one per call. The import of GororobaMath.CayleyDickson.Associator into AnticommutingAssociator.lean was added after that replay, so that `associator` there names CayleyDickson.associator, not Mathlib's root `associator`; the full gate on the head runs separately.

## Claims under review (each with its falsifier)
1. Each statement says what its docstring says, at the generality its proof has. Falsifier: a hypothesis that is unused or stronger than needed, or a conclusion weaker than the docstring (check `(2 : R) ≠ 0` in AssociatorPhaseNonzero, `Field F` in SquareZero, and whether any theorem could be stated over a wider class without a new proof idea).
2. The field hypothesis of SquareZero is necessary: over a commutative ring with 2 a unit, ε • 1 with ε² = 0 squares to zero with re ≠ 0. Falsifier: an error in that counterexample, or a domain hypothesis (NoZeroDivisors with 2 ≠ 0) that suffices with the same proof.
3. `associator` in all three modules is CayleyDickson.associator (Associator.lean:47). Falsifier: a name that resolves to Mathlib's `_root_.associator`.
4. A5-649 reads proved: card_associator_e_e_e_ne_zero with ne_zero_of_associator_e_e_e_ne_zero states the source claim (ordered triples of imaginary basis units with nonzero associator number (D - 2)(D - 4)(D + 6)/2 for every D = 2^n >= 4). Falsifier: a gap between the doubled count over all index triples and the source's count over imaginary triples, or a ring the source uses that has 2 = 0.
5. A5-661 stays partial, with only the seven enumerated counts open; A5-622 stays partial, with only the A5-612 slice readings open. Falsifier: a further clause of either source claim that no cited declaration states, or one the new theorems do not cover as the note says.
6. The README counts (14 lean owed; 18 lean partial; 2 lean proved) equal the ledger, and every proof entry names a declaration that exists. Falsifier: a count or a missing declaration.
7. The modules follow Proof hygiene: a non-terminal `simp` is `simp only`; no file-wide option; module docstring states the convention first. Falsifier: a violation with its line.

## Report
For each claim: justified or falsified, with file and line evidence. Then further defects. Then conjectures: structure these corollaries suggest that no record states (for instance the A5-662 counts through mul_self_eq_zero_iff), each with a falsifier and its cheapest test.
