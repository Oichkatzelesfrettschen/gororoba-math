# Brief: pull request 95 of gororoba-math, Lean proofs for findings rows A5-177, A5-238, A5-467 and A5-470

Read first: the workspace `AGENTS.md`, the sections "Reviews and merges detail" and "Comments, commits and pull-request detail" of `workspace/reference.md` in gororoba-infrastructure, then `AGENTS.md` of this repository ("Statements and proofs", "Rocq sources"). Work read-only: change no file; never commit, push, stash, submit to a provider or start a cloud resource; spawn no subagents. Run no Lean, Lake, Rocq, opam, Python batch or test suite on the review host; the measured build results are listed below as claims with their evidence class. Keep within 25 minutes.

Material: branch `lean/sandwich-trace-symmetric-forms`, read through `git diff origin/main...HEAD` and the files in place. The findings ledger is `docs/evidence/a5-exceptional-fibers/ledger.tsv` of gororoba-quantum (rows by id).

The red-team seats received the same brief with one added paragraph: assume each claim is wrong, look for the cheapest refutation (a counterexample at a small level or ring, a vacuous hypothesis, a statement weaker than its docstring, a ledger status that overstates), report only refutations tied to a line or a computation by hand, and say plainly when an attack fails.

## Claims under review (each is a claim, not a fact; justify or falsify it)

1. lean/GororobaMath/CayleyDickson/SandwichTrace.lean: `Matrix.skew_mul_mul_skew`, `trace_mul_skew_mul_skew`, `trace_mul_skew_mul_skew_of_rank_one` and `trace_mul_skew_mul_skew_eq_zero_iff` state the expansion of findings row A5-467 and the trace identity and rank-one clause of row A5-470, with the signs and index order of the rows. Status: proved (measured: `lake build --wfail` exit 0, `#print axioms` = propext, Classical.choice, Quot.sound, `lake env leanchecker` exit 0, Lean 4.35.0, Mathlib v4.35.0; the 2 x 2 integer instance evaluates to -2 by `decide`). Falsifier: a sign or a hypothesis that differs from the rows; a vacuous hypothesis set in the equivalence; a hypothesis the proof does not use.
2. lean/GororobaMath/KernelMap/EstimatorWalsh.lean states the spectral form of row A5-238 over an abstract orthogonal character family, its two readings, and the orthogonality of the Walsh characters of `Fin d -> Bool` for every d. Status: proved (same measurements). Falsifier: a statement that holds only by the convention x / 0 = 0 where the row means a real reading; a hypothesis set no character family satisfies; a mismatch with the source README docs/evidence/pathion-kernel-map/nhat-bias/README.md (lines 174 to 190) of gororoba-quantum.
3. lean/GororobaMath/CayleyDickson/TwoTermScalar.lean: for t * t != 1 over an ordered domain, left multiplication by e_i + t e_j has zero kernel at every level, for every pair of indices. Status: proved (same measurements; the instance e_1 + 2 e_18 at level 5 over the integers elaborates). Falsifier: a counterexample (try i = j, i = 0, t = 0, small levels by hand); a hypothesis the proof does not use.
4. The rows A5-177, A5-238 and A5-470 of ci/claims/ledger.tsv (all `partial`) and the tally of ci/claims/README.md (12 lean owed, 7 lean partial) follow ci/claims/README.md, and each note names what is open. Status: computed (`python3 ci/check_claims_ledger.py` passes). Falsifier: an open clause of a source row that a note omits; a listed declaration that does not exist.
5. The three definitions `KernelMap.sgn`, `KernelMap.coeff` and `KernelMap.walshChar` need no comparison script under ci/ by AGENTS.md ("A definition that mirrors code in another gororoba repository ..."). Status: hypothesis. Falsifier: code in gororoba-quantum (docs/evidence/pathion-kernel-map/nhat-bias/nhat_spectral.py) that these definitions mirror in the sense of that rule.
6. Docstrings follow the comment rules (convention first, mechanism, no session narration); each theorem sits at the generality its proof has.

## Questions to answer

- Defects: code, claims and records, with file:line.
- Which hypotheses can be dropped or weakened (CharZero, DecidableEq, the order hypotheses)?
- For row A5-262 (counts 84, 252, 684, 1740 and 171 against 126): the cheapest Lean statement that closes the counts, given lean/GororobaMath/CayleyDickson/TwoTermRecursion.lean and AlignedPairSpectrum.lean.

Report ranked by consequence, every finding tied to a file:line, a command with its output, or a theorem name, each marked proved, computed, measured or hypothesis, with a severity P1 to P3. Print the report as your answer, under 150 lines.
