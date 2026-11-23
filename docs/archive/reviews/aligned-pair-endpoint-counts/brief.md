# Brief: pull request 96 of gororoba-math, endpoint counts of the aligned-pair spectrum (findings row A5-262)

Read first: the workspace `AGENTS.md`, the sections "Reviews and merges detail" and "Comments, commits and pull-request detail" of `workspace/reference.md` in gororoba-infrastructure, then `AGENTS.md` of this repository ("Statements and proofs", "Rocq sources"). Work read-only: change no file; never commit, push, stash, submit to a provider or start a cloud resource; spawn no subagents. Run no Lean, Lake, Rocq, opam, Python batch or test suite on the review host; the measured build results are listed below as claims with their evidence class. Keep within 25 minutes.

Material: branch `lean/aligned-pair-endpoint-counts`, read through `git diff origin/main...HEAD` and the files in place. The findings ledger is `docs/evidence/a5-exceptional-fibers/ledger.tsv` of gororoba-quantum (rows by id).


## Claims under review (each is a claim, not a fact; justify or falsify it)

1. lean/GororobaMath/CayleyDickson/AlignedPairEndpoints.lean: `Tower.alignedPairCountMultiplicity_succ_top` (for 3 <= k, the number of ordered pairs of level k + 1 with count 2^k - 4 is 2 * zeroCount k) and `Tower.zeroCount_succ` (for 3 <= k, zeroCount (k + 1) = 2 * zeroCount k + 6 * (2^k - 1)) are proved, and `zeroCount` counts what its docstring says. Status: proved (measured: `lake build --wfail` exit 0, `#print axioms` = propext, Classical.choice, Quot.sound, `lake env leanchecker` exit 0, Lean 4.35.0, Mathlib v4.35.0; independent of the recurrences, `decide +kernel` evaluates zeroCount 5 = 342 and alignedPairCountMultiplicity 5 12 = 252 directly). Falsifier: a level where the recurrence fails by a hand count; a definition of zeroCount that differs from the source's zero-nullity operands; a bound 3 <= k that is not needed or not sufficient.
2. The derived values (84, 252, 684, 1740 at levels 4 to 7; zeroCount 5 = 342) are the counts of findings row A5-262 of gororoba-quantum, with the source's unsigned counts 171 and 126 equal to half the ordered ones. Status: hypothesis. Falsifier: a reading of the source row (ordered against unordered pairs, signs, the exclusion of zero and equal indices) under which the numbers do not correspond.
3. The row A5-262 of ci/claims/ledger.tsv stays `partial` with an accurate note. Status: computed (`python3 ci/check_claims_ledger.py` passes).
4. The definitions `zeroPred`, `zeroCount` and `consPairEquiv` mirror no function of gororoba-quantum in the sense of AGENTS.md ("A definition that mirrors code in another gororoba repository ..."); look at docs/evidence/pathion-kernel-map/census.py there. Status: hypothesis.
5. Docstrings follow the comment rules; helper lemmas that only serve this file do not pollute a shared namespace with names likely to clash.

## Questions to answer

- Defects: code, claims and records, with file:line.
- Is any helper lemma already in Mathlib or in the library under another name?

Report ranked by consequence, every finding tied to a file:line, a command with its output, or a theorem name, each marked proved, computed, measured or hypothesis, with a severity P1 to P3. Print the report as your answer, under 150 lines.
