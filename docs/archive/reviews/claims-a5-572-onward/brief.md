# Brief: gororoba-math PR 127, claims-ledger rows A5-572 to A5-611 and the findings pin at 57c2c08bf

Read first: the workspace AGENTS.md, then gororoba-infrastructure workspace/reference.md ("Reviews and merges detail"), then AGENTS.md ("Statements and proofs": the placement clauses) and ci/claims/README.md (columns and rules). Work read-only: change no file except printing your report as your final answer; never commit, push or stash; spawn no subagents. You may run git and read files; keep each computation under 10 minutes.

Material: worktree this repository, branch ci/claims-a5-572-onward (PR 127, head 0c2e44edf), diff against origin/main. Source of each row: gororoba-quantum at commit 57c2c08bf, docs/evidence/a5-exceptional-fibers/ledger.tsv (use git show 57c2c08bf:PATH).

## Claims under review (each a claim, not a fact)
1. The 40 added rows A5-572..A5-611 each quote their source row correctly (statement at most 30 words, source line number right) and carry the placement, clause, quantifier and status the AGENTS.md clauses give.
2. A5-591 and A5-592 are partial with proof entries that name existing declarations of rocq/quantum/E8ConjugationMap.v and E8ConjugationIdeal.v, and their notes state what stays open.
3. The rewritten rows A5-571 and A5-542 follow the status change of their source rows.
4. expected-sources.tsv changed only in commit and digest columns for the findings ledger; topic notes stay at b7c2b373; QUANTUM_FINDINGS in expected_sources.py implements that split without changing other sources.
5. The nine placements the author flags as uncertain (A5-577, A5-588, A5-583, A5-596, A5-601, A5-603, A5-590, A5-611, A5-542): give for each your placement and the clause that decides it.

## Report
For each claim: justified or falsified, with file and line evidence. Then any further defect. Then conjectures: structure the rows suggest that no record states, with a falsifier. Print the whole report as your final answer.
