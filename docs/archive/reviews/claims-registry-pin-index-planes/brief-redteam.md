# Brief: claims-ledger rows of gororoba-math pull request 102

Read first: the workspace `AGENTS.md` (in the directory above this checkout), then `ci/claims/README.md` of this working directory (gororoba-math, branch claims-registry-pin-index-plane-successors at commit 01ae7fccf). Work read-only: change no file; never commit, push, stash, submit to a provider or start a cloud resource; spawn no subagents. Run no Rocq, opam, Lean, Lake, cargo, Python, test suite or gate on this host; read sources and use git and grep only. Keep within 25 minutes.

Material:
- The change: `git diff origin/main...HEAD -- ci/claims/ledger.tsv ci/claims/README.md ci/claims/expected_sources.py` (expected-sources.tsv is generated; skip it).
- The registry statements: `git -C GOROROBA_OPEN show 3c04c2eb:registry/claims.toml`, claims C-124, C-581, C-1469, C-1141, C-922, C-1787, C-1789, C-1792, C-1793, C-1794, and C-1785, C-1786, C-1788, C-1790, C-1791.
- The cited proofs: rocq/open/verified/C582_IndexPlaneIncidence.v, C029_SedenionOctonionSubalgebras.v, C029_FermionGenerationArithmetic.v, C1141_ZDGraphGeneralStructure.v; lean/GororobaMath/CayleyDickson/Alternative.lean and FlexibleLaw.lean.

## Claims under review (each is a claim, not a fact; justify or falsify it)

1. Each new row that reads `proved` (C-1787, C-1789, C-1792, C-1793) lists declarations that together state the whole registry statement at its generality, by the README rule for `proved`. Falsifier: a clause of the full registry statement (not the 30-word cut) that no listed declaration states, a declaration whose hypotheses are stronger than the clause (ring class, level range, index range), or a listed name that is absent from the file.
2. The C-1794 row is `partial` and its note names everything the proofs leave open. Falsifier: another unproved clause, or a reading under which the row should be `proved`.
3. The rows C-124, C-581, C-1469 and C-1141 take the right clause, placement and status for a claim the registry marks Superseded, and each note names the right successor and a true reason.
4. The quantifier, placement and clause of each new row follow the placement clauses of the README and of AGENTS.md ("Statements and proofs").
5. Leaving C-1785, C-1786, C-1788, C-1790 and C-1791 outside the ledger is consistent with how the ledger chose its 500 earlier claims. Falsifier: an earlier ledger row of the same kind.
6. The README counts (1607, 505, 194) are right, and no other count or commit in ci/claims/README.md or AGENTS.md went stale.

## Red-team task

Try to break the claims rather than audit them: a theorem stated on the integer tower cited for a statement about real spans, a count that depends on including index 0, a level bound off by one, a ring hypothesis the statement omits, a row whose proof list duplicates another row's in a way the rules forbid, a stale number. State each attack, whether it succeeded, and the evidence.

Report ranked by consequence, every finding tied to a file:line or a theorem name, each marked proved, read or hypothesis, with a severity P1 to P3. Print the report as your answer, under 100 lines.
