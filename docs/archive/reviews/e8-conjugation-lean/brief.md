# Brief: gororoba-math PR 129 (branch lean/e8-conjugation, head ec79877eb)

Read first: the workspace AGENTS.md at AGENTS.md, then AGENTS.md ("Statements and proofs", "Rocq sources"). Work read-only: change no file anywhere, commit nothing, run no build, no Python, no Lean or Rocq process (the shared hosts ran out of memory twice today), spawn no subagent; print your whole report as your final answer. You may read files and run git (git show, git diff, git grep) in  the diff under review is origin/main...ec79877eb.

Classify every finding as proved (by reading the source), computed (with the command), or hypothesis, with file and line.

## Claims under review
1. The 27 generator lists jm and jp in lean/GororobaMath/CayleyDickson/E8ConjugationIdeal.lean equal the two "ideal J=" lists of gororoba-quantum docs/evidence/a5-exceptional-fibers/working/runs/e8-rees-fibers-v3-open-cells/conjugation/conjugation_map.sing (read with git -C gororoba-quantum show origin/main:PATH), up to the variable order (i, s1..s9).
2. jm_phi states the conjugation Phi (i -> -i, s4 -> -s5, s5 -> s4, s7 <-> s8) and the signs -1 exactly at k+1 = 5, 7, 8, 10, 13, 16, 19, 21, 23, 26; jm_phi_flip states the same after flipping s3, s4, s5, s6 with no sign; span_phi_jm and span_phiFlip_jm state ideal equalities in MvPolynomial over every CommRing.
3. The four maxHeartbeats 1600000 raises are scoped to single declarations and needed; nothing weakens the statements.
4. rocq/quantum/E8ConjugationIdealBridge.v names the Lean theorems by path and name and states their integer instance; its narrowing (integer values, not the polynomial ring) is stated.
5. ci/compare_e8_conjugation.sh and the AGENTS.md sentence describe the same mechanism, and the generator refuses an input with another sha256.

## Report
For each claim: justified or falsified with evidence. Then defects beyond the claims. Then conjectures the material suggests, each with a falsifier.
