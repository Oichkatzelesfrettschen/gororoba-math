# Brief: gororoba-math PR 130 (branch lean/eisenbud-goto, head 3978afe34)

Read first: the workspace AGENTS.md at AGENTS.md, then AGENTS.md ("Statements and proofs", "Rocq sources"). Work read-only: change no file anywhere, commit nothing, run no build, no Python, no Lean or Rocq process (the shared hosts ran out of memory twice today), spawn no subagent; print your whole report as your final answer. You may read files and run git (git show, git diff, git grep) in  the diff under review is origin/main...3978afe34.

Classify every finding as proved (by reading the source), computed (with the command), or hypothesis, with file and line.

## Claims under review
1. lean/GororobaMath/EisenbudGoto/MinimalMultiplicity.lean states, for every c and d: the Hilbert function of (1 + c t)/(1 - t)^(d+1) (coeff_hilbertSeries), agreement with Mathlib's hilbertPoly for n >= 2 (eval_hilbertPoly), the polynomial identity (1 - t)^c (1 + c t) = 1 + sum_q (-1)^q q C(c+1, q+1) t^(q+1) (numerator_eq), betti_identity, alternating_betti, and eisenbudGoto_numbers_two (C(c+1, c-1) generators and multiplicity C(c+1, c) at p = 2).
2. These match Eisenbud and Goto 1984, Proposition 1.7 and Corollary 1.11 as printed (journal pp. 100 and 104): multiplicity C(c+p-1, c), generator count C(c+p-1, c-1), Betti numbers C(c+p-1, q+p-1) C(q+p-2, p-1). Check the p = 2 specialization algebraically against the Lean statements.
3. e8_hilbertFn (10, 34, 80, 155, 266, 420, 624, 885) and e8_betti (21, 70, 105, 84, 35, 6) are instances of the general theorems, not separate computations that could disagree.
4. The module docstring's list of missing Mathlib foundations is accurate (search the Mathlib tree under lean/.lake/packages/mathlib if present, read-only).

## Report
For each claim: justified or falsified with evidence. Then defects beyond the claims. Then conjectures the material suggests, each with a falsifier.
