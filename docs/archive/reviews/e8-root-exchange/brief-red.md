# Brief: gororoba-math PR 131 (branch rocq/root-exchange, head 6ab5427d7)

Read first: the workspace AGENTS.md at AGENTS.md, then AGENTS.md ("Statements and proofs", "Rocq sources"). Work read-only: change no file anywhere, commit nothing, run no build, no Python, no Lean or Rocq process (the shared hosts ran out of memory twice today), spawn no subagent; print your whole report as your final answer. You may read files and run git (git show, git diff, git grep) in  the diff under review is origin/main...6ab5427d7.

Classify every finding as proved (by reading the source), computed (with the command), or hypothesis, with file and line.

## Claims under review
1. E8RootExchange.v states three nontrivial diagonal congruences of C_N- (flips {s1,s3,s6,s9}, {i,s2,s3,s4,s6,s7,s8}, their product) with explicit sign vectors D, entry (a,b) of C at the flipped point = d_a d_b times entry (a,b), with i free; the same for C_N+ with s4 and s5 exchanged; the list-equality check proves exactly this statement.
2. jm_flip_* state that each listed generator of J_N- changes by a fixed sign under the four flips, over every commutative ring; the sign lists are correct.
3. root_exchange_C, root_exchange_detB and root_exchange_ideal (functor RootExchange over rings with i^2 = -1, instance GaussianRootExchange) state that the flip changing i to -i carries C, detB and the ideal of J at root r to those at root -r, and say nothing about F or G.
4. The file adds no axiom, its _RocqProject line and allowed.tsv rows follow AGENTS.md, and its docstring states the conventions.

## Report
For each claim: justified or falsified with evidence. Then defects beyond the claims. Then conjectures the material suggests, each with a falsifier.

## Role: red team
You are a red-teamer, not an auditor: try to break each claim (a statement weaker than its name, a generator that renders the wrong lists, a sign off by one, an identity true only for small c or d, a bridge that states something else). Report each attempted break and its outcome.
