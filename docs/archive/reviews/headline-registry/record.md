# Review record: headline registry check and Rocq bridges

Pull request 50. The owner chose `codex` on gpt-daybreak-blue and an `agy` red-team for pull requests 50 to 53. `agy` ran on Gemini 4 Hydrogen at `high` and on Gemini 3.8 Flash at `high`, both on one red-team brief covering pull requests 50 to 54. The Advisor reviewed last.

Every reviewer read head 6abb56e. The fixes landed afterwards, as new commits.

The new scan finds 24 fewer theorem names than the old line regex. Each of the 24 was "Lemma 9.4"-style text inside a comment, so the old scan matched them falsely; the parent traced them. Every reviewer found the bridge statements sound. Codex checked the Lean and Rocq sign recurrences on 87,381 pairs through level 8, and agreed that the AnnihilatorSymmetry partners are incomparable with the Lean statements, not narrower.

Advisor column: "confirmed" means the Advisor read the finding, the reconciliation and the resolution as stated in this row and upheld it. "requested" means the Advisor required the change named in the row, which landed after its verdict; the hosted review reads it.

| # | Finding | Reviewer, severity | Resolution | Advisor |
|---|---|---|---|---|
| 1 | A commented-out Rocq theorem satisfies a partner row | codex P1, Hydrogen P1, Flash P1 | Fixed in b57c3c2. Rocq comments and strings are lexed, a theorem counts only if its proof ends in Qed or Defined (or it has a `:=` body), and Module Type is excluded. Mutants: a commented copy, Abort, Admitted, Module Type. | confirmed |
| 2 | Lean comments are counted by delimiter, and private names pass | Hydrogen P1, codex P2 | Fixed in b57c3c2. A lexer handles line comments, nested blocks, docstrings, strings and character literals; `mutual` blocks are tracked, and private declarations are excluded. Three mutants. | confirmed |
| 3 | README misspellings pass (qualified, dotless, lowercase) | codex P1, Hydrogen P1, Flash P2 | Fixed in b57c3c2. The exemption for `GororobaMath.` is gone, and every identifier token resolves or is listed with a reason in `NON_DECLARATION_TOKENS` (20 measured entries); a stale entry fails. AGENTS.md now states the rule. | confirmed; the AGENTS.md sentence requested |
| 4 | Duplicate registry and README rows pass; the calibration misses classes | codex P2, Hydrogen P2 | Fixed in b57c3c2: 21 mutants and 3 known-good controls. The commit body says 23 known-bad copies; that count is wrong and this record corrects it. | confirmed |
| 5 | A section named like its module closes the module | Flash P2 | Verified on b57c3c2: `Module Foo. Section Foo. End Foo.` yields `Foo.inside_foo`. | confirmed |
| 6 | The NonAssociative docstring claims every theorem of the Lean module, but the helper `mul_assoc_ne_mk_zero` has no bridge | codex P3 | Fixed in 3498eb2: the docstring now covers the five headline theorems. | confirmed |
