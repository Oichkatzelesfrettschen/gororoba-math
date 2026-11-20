# Review: claims-ledger rows for the a5 scratch-run statements

Pull request 88 of gororoba-math. Reviewers: the `codex` command-line agent (gpt-daybreak-blue, high effort, read-only) and the Advisor. There is no hosted round, by the owner's ruling of 2026-11-18 for new gororoba-math pull requests.

| Finding (codex, 630a5c3) | Check | Resolution |
|---|---|---|
| P2: line 33 of `ANALYSIS.md` (E8-bar -> VB: dimension 4, multiplicity 2, at both primes) has no row; A5-325 covers only one prime and is not a proof-owed row | Confirmed. | Added an owed row and its expected-source entry. The entry was computed by `expected_sources.py --write`, and the check then reads 1282 listed sources matching. |
| Claims 1 and 3: the rows follow the README; the expected-source pins are right | Justified. Placement `rocq` follows the evidence axis for evaluated certificates at a fixed prime. | - |

## Advisor

The Advisor asked whether the E8-bar -> N- multiplicity-3 row duplicates A5-002. It does not. A5-002 states sheet multiplicities of the fixed varieties along N- and N+, while the new row states the dimension and multiplicity of the local ring of the slice germ. Both rows stay, and the new row's note names A5-002.
