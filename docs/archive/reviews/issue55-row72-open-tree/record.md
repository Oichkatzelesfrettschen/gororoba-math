# Review: row 72 and the open-tree comparisons

Pull request 86 of gororoba-math (issue 55). Reviewers: the `codex` command-line agent (gpt-daybreak-blue, high effort, read-only), the Advisor, and the hosted Codex round.

| Finding (codex, ec71776) | Check | Resolution |
|---|---|---|
| P2: row 72 does not restate `cor_1_17_mod4` at its generality | Confirmed. The Rocq declaration is conditional on the abstract hypothesis `is_h_module_dim`; the Lean theorem proves the conclusion for the actual kernels. | Fixed in ef41c17. The plan's narrowing cell and the module docstring call the theorem a concrete strengthening, and name `Module.four_dvd_finrank_of_quaternion` (rows 69, 70) as the reading of the abstract form. |
| P3: the plan says the samples showed "the same spectrum the proof gives", and the measurement is not retained | Confirmed. The proof gives divisibility by four only. | Fixed in ef41c17: the sampling sentence is removed. |
| Claim 2 (`ci/compare_open_tree.sh`: encoding, mutants first, traps, AGENTS entry) | Justified. | - |

The argument itself was judged sound: the matrix of the kernel, the parity of a skew-symmetric nullity, and the step from complex to real dimension.

## Advisor

The Advisor read ef41c17.
- **Argument:** confirmed. For pure p and q the two real equations are exactly (A + iB)(u + iw) = 0, and a skew matrix of even size has even nullity. The unit-norm hypothesis matters only at k = 0.
- **Codex findings:** the P2 and P3 resolutions are right, and the comparison script is justified.
- **Before the merge:** the commit identities match the repository's, and no claims-ledger row states the row 72 claim (no row names C-1543 or a mod-4 nullity).
