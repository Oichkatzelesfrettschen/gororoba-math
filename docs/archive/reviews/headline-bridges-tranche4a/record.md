# Review record: bridges of the TwoTermNullity and TwoTermRecursion theorems

Pull request 67. The owner chose `codex` on gpt-daybreak-blue and no red-team for this round. The Advisor reviewed last.

Advisor column: "confirmed" means the Advisor read the finding, its reconciliation and the resolution as stated; "requested" means the Advisor required the change named in the row, which landed after its verdict and reaches the hosted review.

Codex read 5b38d60.

| # | Finding | Severity | Resolution | Advisor |
|---|---|---|---|---|
| 1 | The kernel bridge claims both operands `e_i ± e_j` but states only left multiplication by `e_i + e_j` | P2 | Fixed in 4999b80, after the local review; the hosted review reads it. `signed_kernel_basis` proves both operands through `kernel_iff_relation`. The registry partners `kernel_basis` and `kernel_rank` keep their statements, unchanged across the commit as read by the parent. New `kernel_basis_sub` and `kernel_rank_sub` bridge the Lean subtraction theorems, which are not headline rows. | confirmed (choice to add the theorems) |
| 2 | The narrower reason reverses strength: the explicit basis is a stronger witness of freeness than `Module.Free` | P3 | Fixed in 4999b80. Only the rank rows are narrower: they count one basis, with no invariant basis number. | confirmed |
| 3 | `lake build --no-build` writes a `.nobuild` trace on a stale target, so "writes only under the temporary directory" is false on that path | P2 | Fixed in d00af93 for `compare_aligned_pair_count.sh` and `compare_alignment.sh`; the trace was measured on a remote host. Fixed in e2e85dc for `compare_dot.sh` and `compare_estimator_rocq.sh`, once `main` held pull request 63; each header now states the trace, and each message no longer claims nothing is written. | confirmed; e2e85dc requested |

Codex justified the recursion bridges and the comparison's inputs and mutant. The README no longer counts the project-listed modules, a count that each bridge changed.
