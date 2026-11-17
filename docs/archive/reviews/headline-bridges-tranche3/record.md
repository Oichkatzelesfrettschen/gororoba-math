# Review record: bridges of mul_star_self and the nullity estimator theorems

Pull request 63. The owner chose `codex` on gpt-daybreak-blue and no red-team for this round. The Advisor reviewed last.

Advisor column: "confirmed" means the Advisor read the finding, its reconciliation and the resolution as stated; "requested" means the Advisor required the change named in the row, which landed after its verdict and reaches the hosted review.

Codex read af69260.

| # | Finding | Severity | Resolution | Advisor |
|---|---|---|---|---|
| 1 | `ci/compare_estimator_rocq.sh` runs `lake build` in the checkout, writing `lean/.lake/build` outside the scratch directory its header promises | P2 | Fixed in d327c3a: `lake build --no-build` (Lake 5.0.0: exit when a target is not up to date) and a request for a prior build; the same fix in `ci/compare_dot.sh`, which had the defect. | confirmed; the run requested |
| 2 | `PYTHON` is resolved but not exported | P3 | Fixed in d327c3a, in both scripts. | confirmed |

The run the Advisor required was made on a remote host at d327c3a. With the Lean modules unbuilt, both scripts exit 2 with "build the Lean library first". After `lake build` of the two modules:
- `compare_dot`: "72 values agree; the mutated reference is rejected", exit 0;
- `compare_estimator_rocq`: "12 blocks, vHat, nHat, nullity, vBarPos, vBarNeg agree exactly; the unsigned-mean mutant differs on 8 block(s)", exit 0.

The checkout stayed clean.

Codex justified the other claims: `mul_star_self` and its extras are faithful; the estimator definitions match under `Finset.toList`, with both theorems faithful; the `CharZeroField` signature adds no strength; the warning rows and the axiom ledger agree.
