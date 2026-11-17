# Review record: challenge-configuration gate and the P7 replay cost

Pull request 61. The owner chose `codex` on gpt-daybreak-blue and no red-team for this round. The Advisor reviewed last.

Advisor column: "confirmed" means the Advisor read the finding, its reconciliation and the resolution as stated; "requested" means the Advisor required the change named in the row, which landed after its verdict and reaches the hosted review.

Codex read 2e99586.

| # | Finding | Severity | Resolution | Advisor |
|---|---|---|---|---|
| 1 | A configuration may name another tracked challenge module and pass | P1 | Fixed in b7448aa: `challenge_module` must equal `Challenge.<file stem>`, and that tracked module must declare every listed theorem. | confirmed |
| 2 | `theorem_names` and the top-level JSON lack schema validation: a string passes; a number or an array raises a traceback | P1 | Fixed in b7448aa: an object whose module fields are strings and whose list fields are nonempty string lists; a decode failure is a check failure. | confirmed |
| 3 | The four new mutants do not cover each failure class | P2 | Fixed in b7448aa: twelve challenge mutants, each failing for its intended reason, verified on a remote host. | confirmed |
| 4 | The P7 figures have no accessible evidence | unsettled | Fixed in b7448aa: `docs/archive/measurements/h1-vm-compute-decide-kernel.md`. | confirmed |

The pull request also carries the cause of the root replay cost that another session measured: `leanchecker` prefix-matches module names (d87cd08). A later commit dates the figure to the eight-module library it was measured on (e872449, requested).
