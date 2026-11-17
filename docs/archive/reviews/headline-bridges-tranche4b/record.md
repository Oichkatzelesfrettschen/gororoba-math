# Review record: bridges of the spectrum, closed-form, associator-space and bins theorems

Pull request 68. The owner chose `codex` on gpt-daybreak-blue and no red-team for this round. The Advisor reviewed last.

Advisor column: "confirmed" means the Advisor read the finding, its reconciliation and the resolution as stated; "requested" means the Advisor required the change named in the row, which landed after its verdict and reaches the hosted review.

Codex read the merge head 8fb19ff.

| # | Finding | Severity | Resolution | Advisor |
|---|---|---|---|---|
| 1 | The comparison does not compare `clearedXorParity` directly; the closed-form table sees it only for t >= 3 | P2 | Fixed in 438afc0, after the local review; the hosted review reads it. A parity table P covers every pair at levels 0 to 5 and every t from 0 to k, and the mutant flips parity at t < 3. On a remote host, 4,674 rows of eight tables agree and the mutant differs on every table. | confirmed |
| 2 | The agreement verdict prints before the mutant rejection runs | P3 | Fixed in 438afc0: rejection first, then the verdict. | confirmed |

Codex justified the ten bridge statements, their narrower reasons, and the change to `ci/check_headline_results.py`: with zero owed rows, the calibration builds its own owed control, and the real registry is still checked independently.

The worker edited `ci/check_headline_results.py` outside its brief's new-files-only scope, because the calibration needed an owed row and exited 2 with none. Three pushed commits (8c17ce0, 0636343, 0abae07) fail that check until d2faa49 fixes it; they stay, since the history is pushed. The parent read the diff of 438afc0 against the reviewed head: only the script, its helper, AGENTS.md and a docstring changed, and the `.v` hunk touches comment lines only.
