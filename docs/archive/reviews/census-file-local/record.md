# Review record: census of theorems over file-local definitions

Pull request 72, issue 44. The owner chose `codex` on gpt-daybreak-blue and no red-team. The Advisor reviewed last.

Advisor column: "confirmed" means the Advisor read the finding, its reconciliation and the resolution as stated; "requested" means the Advisor required the change named in the row, which landed after its verdict and reaches the hosted review.

Codex read c0bebca. Its brief asked for a verdict on the pull request's stated claims, with findings by severity, and forbade builds and writes.

| # | Round | Finding | Severity | Resolution | Advisor |
|---|---|---|---|---|---|
| 1 | 1 | The README table of successors is a second copy of the `addressed_by` mapping, against the owner's comment on issue 44 | P2 | Confirmed against the comment. Fixed in c41b7a6: the section gives the lookup command over `header-verdicts.tsv` and no table. | confirmed |
| 2 | 1 | `file-local-candidates.tsv` is not what `--file-local --tsv` prints; no invocation reproduces it | P2 | Confirmed. Fixed in 5e1e108 and 6fa0bcf: `--file-local --candidates FILE` writes the queue (header, short local names, empty verdict, rows without a verdict in `header-verdicts.tsv`). Measured with Rocq 9.3.0 on a remote host at 6fa0bcf: 115 closed, 176 file-local, 810 declarations, and the written file equals the committed one byte for byte. | confirmed |
| 3 | Advisor | The README says a queued row leaves the queue when its verdict lands; no run showed it | - | Measured at 6fa0bcf: with `--verdicts` naming a copy of the table that holds one file-local theorem, the option wrote 175 rows and left that theorem out. | requested |

Codex rated the README table and the file-local rule justified and the claim that the candidates file is the mode's output falsified (row 2).
