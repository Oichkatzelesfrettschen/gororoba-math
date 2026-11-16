# Review record: install_rocq and missing system packages

Pull request 53. The owner chose `codex` on gpt-daybreak-blue and an `agy` red-team for pull requests 50 to 53. `agy` ran on Gemini 4 Hydrogen at `high` and on Gemini 3.8 Flash at `high`, both on one red-team brief covering pull requests 50 to 54. The Advisor reviewed last.

Every reviewer read head cace5ad. The fixes landed afterwards, as new commits.

Advisor column: "confirmed" means the Advisor read the finding, the reconciliation and the resolution as stated in this row and upheld it. "requested" means the Advisor required the change named in the row, which landed after its verdict; the hosted review reads it.

| # | Finding | Reviewer, severity | Resolution | Advisor |
|---|---|---|---|---|
| 1 | The clang check breaks the complete-switch no-op | codex P2, Hydrogen P2, Flash P2 | Fixed in b54cce6: the check runs only when a root is missing. Measured: a complete switch without clang exits 0, and a missing root without clang exits 2. | confirmed |
| 2 | Other conf-* depexts still stall at the prompt | codex P2, Hydrogen P1, Flash P2 | Fixed in b54cce6 with `OPAMASSUMEDEPEXTS`, documented in opam 2.5.0 for install and switch import. The next commit adds an empty standard input on both commands; that mechanism was measured for the extraction provisioner. | b54cce6 confirmed; the empty stdin requested |
| 3 | The clang requirement is not tied to the export | codex P3 | Fixed in b54cce6: clang is required only when the export selects conf-clang. | confirmed |
| 4 | The 24-minute figure is not retained | codex P3 | Fixed: the header states the mechanism and drops the duration. | confirmed |
