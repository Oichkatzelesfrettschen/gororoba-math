# Review record: Flocq import recognizer of the evidence producer

Pull request 51. The owner chose `codex` on gpt-daybreak-blue and an `agy` red-team for pull requests 50 to 53. `agy` ran on Gemini 4 Hydrogen at `high` and on Gemini 3.8 Flash at `high`, both on one red-team brief covering pull requests 50 to 54. The Advisor reviewed last.

Every reviewer read head c047234. The fixes landed afterwards, as new commits.

Advisor column: "confirmed" means the Advisor read the finding, the reconciliation and the resolution as stated in this row and upheld it. "requested" means the Advisor required the change named in the row, which landed after its verdict; the hosted review reads it.

| # | Finding | Reviewer, severity | Resolution | Advisor |
|---|---|---|---|---|
| 1 | `From X Require ... Flocq.Y` reads a namespace-relative module as external Flocq | codex P2, Hydrogen P2 | Boundary: issue 59. The consumer in gororoba-open shares the rule, and the evidence contract requires both copies to agree, so both change together. The claim that only previously refused sources change is narrowed: the `From` branch now reads module words as the consumer does. | confirmed; the narrowed claim requested |
| 2 | The calibration misses Instructions, Profile and repeated prefixes, and bypasses the source reader | codex P2 | Fixed in 0c9b57d. Each table row runs through `split_whitespace` and `uses_flocq`, and a rule without Instructions fails the table. A second fixture covers an import behind an attribute; the hosted run on the head compiles it. | confirmed |
| 3 | Producer and consumer can drift silently | codex P3 | Boundary: issue 59 (a shared conformance corpus pinned in both repositories). | confirmed |
| 4 | Redirect, attributes without a following space, and brackets inside attribute strings are missed | Hydrogen P1 | Boundary: issue 59. Both copies share these cases. A missed import makes the compile fail and the run is refused, so no wrong evidence is written. | confirmed |
| 5 | A bare `Flocq` root, Local/Global prefixes, and `From Flocq Require.` with no module | Flash P2, P3 | Boundary: added to issue 59; both copies share these cases. | confirmed |
