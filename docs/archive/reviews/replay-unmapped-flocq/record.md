# Review record: replay evidence refuses Flocq it does not map

Pull request 70, issue 64. The owner chose `codex` on gpt-daybreak-blue and no red-team. The Advisor reviewed last.

Advisor column: "confirmed" means the Advisor read the finding, its reconciliation and the resolution as stated; "boundary" means the Advisor agreed the finding names a documented limit, not a defect of this change; "requested" means the Advisor required the change named in the row, which landed after its verdict and reaches the hosted review.

Codex round 1 read c4ebdf6; round 2 read 5609e03.

| # | Round | Finding | Severity | Resolution | Advisor |
|---|---|---|---|---|---|
| 1 | Advisor | A load under `Succeed` or `Fail` is rolled back, so the library query alone cannot see it | - | Measured: with a blind import rule, both forms wrote evidence without Flocq objects at c4ebdf6. Fixed in 3abe73c: every compile runs on a hidden load path without the installed Flocq; `blind-succeed` is refused, and the `Fail` case is accepted with nothing loaded while the open path refuses it (2400f61). | requested |
| 2 | 1 | The consumer must co-land a versioned field for the library query | P1 | Boundary: gororoba-open runs no Rocq and trusts the producer by design; a field the producer writes gives the consumer no independent check. Accepted evidence is byte-identical to the `origin/main` producer's (FP24Representable and C001, at 18847e6). Round 2 rated the contract claim justified. | boundary |
| 3 | 1 | `loaded_libraries` stops at the first blank line, so an entry after it is unread | P2 | Fixed in 5609e03: the report must be the query's whole output; nine malformed reports calibrate it. | confirmed |
| 4 | 2 | Rocq fills an absent `ROCQPATH` from `coq_environment.txt` beside its executable, which could restore a Flocq root | P1 | Fixed in 34d02aa: `COQPATH` and `ROCQPATH` are set empty in every Rocq process; a recording wrapper calibrates that the variables are empty, and the fallback's behavior is a reading of `Boot.Util.getenv_opt`. | confirmed |
| 5 | 2 | Malformed single-token library names (`???`, `M..N`, `1M`) pass | P2 | Fixed in 34d02aa: each entry must be a dot-separated ASCII qualified name; four cases calibrate it. | confirmed |
| 6 | Advisor | The environment checks have no known-bad input; the calibration header omits the new cases; the body is stale | - | Fixed in 18847e6 and the body: each check rejects a synthetic known-bad line first; the header lists the library-report, environment and Fail cases. | requested |

Codex justified in round 2 that the library query stays outside schema-version-1 evidence, so `theorem_replay.rs` needs no field or corpus change, and that the `blind-open` case is a real known-bad that the `origin/main` producer fails.
