# Review record: lean gate timeout and the cancelled-gate report (pull request 144)

Branch ci/lean-gate-timeout, head b501703fe.

## Reviewers (owner's selection, 2026-11-27: none local)
- The Advisor last, then the hosted Codex round.

## Measurement (main, hosted runner)
| Run | Head | Build | Kernel replay | Outcome |
|---|---|---|---|---|
| 45913112570 | e8ea70846 (92 modules) | 23:50:46 to 23:57:51 (7.1 min) | 23:59:34 to 00:16:35 (17.0 min) | success, 27 min 53 s |
| 45916107942 | b4ecc37c3 (93 modules) | 00:22:08 to 00:30:29 (8.3 min) | from 00:32:34, unfinished at the 30 min cancel | cancelled |
| 45942964041 | d56182c18 (93 modules) | 04:59:46 to 05:08:51 (9.1 min) | from 05:10:43, unfinished at the 30 min cancel | cancelled |

The green runs sat at 24 to 28 min; the build time and the replay of one more module took the job past 30 min. A full run of the gate on this head (workflow dispatch, run 45950837980) measures the 93-module replay before the merge.

## Advisor findings and resolutions
| Finding | Resolution |
|---|---|
| Measure the cause before fixing the number | The table above; the dispatched run on this head |
| Closes: in the commit closes issue 143 while its durable fix stays open | Issue 143 is reopened after the merge; the durable fix is pool row A5F-215 (leanchecker replay driver) |
| The cancelled() report path is unexercised | Stated: no cancelled run of main has passed through the new condition yet; the post-checkout step of run 45942964041 ran after the timeout, which supports the step running |
| PR 126 merged at 04:58 while main's lean gate had been cancelled since 00:50 | Recorded in issue 143: the watcher read only the rocq run |
