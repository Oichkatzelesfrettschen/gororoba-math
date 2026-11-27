# Review record: kernel replay through replayFromImports (pull request 145)

Branch ci/kernel-replay-driver. Heads: a45ba6c46 under local review, 29e44cccd after the fixes.

## Reviewers (owner's selection, 2026-11-27)
- codex gpt-daybreak-blue (high), read-only; agy gemini-4-neon-medium, red team; the Advisor last.
- Owner approval of the AGENTS.md sentences ("Statements and proofs", "Proof hygiene", the gate table) in this pull request.

## Findings and resolutions
| Finding | Reviewer | Class | Resolution |
|---|---|---|---|
| The PASS count checks the line count only, not the module names (a duplicate and a dropped module would pass) | agy | read from source | Fixed in 29e44cccd: sorted PASS names compared with the sorted module list (cmp); calibrated on a list with one module dropped and one duplicated |
| No check that the copied replayFromImports still matches the toolchain source after a toolchain bump | agy | read from source | Fixed in 29e44cccd: the gate compares the copied body with the toolchain's src/lean/LeanChecker.lean and fails closed when the source is absent; calibrated on a one-character mutation; c06bcad74 adds a check: success line for each new check, all three printed on the hosted runner (run 46030825313) |
| The fixture is never replayed inside a multi-module batch | agy | read from source | Fixed in 29e44cccd: "<good module> ReplayFixture" must exit nonzero, print PASS for the good module and name ReplayFixture.bogus |
| README.md and lean/ReplayFixture.lean still name leanchecker in the gate; "every module" overstates coverage; upstream path and the relative usage path | codex, agy | read from source | Fixed in 29e44cccd |
| replayFromImports matches Lean 4.35.0 byte for byte (SHA-256 5d5cfd28... of the extracted body) | codex, agy | read from source | Note |
| Exit codes, PASS after the awaited replay, xargs failure propagation, findOLean resolution | codex, agy | read from source | Note: excluded at the cited lines |
| The fix worker's AGENTS.md edit after the approved edit | Advisor | read from source | Confined to the approved sentence ("every tracked library module under lean/GororobaMath/") |

## Measurements
- Workstation: 93 modules replayed in 916 s by leanchecker, 412 s by the driver in one process, 180 s with four processes; ci/check.sh exit 0 in 340 s on 29e44cccd.
- Hosted (workflow dispatch, run 45980090266, head 29e44cccd, 93 modules): the job took 12 min 32 s against 24 to 28 min with leanchecker.
- Hosted (workflow dispatch, run 46030825313, head c06bcad74 with main merged, 95 modules): build ended 16:16:18, import checks ended 16:17:41, the replay and its three checks ended 16:21:40 (3 min 48 s for the replay), the job took 14 min 43 s; the three new check: lines printed.

## Hosted review
- Codex (requested 16:52Z on fb2b51191): no major issues; receipt comment on the pull request, no review threads.
