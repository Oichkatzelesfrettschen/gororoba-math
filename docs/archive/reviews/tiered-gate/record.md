# Review record: the two-tier gate (pull request 100)

Brief: `brief.md` beside this file. The local seats read commit 19af5776c. Reviewer: the `codex` command-line agent on
gpt-daybreak-blue at high effort. Red team: `opencode` on opencode-go/glm-5.3. Neither seat ran Lean or Rocq; both ran
shellcheck and actionlint. The Advisor read both reports and the fixes last.

| Finding | Seats | Check | Resolution |
|---|---|---|---|
| The manual dispatch on the final head is a rule that nothing checks: a pull request merged without it puts a Lean declaration the kernel rejects, or an uncompiled Rocq source, on `main` | codex (P1), opencode (P2) | Confirmed: neither full workflow has a pull-request trigger, and `--build` exits before the replay | Fixed: job `head-gate` of `quick.yml` fails a pull request that is not a draft until the required full workflows are green on its head |
| `AGENTS.md` names the verification command for `rocq.yml` only | codex (P3) | Confirmed | Fixed: both commands named |
| The red-gate report searches by phrase and two workflows race to create one issue | codex (P3) | Confirmed by reading | Fixed: one title per workflow, matched by equality; two runs of one workflow share a concurrency group |
| A failed cache save after a green gate opens the red-gate issue | opencode (P3) | Confirmed: `failure()` covers every earlier step | Fixed: the report step precedes the save, and the save continues on error |
| `quick.yml` has a dispatch trigger that no text names | opencode (P3) | Confirmed | Fixed: the header comment names it |
| "Near ten seconds each" against a build job of 342 s | opencode (P2) | Confirmed: measured on the first run, with no saved tree | Fixed in the text: both measured times stated; the restored-tree time is not measured until a run on `main` saves a tree |
| `main-gate` reads the latest completed run, so merges can stack while a run on `main` is in progress | opencode (P3) | Confirmed | Boundary: stated in the pull-request body; `head-gate` narrows it for proof and gate changes |
| Advisor: the opam cache key hashes `rocq.yml`, so every edit of that file rebuilds the switch (observed on the dispatched run of 19af5776c: no cache hit) and the gate alone took 105 of the 150 minutes | Advisor | Confirmed: the run restored nothing | Fixed: key without the workflow hash, a hand-raised token, timeout 210 minutes |
| Advisor: a run that a newer pending run replaces reads cancelled, and `main-gate` would then block every pull request | Advisor | Hypothesis: no replaced run was observed | Fixed: the latest run that is neither cancelled nor skipped decides |
| Advisor: a red `main` blocks its own repair | Advisor | Confirmed by reading | Fixed: `main-gate` passes a pull request whose head is green in both full workflows |
| Advisor: `head-gate` asked a Lean-only change for the Rocq run | Advisor | Confirmed | Fixed: required workflows follow the changed paths |
| Advisor: `main` has no branch protection and no ruleset | Advisor | Confirmed: the API returns "Branch not protected" and an empty ruleset list | Boundary: the red check and the rule of `AGENTS.md` stop a merge; a required check is the owner's setting |

## The kernel checker's conversion (after the review round)

A second red-team run (`opencode` on opencode-go/glm-5.3) read the Rocq gate for the cause of its length. Checked
against measurements:

| Claim | Check | Result |
|---|---|---|
| The runs of 105 minutes were opam cache misses | Step times of two runs on the same sources: both restored the switch (install 0 to 1 s); the gate step took 3,967 s and 6,280 s | Refuted: the hosted runner varies |
| One module, `StiefelA5Certificate`, holds most of the 3,008 s kernel check, because the checker reduces its `vm_compute` steps with its own lazy machine | Measured (Rocq 9.3.0, one core of a 32-thread workstation): `rocq check -silent -o -norec` 1,902 s at 0.73 GB, recursive 1,946 s at 1.11 GB | Confirmed |
| The checker has no bytecode conversion | `rocq check --help` lists `-bytecode-compiler (yes|no)`, default no; with `yes` the same module re-checks in 73 s (`-norec`) and 95 s (recursive), exit 0, context summary clean | Refuted, and the lever |

Owner ruling (2026-11-23): runs of a push and of a dispatch use the bytecode machine in the checker; the nightly run
keeps the checker's own reduction. `ci/check_rocq.sh` reads `ROCQ_CHECK_VM`, and its declared-axiom calibration runs
under the same option. The other proposals of that report (a split check with `-norec`, a verdict cache by closure
digest, reuse of objects by content digest, a smaller certificate) are not part of this pull request.

## Hosted round

The hosted Codex review read c91079e4f and posted two findings.

| Finding | Check | Resolution |
|---|---|---|
| P2: a change of a `.gitattributes` file alone needs no Rocq run under `head-gate`, though it alters the export the Rocq gate builds from | Confirmed: the path filter named `rocq/`, `ci/` and workflows only | Fixed: a `.gitattributes` file at any depth requires `rocq.yml` |
| P2: a pull request from a fork cannot satisfy `head-gate`, since a dispatch targets a branch of this repository | Confirmed | Boundary: a maintainer pushes the head to a branch here and dispatches on it, which keeps unread fork code away from this repository's caches; `AGENTS.md` and the workflow comment state it |

Survived both seats: without an option `ci/check.sh` runs the steps of `main` in the same order (a comment-stripped
diff shows three guarded additions); `--quick` and `--build` exit nonzero on every failed check and 2 on an unknown
argument; `ci/check_signal_traps.sh` still interrupts the script before either early exit; only a green run on
`main` saves the build tree and pull requests only restore; an empty or null run list fails `main-gate`;
`make --keep-going` still exits nonzero on a failing source; the triggers and concurrency groups match their comments.

Calibration: the red path of `head-gate` and its green path after the dispatched runs are recorded in the pull
request. The red path of `main-gate` needs a red run on `main` and was not exercised.
