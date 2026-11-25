# Brief: pull request 100 of gororoba-math, a two-tier gate (quick checks per push, full gates nightly, on main and on dispatch)

Read first: the workspace AGENTS.md, then the sections "Reviews and merges detail" and "Landing detail" of workspace/reference.md of gororoba-infrastructure, then WORKTREE/AGENTS.md ("Landing", "Layout"). Work read-only: change no file; never commit, push, stash, dispatch a workflow or start a cloud resource; spawn no subagents. You may run git, grep, file reads, shellcheck and actionlint. Run no Lean, Lake, Rocq, opam, Python batch or test suite on this host. Keep within 25 minutes.

Material: the session worktree (WORKTREE below) on branch ci-tiered-gate; read the change with `git -C WORKTREE diff origin/main...HEAD` and the files in place. Measured on the first run of the pull request (hosted runner): quick checks 11 s, build job 342 s without a saved build tree, main-gate 5 s.

## Claims under review (each is a claim, not a fact; justify or falsify it)

1. `sh ci/check.sh` without an option runs exactly the steps it ran on origin/main, in the same order, with the same exit statuses. Status: hypothesis. Falsifier: a step skipped, reordered or newly reachable.
2. `--quick` needs no Lean toolchain and exits 0 only after shellcheck, the recursive-removal rule, ci/check_signal_traps.sh, ruff, the headline registry, the claims ledger and actionlint all passed; `--build` runs every step of the full gate except the leanchecker replay of each module and the replay-fixture calibration. Status: hypothesis. Falsifier: a path where a failed check still exits 0, an unknown argument that is accepted, ci/check_signal_traps.sh broken by the new early exits (it interrupts check.sh under stub tools).
3. In .github/workflows/quick.yml the job build restores lean/.lake/build with actions/cache/restore by a prefix key and the lean workflow saves it only on refs/heads/main after a green gate; a restored tree cannot make the build accept a module whose source changed (Lake decides by content hash). Status: hypothesis. Falsifiers: a cache written by a pull-request ref that main-based runs later restore; a stale object accepted; the key never matching; `lake build --wfail` passing over a restored tree on a module whose earlier build printed a warning.
4. The job main-gate fails a pull request exactly when the latest completed lean or rocq run on main is not a success; its permissions suffice (actions: read) and an empty result is not read as success. Status: hypothesis. Falsifier: a cancelled or skipped run misread, a run of another event or branch selected.
5. The "Report a red gate on main" steps of lean.yml and rocq.yml open or comment on one issue only on a failure on main, with issues: write as the only added permission, and no untrusted input reaches a shell unquoted. Status: hypothesis.
6. The schedule, push and workflow_dispatch triggers with the concurrency groups do what the comments say; a dispatch on a branch and a push run on main do not cancel each other. Status: hypothesis.
7. `make --keep-going` in the three makes of ci/check_rocq.sh changes no verdict: a failing source still fails the script. Status: hypothesis.
8. The text of AGENTS.md "Landing" matches the workflows, and no other tracked file (README.md, ci/claims/README.md, docs) still says that the lean and rocq workflows run on every pull request. Status: hypothesis; search for it.

## Questions to answer

- Defects in code, workflows and text, with file:line.
- Which check of the old per-pull-request gate has no home in either tier for a pull request merged without the manual dispatch, and what is the worst a merge can now put on main?

Report ranked by consequence, every finding tied to a file:line, a command with its output, or a documented behavior with its source, each marked proved, computed, measured, documented or hypothesis, with a severity P1 to P3. Print the report as your answer, under 150 lines.
