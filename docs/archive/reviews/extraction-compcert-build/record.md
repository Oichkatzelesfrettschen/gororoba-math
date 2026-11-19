# Review: ccomp build of the R2VB C targets

Pull request 80 of gororoba-math (issue 75). Reviewers by the owner's ruling of 2026-11-18 for new pull requests: the `codex` command-line agent (gpt-daybreak-blue, high effort, read-only) and the Advisor, last; no hosted review round.

## Brief

The codex reviewer read head c953c12; the Advisor read efaf535 and checked four claims. First, the recipe fails on a broken compile, a differing output or a differing golden record. Second, the interpreter verdict and the README's reading of it are correct. Third, the unity files read the units unchanged apart from the stated rename. Fourth, the body, README and golden record agree with the logs.

## Findings and reconciliation

| Finding (codex, c953c12) | Check against the source | Resolution |
|---|---|---|
| P2: the README says CompCert's theorem does not apply. It still holds: a source that goes wrong makes the behavior improvement unconstraining. | Confirmed by the Advisor's check of `behavior_improves` (`common/Behaviors.v`, CompCert v3.17): `Goes_wrong t` is improved by any behavior that extends the trace `t`. | Fixed in 2b20597 and the record commit: the README states that the theorem holds and fixes only the output before the stuck point, the line of fixture 0. The operation is `sem_and` of `cfrontend/Cop.v`, which yields no value for a pointer. |
| P2: MATCH is not bound to freshly emitted, pinned source bytes. | Confirmed. The target depended only on `test-r2vb-correspondence`, which neither emits nor hashes. | Fixed in 2b20597 and efaf535: the target runs `extract-r2vb-check` and `extract-c-check` first and records the verified manifests' digests. |
| P3: the claim that the unity files are equivalent is unproved. | Confirmed: no preprocessed comparison was retained. | Fixed in 2b20597 and efaf535: the record counts the preprocessed lines the rename changes. They are 0 in each emitted unit and 4 in the glue, all the struct tag (its declaration, its definition and two casts). The record keeps the unity-file digests. |
| P3: several measured numbers lack retained run evidence. | Confirmed for the occurrence counts and the run transcript. | Fixed: the record now prints the occurrence counts (24, 26, 25). The transcript of the run at efaf535 and its record are kept with the session's evidence, and the PR body quotes them. |

Review slip and known-bad evidence: 2b20597 wrote single dollar signs in the new record lines, because a string replacement expanded `$` to `# Review: ccomp build of the R2VB C targets

Pull request 80 of gororoba-math (issue 75). Reviewers by the owner's ruling of 2026-11-18 for new pull requests: the `codex` command-line agent (gpt-daybreak-blue, high effort, read-only) and the Advisor, last; no hosted review round.

## Brief

The codex reviewer read head c953c12; the Advisor read efaf535 and checked four claims. First, the recipe fails on a broken compile, a differing output or a differing golden record. Second, the interpreter verdict and the README's reading of it are correct. Third, the unity files read the units unchanged apart from the stated rename. Fourth, the body, README and golden record agree with the logs.

## Findings and reconciliation

| Finding (codex, c953c12) | Check against the source | Resolution |
|---|---|---|
| P2: the README says CompCert's theorem does not apply. It still holds: a source that goes wrong makes the behavior improvement unconstraining. | Confirmed by the Advisor's check of `behavior_improves` (`common/Behaviors.v`, CompCert v3.17): `Goes_wrong t` is improved by any behavior that extends the trace `t`. | Fixed in 2b20597 and the record commit: the README states that the theorem holds and fixes only the output before the stuck point, the line of fixture 0. The operation is `sem_and` of `cfrontend/Cop.v`, which yields no value for a pointer. |
| P2: MATCH is not bound to freshly emitted, pinned source bytes. | Confirmed. The target depended only on `test-r2vb-correspondence`, which neither emits nor hashes. | Fixed in 2b20597 and efaf535: the target runs `extract-r2vb-check` and `extract-c-check` first and records the verified manifests' digests. |
| P3: the claim that the unity files are equivalent is unproved. | Confirmed: no preprocessed comparison was retained. | Fixed in 2b20597 and efaf535: the record counts the preprocessed lines the rename changes. They are 0 in each emitted unit and 4 in the glue, all the struct tag (its declaration, its definition and two casts). The record keeps the unity-file digests. |
| P3: several measured numbers lack retained run evidence. | Confirmed for the occurrence counts and the run transcript. | Fixed: the record now prints the occurrence counts (24, 26, 25). The transcript of the run at efaf535 and its record are kept with the session's evidence, and the PR body quotes them. |

. The run at 2b20597 failed with make exit 2, no record and no MATCH line, so the recipe ends nonzero on a failing `ccomp` call. efaf535 escapes them, and the run there exits 0. Neither `rocq/open/Makefile` nor `rocq/open/.gitignore` is cited by digest in gororoba-open or gororoba-quantum (`git grep` of their `origin/main` sha256).

## Advisor

The Advisor read efaf535 and confirmed all four codex findings. For the theorem boundary it required the reading of `behavior_improves` above and a check of the `Cop.v` name, both done in the record commit. It accepted the unity-file fix, noting that `-D` renames across the whole glue and so gives an upper bound, and the evidence fix, noting that the counts are text matches of `& 1`. Applied in the record commit: the Makefile comment names the two emission checks, and the README gives the working invocation with `OPAMSWITCH`. The last commits change the Makefile, so the hosted `rocq` check on the final head is the gate.
