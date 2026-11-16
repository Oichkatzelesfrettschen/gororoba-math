# Review record: warning ratchet and Mathlib linters

Pull request 49 (`ci/warning-ratchet`). The owner chose the local reviewers for this pull request: `codex` on gpt-daybreak-blue at high effort, with no red-teamers. The Advisor reviews last.

## Brief

`codex` read head 7da247b under a brief built from the workspace review template. The brief listed eight claims:
1. `-w all,+default` reaches every compile path of the gate, and the ratchet reads every log.
2. `ci/rocq_warning_pairs.py` parses every warning block that Rocq 9.3 prints and fails closed.
3. The comparison is two-sided, and `--new-only` relaxes only the stale side.
4. Both calibrations exercise the known-good and the known-bad verdicts.
5. `allowed.tsv` equals the baseline union, and each name in `causes.tsv` matches what Rocq reports.
6. The Lean linter set is fatal under `--wfail`; the header linter's exclusion and the `show`→`change` edits keep their meaning.
7. No file that a retained record cites by sha256 changes, and the kernel replay evidence vectors are unchanged.
8. The text, commit and PR shape follow the guides.

## Reconciliation

| # | Finding (codex, on 7da247b) | Severity | Resolution | Advisor |
|---|---|---|---|---|
| 1 | `extract` compiles `ExtractQuaternion.v` without the warning option, so its warnings never reach the ratchet | P1 | Fixed in 3f94890. The recipe passes `-q -w all,+default`. Measured: one `deprecated-transitive-library-file-since-Stdlib-9.0` pair, the golden file unchanged, and its row added. A later commit lists every compile of the gate in AGENTS.md: three stay outside the comparison, each with its reason, and the on-demand scripts are named. | confirmed; the class was closed by enumeration |
| 2 | An allow-list row of an unknown tree (`quantm`) is compared with no tree's logs and passes | P1 | Fixed in 3f94890. `check_trees` exits 2 on an unknown tree, the script's self-calibration includes that case, and the measured exit is 2. | confirmed |
| 3 | The mutation harnesses and the evidence producer compile under other options and outside the ratchet | P2 | Accepted as a narrowing. AGENTS.md names both. `schur_acceleration_mutations.rs` is cited by digest in gororoba-open, so its `-w +default` keeps its bytes. The unaltered law it compiles is a checkpoint that the gate compiles under the policy. | confirmed |
| 4 | `AuditFixture` builds without `--wfail` | P3 | Accepted as a narrowing. The fixture holds `sorry` and declared axioms by design, so the claim covers the modules built with `--wfail`. | confirmed |
| 5 | Hosted tool versions are unrecorded, and the body claimed a hosted pass before the run ended | P3 | The hosted run on 7da247b passed with "warnings match the allow-list (741 pairs)": open 656, quantum 85, delegation 0, the same as the build machine. The workflow prints no Python or make version; the body says so. | confirmed |

Claims 5 and 7 were justified by the reviewer. Claim 4 was unsettled until the hosted run, which ran both calibrations.

## Owner decision during review

New Rocq sources add rows only for warning names that `causes.tsv` already lists, so the set of tolerated names only shrinks. A new name is the owner's decision (2026-11-16). This rule is a review rule; the gate does not enforce it.

## Advisor

The Advisor confirmed each reconciliation. It required, before the hosted request:
- the enumeration of compile paths;
- a reading of the mutation harnesses;
- removal of the remaining "only shrinks" wording;
- a reading of the hosted run on the head with the extraction recipe under the policy.

It also set the merge order with pull request 50. That pull request adds Rocq sources whose warning pairs this list does not hold, so it lands after this one, with `main` merged into it and its rows taken from a gate run.

## Hosted review

| Reviewer | Head | Finding | Resolution |
|---|---|---|---|
| Codex | 42fd111 | A failed working-tree build skipped the ratchet, so a source that had compiled with an unlisted warning kept its object, and the next build passed (P2) | Fixed in 8ebd4dd: the cleanup runs after every build. Reproduced: after the failing source is fixed, the second run reports the pair and fails. |
| Copilot | 8ebd4dd | When the ratchet itself exits 2, no source is named, so nothing is invalidated | Fixed in 65ea801: exit 2 removes every object of the tree. Measured with a parser stub: the object count goes from 6 to 0, and the run exits 2. |
