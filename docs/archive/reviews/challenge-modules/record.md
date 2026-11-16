# Review record: challenge modules for the remaining headline theorems

Pull request 54 (`lean/challenge-modules`). The owner chose `codex` on gpt-daybreak-blue and an `agy` red-team for pull requests 50 to 53. This pull request, opened afterwards, ran under the same selection. The Advisor reviews last.

## Brief

`codex` read head 4e390f8. Its brief listed three claims:
1. Each challenge restates its library theorem faithfully, and together the challenges cover every Lean row of `ci/headline-results.tsv` on `main`.
2. The reason for leaving five modules out of `lean/Challenge.lean` is correct, and no gate depends on that file.
3. The two AGENTS.md statements are accurate and well placed.

The red-team brief covered pull requests 50 to 54. It asked for a challenge whose statement differs from its theorem in a way the comparator would miss, or for a headline row without a challenge.

## Measurement retained for the comparator rule

On Linux, with Lean 4.35.0 and Mathlib v4.35.0, in a worktree whose `lean/.lake/packages` was a symbolic link to the primary checkout's packages, `lake comparator --config Challenge/Basic.json` printed:

```
info: mathlib: materializing new dependency
error: already exists (error code: 17, file already exists)
  file: <worktree>/lean/.lake/packages
error: Child exited with 1
```

With a hard-linked copy of the packages directory, all seven configurations printed "Your solution is okay!".

## Reconciliation

| # | Finding | Severity | Resolution | Advisor |
|---|---|---|---|---|
| 1 | No gate checks challenge coverage, configurations or drift; a later headline row can land without its challenge (codex) | P2 | Boundary. The registry check of pull request 50 is the natural home. A follow-up extends `ci/check_headline_results.py` to require, for each Lean row, a configuration that names the row's theorem, its solution module and exactly the three permitted axioms. Filed as issue 60, because that script does not exist on this branch's base. | confirmed |
| 2 | The environment-clash sentence is broader than the mechanism: `Challenge.Tower` imports `Basic` and declares `Tower` without a clash (codex) | P2 | Fixed: AGENTS.md now says the clash arises with a module that imports the solution module declaring the restated definition. | confirmed |
| 3 | The comparator error has no retained primary evidence (codex) | P3 | Fixed: this record holds the command and its output, and AGENTS.md names the toolchain and points here. | confirmed |
| 5 | Red team (agy, Gemini 3.8 Flash): `lake comparator` would miss a restated definition that differs | P2 | Refuted: in Basic, Tower, TwoTerm and Estimator, one restated definition was changed and each change was rejected with "Const does not match". | confirmed |
| 4 | Red team (agy, Gemini 4 Hydrogen): no finding. It checked all rows against the configurations, and every restated definition and statement against its solution module | none | none | confirmed |

Codex justified claims 1 and 2 by a static audit: 28 rows, 13 configurations, every statement prefix identical, every import list matching, and the three axioms in each configuration.
