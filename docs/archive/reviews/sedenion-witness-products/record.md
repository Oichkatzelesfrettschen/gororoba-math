# Review record: sedenion witness products (pull request 105)

## Reviewers

The owner chose no local reviewer for this pull request (2026-11-24). The hosted Codex round on commit 3218f6655
reported no finding. The Advisor reviewed last; its findings are below.

## What each check establishes

| Statement | Evidence class | Check |
|---|---|---|
| the three products, the two nonzero factors, the three trace-form values and the quotients 0, 1, 1/2 | kernel-checked | `lake build GororobaMath.CayleyDickson.WitnessProducts` without warnings, `lake env leanchecker` on the module, `#print axioms` of the eight theorems (propext, Classical.choice, Quot.sound), on an aarch64 host; the `lean` workflow, which runs `sh ci/check.sh`, and the `rocq` workflow are green on the head |
| the products equal those `cd_core.cd_multiply_exact` of gororoba-quantum returns (dark all zero; bright 2 at index 5 and -2 at index 14; fixture 1, 1, 1, -1 at indices 3, 7, 8, 12) | computed | one run on the same host |
| `Tower.sign 4 p q` equals `cd_core.cd_sign(16, p, q)` on all 256 pairs | measured, not retained | a scratch `#eval` table against the Python table, sha256 97ff75b9edd4049ed4f05a4b8e148c1f2b73058fe102dc4b19f565cb8527074b; a table with its first entry negated was rejected; `ci/compare_signs.sh`, the standing comparison through the Rocq bridge, was not run |

## Advisor findings

| Finding | Verdict | Change |
|---|---|---|
| the builder ran neither `sh ci/check.sh` nor a full-library build | answered: the `lean` workflow runs `sh ci/check.sh` on the pull request and is green | none |
| the pull-request body and the commit message could name a host or a local path | checked: neither does | none |
| the three products may owe a row of the claims ledger or of the headline results | no row: the claims ledger lists the sources of `ci/claims/expected-sources.tsv`, which does not include the script that states these products, and a headline row is a theorem the README table names; the statements are fixed-level and proved once, in Lean | none |
| "squared norm" needs the star convention | `Tower.dot a b` is `re (a * star b)`; for coefficients with the trivial star (the rationals, the reals) `dot z z` is the sum of the squared coordinates, and the theorems hold for every star ring as stated | this record |

## Scope

The file proves three products of the sedenion level and their trace-form values. It does not prove that a circuit's
selector probability equals the trace-form value divided by 8, and it does not model the SELECT of that circuit. The
statements at level 5 that a kernel-map case would cite are not part of this change.
