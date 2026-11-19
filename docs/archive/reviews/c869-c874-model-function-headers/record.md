# Review: successors of C869 and C874 scoped to the model functions

Pull request 79 of gororoba-math (issue 58). Reviewers by the owner's ruling of 2026-11-18 for new pull requests: the `codex` command-line agent (gpt-daybreak-blue, high effort, read-only) and the Advisor, last; no hosted review round.

## Brief

The codex reviewer read head b51c6ee; the Advisor read 7a50973, the head with the fixes and checked four claims: the five successor theorems restate the originals exactly under unclashing names; each test the headers name exists in `crates/gr_core/src/warp_metric.rs` of gororoba-open at 957fc28f and asserts what the header says; the headers claim no more than the theorems prove; the originals keep their bytes and the `_RocqProject` and `ci/rocq-warnings/allowed.tsv` rows are those a new source needs.

## Findings and reconciliation

| Finding (reviewer, head) | Check against the source | Resolution |
|---|---|---|
| P2 (codex, b51c6ee): the C869 header attaches `test_gating_interior_is_zero` to the theorem's bound, while the test evaluates rho = 0.1 and asserts a value below 0.01 | confirmed: `warp_metric.rs` line 443 calls `gating_function(0.1, 5.0, 10.0, 0.5)`; the theorem fixes rho = 0 and bounds by 1/2 | fixed in 7a50973: every named test is described as a numerical test at fixed parameters in f64 that instances no theorem, with the gating test's rho = 0.1 stated |
| P2 (codex, b51c6ee): the convention paragraphs list variables (r_s, rho, x, R, sigma) that are not the binders | confirmed: the theorems bind Rb, sig, rho_0, kappa, delta, L, sigma_x and fix the first argument at 0 | fixed in 7a50973: each paragraph names the binders, their hypotheses, and the argument evaluated at 0 |
| P3 (codex, b51c6ee): the residual-risk bullet on census counts is wrong, since the census lists only statements that name no `OpenGororoba` constant | confirmed: `ci/census/README.md` lines 3 to 4 | fixed in the pull-request body: the bullet states the census is unchanged by design |
| claim 1 justified, claim 4 unsettled pending the hosted gate (codex) | the hosted `rocq` workflow runs `ci/check_rocq.sh`, which compares warning pairs and kernel assumptions | the merge waits on a green hosted `rocq` check on the final head |

Fix 7a50973 also names `test_center_extrinsic_curvature_is_zero`, which asserts K_ij = 0 at the origin for the default parameters, as the numerical counterpart of the statement the files do not prove.

## Advisor

The Advisor read 7a50973 and confirmed each codex finding and its fix: the gating test calls the function at rho = 0.1 (`warp_metric.rs` from line 443); the convention paragraphs now match the binders and hypotheses of all five theorems; the census bullet matches `ci/census/README.md` lines 3 to 4. Claim 1 is justified; claim 4 holds once the hosted `rocq` check is green on the final head. Two further items, applied in the commit that files this record: `test_center_extrinsic_curvature_is_zero` also asserts that the ADM York time and `nacelle_york_time` are 0.0 at the origin, so the C874 header names it; the two C874 successor rows of `ci/rocq-warnings/allowed.tsv` move to sorted order. The subject of 7a50973 is longer than 72 columns; it is pushed and stays.
