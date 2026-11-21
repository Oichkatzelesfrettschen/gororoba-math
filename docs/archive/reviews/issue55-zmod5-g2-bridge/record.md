# Review: headline rows for the mod-5 kernel swap and the G2 derivation dimension

Pull request 89 of gororoba-math (issue 55). Reviewers, in order:
- the `codex` command-line agent (gpt-daybreak-blue, high effort, read-only) on head 975656e;
- the Advisor, last.

The owner's ruling of 2026-11-18 sets the review chain for gororoba-math pull requests at local codex and the Advisor, so this pull request has no hosted round.

| Finding (codex, 975656e) | Check | Resolution |
|---|---|---|
| P1: the PR body leaves the `ci/check_rocq.sh` result open, and the recorded runs predate 975656e, whose warning row the bridge-only compile does not exercise | Confirmed. | `sh ci/check_rocq.sh` on 975656e exits 0: 372 open, 63 quantum and 4 delegation modules compiled and kernel-checked, warning pairs all allowed, axiom ledgers matched. The PR body records it. |
| P2: `docs/plans/lean-generalizations.md` still calls every row an uncompiled proposal and says rows 118 to 121 each owe a bridge | Confirmed against the file. | Fixed in 4183196: the introduction states that landed rows name their compiled declaration, and the bridge paragraph separates the landed row-119 bridge from rows 118, 120 and 121. |
| Claims 1 to 4 and 7: the mod-5 statements, both challenge restatements and the three bridge clauses match their sources; comments and subjects follow the voice rules | Justified from source. | - |
| Regression checks: `ci/check_headline_results.py` passes (110 rows, 34 challenge configurations); no new `NON_DECLARATION_TOKENS` entry needed; `Challenge.Derivation` stays out of `lean/Challenge.lean` | Agrees with the gate run (`ci/check.sh` exit 0 on bd5da82; the later commits change only the warning list and plan prose). | - |

## Advisor

The Advisor confirmed the codex P1 (resolved by the `ci/check_rocq.sh` run on 975656e), the P2 fix in 4183196, and the three bridge clauses as the substituted hypotheses: independence holds on every input, the span coefficients are chosen before the input, and `Print Assumptions` is closed. It asked for three changes before the pull request leaves draft, all done:
- **Mechanism stated as fact.** The `leibnizSubmodule` docstrings and the PR body said `simp` and `abel` emit module-named auxiliary lemmas.
  - What was measured: the comparator rejected the `simp only` and `abel` proofs at `_proof_2` and accepts the `rw` proofs.
  - b00bb43 states that measurement and marks the module dependence `hypothesis:`.
  - After it, `lake build --wfail GororobaMath.CayleyDickson.Derivation` and `lake comparator --config Challenge/Derivation.json` pass.
  - Commit b161568 keeps its original subject.
- **`Closes:` and the plan.** Rows 118, 120 and 121 still owe bridges, and issue 55 was their tracker. Issue 90 now tracks them, and the plan paragraph names it, so the pull request still closes issue 55.
- **Hosted checks.** `gh pr checks 89` on b00bb43: both checks pass.

## External kernel

The two RingTowerI headline theorems (`Tower.kernel_swap_iff_two_eq_zero` and `Tower.zmod5_not_pure_kernel_swap`) were exported with lean4export v4.35.0 and accepted by nanoda (commit 0da9f98). The export holds their full dependency closure (176,017 lines), and nanoda permitted only `propext`, `Classical.choice` and `Quot.sound`. The nanoda pass over every Lean headline theorem is recorded separately.
