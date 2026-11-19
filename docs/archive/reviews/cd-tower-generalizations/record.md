# Review: Lean generalizations of the Rocq tower results and the claims-ledger rows they prove

Branch `lean/ledger-partial-closure` of gororoba-math (issue 55, the claims ledger of issue 56's successor work). It holds tranches 2 to 6 of `docs/plans/lean-generalizations.tsv`, the ledger sweep, the associator, alternative-law, Artin, Kaplansky and inverse modules, and the integration merge fcc121e. Reviewers, by the owner's ruling of 2026-11-18: the `codex` command-line agent (gpt-daybreak-blue, high effort, read-only) and the Advisor, last. From 10:00Z to 10:54Z on 2026-11-19, codex hung at startup under the user configuration. Every review below ran with `--ignore-user-config`, on the same model, effort and sandbox.

## Findings and reconciliation

| Review (head read) | Finding | Resolution |
|---|---|---|
| tranches 2-3 (6578cb4) | P1: rows 42 to 47 mismarked in the proved table | Refuted. The `headline` column records that a theorem is cited in a record, not that it is proved (plan, "Columns"), and the branch leaves that column unchanged. |
| tranches 2-3 (6578cb4) | P2: row 21 needs no `IsLeftRegular (2 : R)` | Fixed. `Tower.mul_mul_self_eq'` (FlexibleLaw.lean, e509741) is the flexible law over every commutative ring with the identity as star, proved by base change through ℤ[X, Y]. |
| tranche 4 (ae8adcc) | P3: `x.re` never denotes `Tower.re` | Refuted by measurement. With `AnnihilatorSymmetry` imported, `#check fun k (x : Tower ℤ (k+1)) => x.re` prints `Tower.re (k + 1) x : ℤ`; that is why `compare_isum` printed zeros before ae8adcc. |
| tranche 4 (ae8adcc) | P3: row 99's docstring and the plan prose | Fixed in 6c45bbc. |
| tranche 5 (e509741) | P3: row 88 and row 93 citations; row 93 narrowing | Fixed in 6c45bbc. |
| ledger sweep and lemmas (0738e4c) | P2: C-153, C-302, C-187, C-1520, C-1463 and C-414 overstated; P3: the Associator module text | Read as partial in e9e984c. 1530013 then adds the missing theorems for C-302, C-153, C-187, C-1520 and C-414; C-1463 stays partial, because its architecture sentences are properties of a source, not of a theorem. |
| alternative laws and identity rows (7a374a7) | P2: 25 rows read proved while their claims report numeric measurements; P3: the commit says "Seventeen rows" for 18 | The 25 rows read partial in e9e984c; the count is recorded here, and the pushed commit text stays. |
| closure (1530013) | P2: C-153's source holds a false clause; P2: C-302 lacks the (1,2)-swap boundary | Resolved in f2fde96. The C-153 source says the direct form fails at dimension 4, where the associator vanishes and both forms hold; the row stays partial with this finding. C-302 cites `associator_add_swap_left_of_le_three` and `exists_associator_swap_left_ne`. |

| tranche 6 and fixes (e509741..6c45bbc) | P3: compare_order_three.sh and compare_schreier.sh print agreement before the mutant check; P3: the plan's narrowing list omits rows 93 and 95 | Fixed in 80e8d3c: the mutant check runs first, as in compare_anf.sh, and the list names both rows. |
| Advisor, final review of the round | Row 77's comparison was unwritten; C-188 and C-245 read proved while their claims report a numeric value; the four branches had never been gated together | 13cd6c9 and 04f74d6 extend compare_anf.sh with Tower.anfDegree, rejecting Rocq and Python degree mutants, with 334 tables agreeing. 151358e reads C-188 and C-245 as partial. A trial merge of the four branches is gated below. |

Integration found one defect the branch gates could not show. `Tower.re_one` and `Tower.re_smul` were declared in both `Kaplansky` and `OrderThree`, which came from different branches. The `OrderThree` copies are now private.

## Validation

On the compute workstation, with ruff 0.14.11 and actionlint 1.7.12 (the versions the `lean` workflow pins), `sh ci/check.sh` passed at each branch head. At the integration head every module builds with no warning, the axiom audit is clean, and kernel replay accepts every module. The five comparisons agree, and each rejects its mutant:
- `ci/compare_anf.sh`: 334 tables, 1002 rows
- `ci/compare_isum.sh`: 126 coordinates
- `ci/compare_am_exponent.sh`: 5460 exponents
- `ci/compare_order_three.sh`: 512 values
- `ci/compare_schreier.sh`: 37448 values

## Advisor

At the final review of the round, the Advisor named four blocking items: the tranche 6 review, row 77's comparison, the ledger rule on every row the branch moved to proved, and a combined gate of the four branches. The first three are done above. The combined gate result is recorded in the session's board and in the pull-request body.

## Scope

The pull request carries no `Closes:` line for issue 55. Three items remain on that issue:
- row 72, whose level-4 nullity spectrum is recorded in its narrowing cell;
- headline rows and challenge modules for results that records cite;
- the open-tree comparison halves of rows 75 and 81.
