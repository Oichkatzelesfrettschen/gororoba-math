# Review record: claims rows A5-572 to A5-611 and the findings pin (PR 127)

Head under review: 0c2e44edf. Reviewers chosen by the owner on 2026-11-25: codex on gpt-daybreak-blue at high effort (brief.md, report codex-report.md), then the Advisor last.

## Reconciliation of the codex findings
| Claim | Codex verdict | Parent check |
|---|---|---|
| 1. The 40 rows quote their sources (30-word cut, line numbers 551-590 of the findings ledger at 57c2c08bf) and follow the placement clauses | justified; check_claims_ledger.py passes on 1,327 rows | the quick workflow on this head passes the same checker |
| 2. A5-591 and A5-592 are partial with existing declarations | justified, with line numbers of each declaration | Phi_order4 (E8ConjugationMap.v:397), conj_C, conj_F, detB_Nm, detB_Np, detB_conj and conjugation_ideal (E8ConjugationIdeal.v:181) opened on main |
| 3. A5-571 and A5-542 follow their source status changes | justified | - |
| 4. expected-sources.tsv: 40 added, 0 removed, 549 changed (534 commit only, 15 commit and digest), topic notes unchanged at b7c2b373 | justified; the qualification is the 40 added rows | the parent compared the claim and status cells of the 15 digest-changed rows at b7c2b373 and 57c2c08bf: 13 changed only their basis text (A5-010, 019, 242, 278, 307, 332, 389, 409, 418, 425, 428, 457, 460), A5-542 changed status (open to survives) and A5-571 changed claim text and status (open to certified); both are rewritten in this change, and the A5-571 statement equals the first 30 words of the new claim |
| 5. The nine flagged placements | each justified with its clause | accepted |

Further defects: none found. Codex could not run `sh ci/check.sh --quick` (its sandbox mounts /tmp read-only); the hosted quick workflow ran it green on this head.

Conjectures the reviewer raised (recorded, not acted on here): universal conjugation transport of the Rees algebra over every ring with a square root of -1; boost flatness of the E8-bar -> VB fiber cone; a linearly joined minimal-degree family across E8-bar fibers; stable Gauss-image Hilbert data for A5-601.
