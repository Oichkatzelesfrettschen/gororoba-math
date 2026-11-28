# Review record: claims rows A5-612 to A5-668 and the findings pin (PR 151)

Head under local review: 5d768cc7e. Reviewer chosen by the owner on 2026-11-28: codex on gpt-daybreak-blue at high effort (brief.md, report codex-report.md); the hosted Codex round and the Advisor follow.

## Reconciliation of the codex findings

| Claim | Codex verdict | Parent check and action |
|---|---|---|
| 1. The 57 added rows name their source lines at 6d2cdac90 and carry the 30-word cut of the claim | justified; 57 rows, zero mismatches | - |
| 2. Each placement follows the README rules | falsified at A5-622, A5-633, A5-648 (partly proved on main) and A5-623 (mixed axes) | each declaration opened on the branch: `star_mul_mul_sub_eq` (AlternativeIdentities.lean) and `toMatrix_mulLeft_star` (LeftMulMatrix.lean) give L_y^T L_y = N(y) I + the left associator at every level; `amExponent_eq` (SignLaws.lean) and `am_sign` (CdTowerBasisSign.v) state the transposed cochain; `liftMat_surjective` and `mono_linearIndependent` (ZeroEight.lean) give the generation of M_16(R) at n = 4. Fixed in 8b403433e: the three rows read partial with those proofs, and A5-623 reads ring-class, both, owed |
| 3. The five partial rows match their declarations | justified | - |
| 4. No owed row is proved on main | falsified by the same three rows | fixed in 8b403433e, as under claim 2 |
| 5. Relocations change the line alone, and the refreshed notes follow the sources | falsified at the A5-548 note, which put nine cells at 32057 | the source puts six cells at 32057 (A5-560) and the ninth decision over Q(i) (A5-641); fixed in 8b403433e |
| 6. The expected-sources diff and the README counts | justified: 57 added, 0 removed, digests changed at the eight rows only | the README counts move with the fixes to 15, 18, 1, 1, 195, 405, 9, 2 |
| 7. The flagged placements | A5-622 and A5-658 take the existing-proof clause; A5-623 takes the placement both; the others stand | applied in 8b403433e; the README states the use of both and of the existing-proof clause for these rows |

Hosted Codex round: requested on 52b8b55d0 at 2026-11-28T05:22:56Z; the receipt of 05:24:04Z reads "Didn't find any major issues" for that commit.

Validation after the fixes: `expected_sources.py` (1,384 sources) and `sh ci/check.sh --quick` pass on the compute workstation at 8b403433e.

## Conjectures the reviewer raised (recorded, not acted on here)

- One operator identity, L_y^T L_y = N(y) I + Assoc(y, y, -), organizes the null-slice spectra and the nullity transitions (A5-612, A5-622, A5-623, A5-635, A5-650 to A5-668).
- The commutant of the compression pencil (R, C, H) decides its Lie closure (so(8), su(4), sp(2)) as the full skew centralizer (A5-654, A5-659, A5-666, A5-667).
- The normalized scalars of the slice-change maps (i/2, 1/2, -1/2, -1, 1; A5-638 to A5-647) form one descent cocycle; falsifier: a closed loop of retained maps whose normalized product is not the identity at 32009 and 32029.
