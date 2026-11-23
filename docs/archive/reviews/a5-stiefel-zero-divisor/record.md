# Review record: A_5 Stiefel elements are zero divisors (pull request 97)

Brief: `brief.md` beside this file. The local seats read commit d97e68dd0. Reviewer: the `codex` command-line agent on
gpt-daybreak-blue at high effort. Red team: `opencode` on opencode-go/deepseek-v4-pro (the owner's substitute for agy,
whose quota was exhausted). Neither seat compiled Rocq; the gate of the pull request supplies the build evidence.

| Finding | Seats | Check | Resolution |
|---|---|---|---|
| The docstring and the pull-request body say "every field", while `PfField` also requires decidable equality | codex (low) | Confirmed: `PfField.eq_dec` (Pfaffian.v) | Fixed in 90bbc0c11: the statement names decidable equality, characteristic other than 2 and i |
| `pf_expand_at` is proved and never used | opencode (hygiene) | Confirmed: no reference in rocq/ | Fixed in 90bbc0c11: removed |

Survived both seats:

- `stiefel_zero_divisor` and `real_stiefel_zero_divisor` state a nonzero annihilator under exactly the Stiefel
  condition (pure halves, a.a = b.b, a.b = 0 as inner products), on the tower product of CdTowerRing.v.
- `pf_zero_kernel` carries the hypotheses its uses meet (skew, even length, distinct indices, characteristic other
  than 2).
- The certificate is fail-closed: `lookup` checks the key and the index list, `entry_ok` requires every child, and
  `pf_A_eval` lifts the local checks to the Pfaffian of `PfaffianTheory`.
- The transport ties the certified matrix to the tower product without a convention change (`sgn_tab_ok`,
  `evM_Aent`).
- `Cplx` is a field.
- The ledger rows match the theorems: a nonzero annihilator, with the README's nullity bound of 4 and the
  determinant identity left open.

Neither seat found a defect in the mathematics.
