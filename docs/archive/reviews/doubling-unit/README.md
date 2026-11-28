# Review of the doubling-unit lemmas (pull request 153)

The change adds `lean/GororobaMath/CayleyDickson/DoublingUnit.lean`: for the doubling unit `h`, `h (h z) = -z`;
for `x` with imaginary halves, `h (x z) + x (h z) = 0`; and the kernel of `x` is invariant under `h`. All three hold
over every nonassociative star ring. The owner chose no command-line reviewer and two red-teamers; the Advisor
reviews last. Head under review: `b947d1e36`. Local paths in the retained files read `WORKTREE` and `SCRATCH`.

| Role | Agent | Run |
|---|---|---|
| red team | `agy` on gemini-4-neon-medium | [report](reports/report-agy-neon.md), [brief](reports/brief-redteam.md) |
| red team | `opencode` on opencode-go/hy4-flash-free (the free deepseek model hit its usage limit) | [report](reports/report-opencode-hy4-flash-free.md) |

## Findings and verdicts

| Finding | Source | Verdict |
|---|---|---|
| Both theorems hold, and neither hypothesis can be weakened: `z = h` gives `h (x h) + x (h h) = (-(star a + a), -(star b + b))` | Neon, opencode | confirmed; no change |
| A non-terminal `simp` before `abel` breaks the `simp only` rule (`AGENTS.md`, "Proof hygiene") | Neon, opencode | confirmed; each goal now carries the `simp only` list that `simp?` printed |
| The first commit has no evidence sentence in its body | Neon | boundary: the commit is pushed and force-push is denied; the follow-up commit carries the sentence |
| The docstring said "every level" (level 0 has no doubling unit), named too few ingredients, and equated imaginary halves with orthogonality over any ring | Neon | confirmed; it reads every doubled level `Tower R (k + 1)`, names the unit, zero and star laws, and keeps orthogonality to the reals |
| The citation should be Lemma 5.2, Lemma 5.7 with `alpha = i_n` and Lemma 9.6, with Proposition 5.3 and Lemma 6.4 as context | Neon (opencode accepts the original as fair) | confirmed; the docstring cites each |
| `CayleyDickson.unit` already names `(0, 1)`, and `Tower.mk_mul_iota_mul`, `Tower.mul_cs_mul_eq_zero` and `Tower.iota_mul_iota_mul` state the field-level twins | Neon, opencode | confirmed; the module uses `unit` (the theorems are renamed to `unit_*`) and names the twins |
| Next step: the parity of `ker L_p n ker L_q` through a determinant lemma over an ordered field (both reviewers wrote and compiled one) | Neon, opencode | recorded as the next PROOF-68 target; not in this change |

## Advisor

The Advisor reviewed last, on the findings above and the fix commit `b02ac4f94`. Its findings: the opencode report named a
build-tree path of the compute workstation (replaced with a description), the hosted checks had been read on no head,
and the review documents had not passed the quick tier. The quick tier and the `lean` and `rocq` runs of `main` are
read before the merge.
