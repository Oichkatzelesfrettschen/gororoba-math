# Review record: factored K2 cofactor checker (pull request 146)

Branch rocq/k2-factored-q08. Heads: 93efffe92 under local review, 7c6592dae after the fixes (comment-only diff).

## Reviewers (owner's selection, 2026-11-27)
- codex gpt-daybreak-blue (high), read-only; opencode on opencode-go/hy4-flash-free (free model); the Advisor last.

## Findings and resolutions
| Finding | Reviewer | Class | Resolution |
|---|---|---|---|
| Module comments put the mechanism before the convention; main theorems lack one-sentence mechanism comments | codex | read from source | Fixed in 7c6592dae |
| Main results omit toy_data_accepted_f and toy_data_rejected_f | opencode | read from source | Fixed in 7c6592dae |
| The factored checker requires p > 0 where the plain one requires p <> 0 (negative moduli excluded, no soundness loss; the Hilbert application assumes prime p) | codex, opencode | read from source | Stated in the module comment in 7c6592dae |
| Soundness: regrouping (stage1_spec, horner, master), key collisions (enc_inj, tadd_enc), forced accumulation (check_factoredF_eq), counts (m_products_len); the 4-bit exponent mask limits completeness only | both | read from source | Note, no change |
| The template-universe fix at line 623 changes no statement | both | read from source | Note |
| Conjecture: for p > 0, check_factored = check_cofactor at d = 2 | codex, opencode | hypothesis | Open item |

## Validation on 7c6592dae
- rocq-9.3 (Rocq 9.3.0) on the workstation, -w all,+default, 8G scope: the six-file closure compiles; only allow-listed warnings; Print Assumptions closed for every theorem.
