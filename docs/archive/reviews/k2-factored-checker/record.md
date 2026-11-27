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

## Additions after the Advisor
- ci/rocq-warnings/allowed.tsv gains six rows: the two existing names deprecated-transitive-library-file-since-Stdlib-9.0 and disj-pattern-notation for each of the three files, as PR 126's files carry; none for bad-template-constraint (owner decision: fix the source).
- K2CofactorForced.v lands as the retained refutation of the accumulation-order hypothesis: the forced variant is proved equal to check_factored and measured at 1,837 s and 3.53 GB on q08 against 220 s and 3.81 GB, so evaluation order does not bound the memory.
- The diff 93efffe92..7c6592dae was read line by line: comments only.
- Hosted checks on b34237964: quick, build, rocq-changed and main-gate succeeded.

## Hosted review
- Codex (requested 16:28Z on 3a6a002ca): no major issues; receipt comment on the pull request, no review threads.
