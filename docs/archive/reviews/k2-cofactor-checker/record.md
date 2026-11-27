# Review record: K2 cofactor certificate checker and Hilbert upper bound (pull request 126)

Branch rocq/k2-cofactor-checker. Heads: 7e39ee268 under local review, 28a6001a1 after the fixes.

## Reviewers (owner's selection, recorded in pool row PROOF-41)
- codex gpt-daybreak-blue (high), read-only.
- agy gemini-4-neon-medium, red team.
- opencode on opencode-go/hy4-flash-free (free model), red team.
- The Advisor last.

## Findings and resolutions
| Finding | Reviewers | Class | Resolution |
|---|---|---|---|
| hilbert_upper_bound, hilbert_upper_sel and hilbert_cell_of_bound take check_bound = true, which hardcodes the monolithic unfactored check of every quadric (more than 30 h and 41 GB measured), so they cannot consume per-quadric membership proofs from a factored or basis-changed checker | codex, agy | read from source | Fixed in 28a6001a1: check_red checks the reduction data only; hilbert_upper_bound_of_red, hilbert_upper_sel_of_red and hilbert_cell_of_red take a per-quadric in_local_ideal hypothesis; the three old statements stay as corollaries through check_bound_red and check_bound_members |
| ymono truncates at the end of G or of the exponent vector, and check_cofactor checks neither lengths nor well-formedness, so the ordinary-substitution reading of the documentation overstates; the formal conclusion is sound for the truncating encoding | codex | read from source | Fixed in 28a6001a1: the documentation names the truncating encoding; check_red checks both lengths |
| check_entry checks neither msum (r_mu e) = d nor quadric index < length Q (soundness holds, canonicality does not) | opencode | read from source | Fixed in 28a6001a1: both checks added, check_entry_facts isolates them, mutant toy_index_rejected is rejected only by the index check |
| Unused prime p in LI_mult_transport; unused Ea in hilbert_upper_bound | codex, agy | read from source | Fixed in 28a6001a1 |
| Soundness of check_cofactor_sound: no key collision or overflow (enc_inj, unbounded positive keys), no dropped term (tget_tadd, tmul_get, tcombo_get, the length check), both sides reduced together (tall_sound, tree_pzero); 4-bit packed exponents restrict completeness only | all three | read from source | Note, no change |
| hilbert_cell_of_bound stays conditional on independent_mod (the toy spans a 1-dimensional quotient with two representatives) | opencode | read from source | Note: the PR body states it |
| Conjecture: one homogeneous Groebner basis of (Q) yields the reduction data for every d >= 2 | codex, agy | hypothesis | Open item for the factored route |

## Validation on 28a6001a1
- rocq-9.3 (Rocq 9.3.0) on the workstation, -w all,+default, capped scope 8G: both files compile (peak 0.43 to 0.47 GB); only allow-listed warnings; Print Assumptions closed for all eight theorems; rocq check shows no axiom.
- The 21 instance files stay outside this pull request (default-mode check of all 21 needs more than 30 h); the factored q08 check measured 220 s at 3.81 GB (local record w12-k2-factored), and the worst quadric extrapolates to about 26 GB, the next decomposition step.
