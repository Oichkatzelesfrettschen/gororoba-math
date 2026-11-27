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
| hilbert_upper_bound, hilbert_upper_sel and hilbert_cell_of_bound take check_bound = true, which hardcodes the monolithic unfactored check of every quadric (more than 30 h and 41 GB measured), so they cannot consume per-quadric membership proofs from a factored or basis-changed checker | codex, agy | read from source | Fixed in 28a6001a1: check_red checks the reduction data only; hilbert_upper_bound_of_red, hilbert_upper_sel_of_red and hilbert_cell_of_red take the per-quadric hypothesis forall q, In q Q -> LI p n (J ++ m_products n G 2) (subst_q n G q) (degree 2, the membership the monolithic check_cofactor ... G 2 certifies); the three old statements stay as corollaries through check_bound_red and check_bound_members |
| ymono truncates at the end of G or of the exponent vector, and check_cofactor checks neither lengths nor well-formedness, so the ordinary-substitution reading of the documentation overstates; the formal conclusion is sound for the truncating encoding | codex | read from source | Fixed in 28a6001a1: the documentation names the truncating encoding; check_red checks both lengths |
| check_entry checks neither msum (r_mu e) = d nor quadric index < length Q (soundness holds, canonicality does not) | opencode | read from source | Fixed in 28a6001a1: both checks added, check_entry_facts isolates them, mutant toy_index_rejected is rejected only by the index check |
| Unused prime p in LI_mult_transport; unused Ea in hilbert_upper_bound | codex, agy | read from source | Fixed in 28a6001a1 |
| Soundness of check_cofactor_sound: no key collision or overflow (enc_inj, unbounded positive keys), no dropped term (tget_tadd, tmul_get, tcombo_get, the length check), both sides reduced together (tall_sound, tree_pzero); 4-bit packed exponents restrict completeness only | all three | read from source | Note, no change |
| hilbert_cell_of_bound stays conditional on independent_mod (the toy spans a 1-dimensional quotient with two representatives) | opencode | read from source | Note: the PR body states it |
| Conjecture: one homogeneous Groebner basis of (Q) yields the reduction data for every d >= 2 | codex, agy | hypothesis | Open item for the factored route |

## Validation on 28a6001a1
- rocq-9.3 (Rocq 9.3.0) on the workstation, -w all,+default, capped scope 8G: both files compile (peak 0.43 to 0.47 GB); only allow-listed warnings; Print Assumptions closed for all eight theorems; rocq check shows no axiom.
- The 21 instance files stay outside this pull request (default-mode check of all 21 needs more than 30 h); the factored q08 check measured 220 s at 3.81 GB (local record w12-k2-factored), and the worst quadric extrapolates to about 26 GB, the next decomposition step.

## Checks after the fixes (parent and Advisor)
- check_factored_sound on branch rocq/k2-factored-q08 concludes in_local_ideal p n (J ++ m_products n G 2) (subst_q n G q), so a factored certificate supplies the _of_red hypothesis through LI_of_ili.
- No real E8-bar -> VB reduction table is tracked; the stricter check_entry is calibrated on the toy instances only.
- The 23 untracked instance files are copied with their sha256 list to gororoba-math local/a5-tower/research/k2-instances/; the renderer's bytes stay at 11a47c050 (sha256 f0e359de...).
