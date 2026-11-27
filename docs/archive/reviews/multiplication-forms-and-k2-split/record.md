# Review record: multiplication forms and the split K2 cofactor checker (pull request 148)

Branch lean-multiplication-forms. Heads: 3fa36704b under local review, 9c0c0e055 under the first hosted Codex round, 2548ee171 after its fix.

## Reviewers (owner's selection of 2026-11-27)
- opencode, red team. The owner chose the free DeepSeek model; its free allowance was spent (provider.free-limit, retry after 3.3 h), so opencode/hy4-flash-free stood in, the free model of the K2 cofactor checker review.
- The Advisor last.
- Hosted Codex after this record: one finding on 9c0c0e055 (last row).

## Findings and resolutions
| Finding | Reviewer | Class | Resolution |
|---|---|---|---|
| ci/rocq-warnings/allowed.tsv lists no pair for K2CofactorSplit.v, whose Require line loads the same Stdlib set as K2CofactorFactored.v; the gate fails on an unlisted pair | opencode | read from source | Fixed in 08d7608e9: the two rows deprecated-transitive-library-file-since-Stdlib-9.0 and disj-pattern-notation, both names already in causes.tsv |
| The module docstring of MultiplicationForms.lean calls gramForm positive semidefinite and the derivative an exact three-form; no theorem states either, and exactness needs 3 invertible | opencode | read from source | Fixed: the docstring names gramForm_comm and ends at the identity skewForm_exterior_derivative |
| docs/archive/reviews/k2-cofactor-checker/record.md says the renderer's bytes stay at 11a47c050; the restored k2_cofactor_certificate.py differs (QUADRIC_F and --write-factored added) | opencode | read from source | Boundary: no file of gororoba-quantum, gororoba-open or gororoba-math pins the digest f0e359de (git grep on each origin/main, the one hit is that record's own sentence). The diff from 11a47c050 to the probe branch only adds lines, so the templates of the 23 retained instances are unchanged. That earlier record describes pull request 126 and stays as written |
| k2_cofactor_split.py renders no tracked source and has no --check mode, so its output has no drift check | opencode | read from source | Note: stated under residual risk in the pull request; the step sources enter with their own gate |
| toy_J and toy_G exist in both HilbertCellCertificate.v and K2CofactorCertificate.v; the import order selects the one-variable cell | opencode | read from source | Boundary: the vm_compute acceptance lemmas toy_step1_accepted and toy_step2_accepted fail under the other cell, so a reordering cannot pass silently. No change |
| skewForm_exterior_derivative is a linear combination of tripleForm_swap_left and tripleForm_swap_right, themselves the skew-symmetry lemmas of TraceForm.lean; LI_recover is LI_add and LI_scalec on q1 = (q1 + d q2) - d q2; forall_skewForm_eq_zero_iff is mul_eq_zero_iff_forall_dot_mul_eq_zero reversed | opencode | read from source | Note: the module packages library identities under the names of the three forms; no new mechanism is claimed |
| Hypothesis: for pure a, skewForm k a u (a * u) = - gramForm k a u u at every level; it fails at a = 1 | opencode | hypothesis | Open item, not stated in this pull request |
| The generators were reformatted and four lines hand-split after the probe branch; one constant's length was the only equality checked | Advisor | measured | Checked: ast.dump of the parsed k2_cofactor_split.py and k2_cofactor_certificate.py at this branch equals that of the probe branch (Python 3 on the compute workstation), so every rendered string is unchanged |
| The opencode pin search ran in two directories that are not checkouts | Advisor | read from source | Checked again in the three primary checkouts (previous row but two) |
| The pull-request body named the compile of K2CofactorSplit.v before a finished rocq-changed result existed | Advisor | process | The body now cites the finished hosted runs by head |
| --write and --write-factored of k2_cofactor_certificate.py and the write of k2_cofactor_split.py follow a linked rocq/quantum or a linked output file, against the write-confinement rule of AGENTS.md | hosted Codex (P1) | read from source | Fixed in 2548ee171: confine_output refuses a rocq/quantum that is a link, lies outside the checkout or holds a symbolic link, before each write; calibrated on the compute workstation (a plain directory accepted; a linked directory, a linked source, a linked K2Split.order and a directory outside the checkout refused) |

## Left on the archived probe branch
archive/rocq-k2-factored-probe (b43ced7f1) keeps the five accumulation-benchmark modules and K2FactoredCount.v, which import the untracked instance sources, and the older copy of K2CofactorFactored.v.
