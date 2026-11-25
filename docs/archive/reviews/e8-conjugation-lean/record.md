# Review record: gororoba-math PR 129

Head under review: ec79877eb. Reviewers chosen by the owner on 2026-11-25: codex on gpt-daybreak-blue (brief.md, codex-report.md) and agy on gemini-4-neon-medium as red team (brief-red.md, agy-neon-report.md); the Advisor runs last. Fixes after the round: af37de11a and its parents on this branch.

| Finding | Reviewers | Parent check | Outcome |
|---|---|---|---|
| generator lists equal the sing data | codex (sha256 of sorted monomial streams), agy | - | justified |
| the flip in jm_phi_flip is on s3, s5, s6 (not s4) | codex, agy | read flipVars | PR description corrected |
| heartbeat comments say 12-16 terms; generators have 3-14 | codex, agy | counted from the parsed sing lists: 3 to 14 | fixed: per-generator lemmas, no maxHeartbeats raise remains, build green at the default limit (114ede3d5) |
| map_jpAt unused | agy | git grep | removed |
| parity-character sentence describes a Python check | codex | read the generator | relabeled |
| bridge omits span_phiFlip_jm and understates the Lean generality | agy | read the bridge | names and wording fixed (af37de11a); Boundary: conjugation_ideal_bridge is a value-level analogue over integer values, not the substituted Lean proposition (an ideal equality in MvPolynomial (Fin 10) Z), and its comment says so |
| compare script: GNU sed address, false calibration message after a failed check, no digest calibration | agy, codex | read the script | fixed: POSIX awk, early exit, a mutated-sing calibration with an unchanged-copy control (af37de11a) |
| unused CONTINUATION constant, inconsistent error prefix | agy | read the generator | fixed |
| five generator lines over 120 columns (ruff E501 in the hosted quick check on af37de11a) | hosted CI | read the log | wrapped; the one template line changes a Lean docstring, so the module was re-rendered: the generator's --check reports it fresh and compare_e8_conjugation.sh passes both rejections on the workstation; lake build --wfail, axioms and leanchecker pass |

The Advisor ran last on 2026-11-25 over both reviewers' findings and the parent's checks; its corrections (the bridge row as a Boundary, the lint failure, re-reading the AGENTS.md diff) are applied above.
