# Review record: AGENTS.md generator list and five comparisons (PR 128)

Reviewer chosen by the owner on 2026-11-25: the Advisor only.

Advisor verdict: each of the five comparison sentences matches its script's header and tool loop (compare_cz_matrix.sh, compare_hilbert_cell_header.sh, compare_walsh.sh, compare_pfaffian.sh, compare_box_kite_census.sh), and the generator sentence matches the pairs list of ci/check_quantum_sources.sh. Two items followed: the inserted clause broke the list of what ci/quantum-sources/ holds, fixed in this record's commit; and ci/check_quantum_sources.sh has not run with its two new pairs (conjugation_map_certificate, e8_conjugation_ideal), recorded as not run in the pull-request body.
