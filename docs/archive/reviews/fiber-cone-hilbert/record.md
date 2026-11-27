# Review record: Hilbert function of the fiber cone (pull request 141)

Branch lean/fiber-cone-hilbert. Heads: c0eff5508 under local review, c96bd01c5 after the fixes.

## Reviewers (owner's selection, 2026-11-27)
- agy gemini-4-neon-medium, red team; opencode on opencode-go/hy4-flash-free (free model); the Advisor last.

## Findings and resolutions
| Finding | Reviewer | Class | Resolution |
|---|---|---|---|
| finite_piece takes a generating tuple but uses only I.FG | agy | read from source | Fixed in c96bd01c5: finite_piece (hI : I.FG) |
| The module docstring calls fiberMap "the surjection" without the generating hypothesis (counterexample: k[[t]], I = (t^2), f = t^3) | opencode | read from source | Fixed in c96bd01c5: "when the f_i generate I"; the section variables f and hf are named |
| mem_map_maximalIdeal_iff uses no property of the maximal ideal | agy | read from source | Fixed in c96bd01c5: mem_map_iff for any ideal J, the old name as the J = m case |
| The quotient form measures dim (k[y]/K)_n honestly (the mkₐ-image of the degree-n polynomials, K homogeneous by homogeneousComponent_mem_ker) | both | read from source | Note, no change |
| Conjecture: k[y] / ker fiberMap ≃ F(I) as graded k-algebras under the generating hypothesis | both | hypothesis | Fixed in c96bd01c5 as fiberMapQuotEquiv (k-algebra isomorphism; the grading through homogeneousComponent_mem_ker and fiberHilbert_eq_finrank_quotient) |
| Conjecture: IsPolynomialFiber iff h_F(n) = C(n + s - 1, n) for every n | agy | hypothesis | Open item |
| ker_fiberHom_eq_comap unused; the direct-sum decomposition of k[y]/K left implicit | agy | read from source | Note: kept as the rank-nullity hook |

## Validation on c96bd01c5
- lake build --wfail exit 0 on the workstation (Lean 4.35.0, Mathlib v4.35.0); axioms propext, Classical.choice, Quot.sound; leanchecker replay exit 0.
