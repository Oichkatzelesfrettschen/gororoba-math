# Review record: iterated squares and independent associator indices

Pull request 154 of gororoba-math, branch `lean/iterated-square-associator-indices`. It answers two reviewer conjectures of
`docs/archive/reviews/proof71-corollaries/record.md` (pool row PROOF-76) and tests the A5-662
counts over fields of prime-power order (pool row PROOF-75's falsifier).

## Results

| Declaration or record | Statement | Evidence class |
|---|---|---|
| `Tower.iterate_mul_self_eq_zero_iff` (`SquareZero.lean`) | over a commutative ring without zero divisors, for `m >= 1` the m-fold iterated square of x is zero exactly when x * x = 0 | proved |
| `Tower.mul_self_eq_zero_of_mul_self_mul_mul_self_eq_zero` | its hypothesis `2 ≠ 0` removed; characteristic two handled by x * x = -N(x) 1 | proved |
| `Tower.mul_self_eq_self_iff_of_two_eq_zero` | when 2 = 0 the only idempotents are 0 and 1 | proved |
| `Tower.independent_of_associator_e_e_e_ne_zero` (`AssociatorPhaseNonzero.lean`) | a nonzero basis associator has nonzero, pairwise distinct indices with `p ^^^ q ≠ x`, over every nonassociative ring with a star | proved |
| `quaternion_prime_power_counts.py` | A_2 over F_9, F_25, F_27: q^2 square-zero elements and q^2 + q nontrivial idempotents; over F_4, F_8: q^3 and 0 | computed (exhaustive, 5 s, lab host aarch64, python 3.14) |
| `ci/claims/ledger.tsv` A5-661 | proof cell cites `iterate_mul_self_eq_zero_iff`; note states the iterated-square result with no hypothesis on 2; status stays partial | record |

The first run of the script reported 91 idempotents at F_9 against the predicted 90: index 1 of
the field table named the generator t instead of 1, so the identity counted as a nontrivial
idempotent. The digit order was reversed and a check that index 1 is the unit was added; the
prediction then held at every field.

## Reviewers

`codex` (gpt-daybreak-blue, effort high, read-only sandbox) and `agy` (gemini-4-neon-medium, red
team) read `brief.md` at head 7dba38efe; their reports are `codex-report.md` and
`agy-report.md`, with local paths and host names removed. agy compiled its counter-proof and
recounted the quadrics on the lab host; codex ran read commands only.

## Reconciliation

| Finding | Source | Verdict | Resolution |
|---|---|---|---|
| `2 ≠ 0` is avoidable in the iterated-square and fourth-power lemmas: when 2 = 0, x * x = -N(x) 1 | both | confirmed: agy's proof compiled; rebuilt at 9336577e2 with `--wfail` | Fixed in 0be29c054 |
| A5-661 understates the new coverage: cite `iterate_mul_self_eq_zero_iff` and restate the note; keep partial | both | confirmed against `ledger.tsv:1216` | Fixed in 0be29c054 |
| The power sentence names span closure only; reassociation needs `associator_span_one_self` | codex | confirmed (`Associator.lean:189`) | Fixed in 0be29c054 |
| Module header of `AssociatorPhaseNonzero.lean` says every result assumes `2 ≠ 0`; `x ≠ p ^^^ q` against `p ^^^ q ≠ x` | agy | confirmed | Fixed in 0be29c054 |
| The control misses a paired flip of s(1, 2) and s(2, 1), which leaves every square unchanged and breaks associativity | agy, codex (noted) | confirmed: squares read s(i, j) + s(j, i) | Fixed in 9336577e2: an associativity check of the table, with the paired flip as a second control |
| Split quaternions keep the F_9 counts and change only the predicate mismatches | agy | confirmed as stated; the main-field check already requires 0 mismatches, so that table fails it | Refuted as a defect: `main` compares the whole count record, mismatches included |
| Line 53 of the script is 106 columns, over a 100-column limit | both | the 100-column limit is the Lean linter's; `ruff.toml` sets `line-length = 120` and ruff passes | Refuted |
| Commit 0c6d1d38b changes proofs without the evidence sentence of "Proof hygiene" | agy | confirmed | Boundary: the commit is pushed and stays unamended; 0be29c054 carries the sentence, and the build of 0c6d1d38b is recorded here and in the pull-request body |
| Gates on the final head not run | codex | confirmed at review time | Fixed: the full gate passed at 391401d03 ("Validation") |
| Reducedness may suffice in place of `NoZeroDivisors` for the fourth-power and iterated-square lemmas | both | open: the proof uses no zero divisors in the `2 = 0` branch and through `mul_self_eq_zero`; a reduced-ring statement needs another proof | Boundary: open item, pool row |
| A5-649's proof cell could cite `independent_of_associator_e_e_e_ne_zero` | agy (optional); codex (no change) | A5-649 states the count alone, which `card_associator_e_e_e_ne_zero` carries | Boundary: cell unchanged |

## Conjectures

1. Characteristic two (both reviewers): over F_q with q even, A_n has q^(2^n - 1) square-zero
   elements and no idempotent other than 0 and 1. The idempotent half is now
   `mul_self_eq_self_iff_of_two_eq_zero`. The count follows from x * x = -N(x) 1 when 2 = 0 and
   N(x) = (sum of coordinates)^2 in characteristic two, and is not yet stated in Lean; it held at
   n = 2 over F_4 and F_8.
2. Signature invariance (agy): over odd F_q every split Cayley-Dickson signature gives the A5-662
   counts, since the product of the imaginary norm coefficients is a square. Falsifier: a
   signature of A_3 over F_3 with counts other than 729 and 756; test: 2,187 points per
   signature.
3. Associating independent triples (both): for D = 2^n >= 8 the independent ordered index triples
   with zero basis associator number (D - 2)(D - 4)(D - 8)/2: 0 in the octonions, 672 at D = 16.
   It follows from `independent_of_associator_e_e_e_ne_zero`, which puts every nonzero triple
   among the (D - 1)(D - 2)(D - 4) independent ones, and the proved nonzero count; the count of
   independent triples is not yet stated in Lean.
4. Reduced coefficients (both): the fourth-power and iterated-square lemmas hold over every reduced
   commutative ring. Falsifier: a reduced ring with zero divisors and an x with x * x ≠ 0 and
   (x * x) * (x * x) = 0; cheapest test: level 1 over F_3 × F_3.

## Route for A5-662 in Lean (PROOF-75)

Both reviewers found no diagonal-quadric point count in Mathlib v4.35.0. agy names the pieces:
`quadraticChar_card_sqrts` (`Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/Basic.lean:213`)
for one variable, and `jacobiSum_nontrivial_inv` (`Mathlib/NumberTheory/JacobiSum/Basic.lean:140`)
for the two-variable convolution, giving N_2(0) = q + χ(-1)(q - 1) and N_2(c) = q - χ(-1) for
c ≠ 0; induction by pairs then gives the odd-dimensional counts. Both Mathlib declarations were
opened by grep in the Mathlib v4.35.0 tree: `quadraticChar_card_sqrts (hF : ringChar F ≠ 2) (a : F)
: #{x : F | x ^ 2 = a}.toFinset = quadraticChar F a + 1` and `jacobiSum_nontrivial_inv (hχ : χ ≠ 1)
: jacobiSum χ χ⁻¹ = -χ (-1)`; codex's "not found" for the Jacobi piece came from a sandbox that
could not reach that tree. The coordinate bridge (`Tower.re_eq_repr_zero`, `Tower.dot_eq_sum_repr`,
`Tower.borderEquiv`) is cited by agy and unopened here.

## Validation

- `lake build --wfail` of both modules at 9336577e2: passed (28 s over a built tree; lab host,
  aarch64, Lean 4.35.0, Mathlib v4.35.0).
- `#print axioms` of the four theorems: propext, Classical.choice, Quot.sound.
- `sh ci/check.sh` at 0c6d1d38b: passed in 941 s (kernel replay of 100 modules, fixture
  rejected), with the script present as an untracked file.
- `sh ci/check.sh` at 391401d03, clean tree: passed in 591 s, the kernel replay accepting 100
  tracked modules and rejecting the fixture.
- `sh ci/check_rocq.sh`: not run (no Rocq path changes).

## Hosted round

`@Codex review` on 391401d03: "Didn't find any major issues" (review state `has_any_findings:
false`).

## Advisor

The Advisor reviewed last, with both reports and this reconciliation: no blocking defect in the
Lean, the script or the ledger edit. The statement recheck holds: the iterated-square theorem for
every m >= 1 implies the conjecture's existential form; the `2 = 0` branch of the fourth-power
lemma is sound and the other branch still uses `mul_self_eq_zero_iff`, which needs `2 ≠ 0`; the
seven conjuncts of the index theorem are the seven nonzero combinations of p, q, x over the
two-element field; A5-661 stays partial. Its requests, applied in this commit: complete the
validation and review sections, record the reducedness and A5-649 items, settle the Mathlib
citation conflict by grep, and label conjectures 1 and 3 as consequences of proved statements.
