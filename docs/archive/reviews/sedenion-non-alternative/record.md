# Review record: rocq/open SedenionNonAlternative.v (pull request 92)

Brief: `brief.md` beside this file. Reviewers: the `codex` command-line agent on gpt-daybreak-blue-latest at high
effort, which read commit f3f21c99e, then the Advisor last, which read 58a91fc25 with the codex findings and their
fixes.

## Codex findings and their resolution

1. Serious: `ci/claims/ledger.tsv` cited `SedenionAlternativityFails.v` as evidence. C-813 (row 473) cited its
   `sedenion_not_alternative`, whose statement mentions only two declared constants and never `sed_mul`. Nine
   every-level rows cited the same file. Confirmed against the predecessor's lines 44-45 and 71-74. Fixed in
   58a91fc25: those rows cite `SedenionNonAlternative.v:sedenion_not_left_alternative` (the left-alternative rows)
   or only their Lean theorems (the right-alternative rows). C-813 also cites
   `C002_SedenionZDAndNormFail.v:C002_zero_divisors`, a zero-divisor pair of the same `sed_mul`, and is `proved`.
2. Serious: the Rocq certificate lacked the instance-bridge comment that `AGENTS.md` ("Statements and proofs")
   requires toward the general Lean theorem. Confirmed: `lean/GororobaMath/CayleyDickson/Alternative.lean`,
   `CayleyDickson.Tower.exists_left_alternative_ne`, uses the same witness at level 4. Fixed in 58a91fc25 and
   refined in the commit after it: the comment names the theorem, the substitution R = the reals and k = 4, and the
   matching associator `(2 : Z) . e 15` (`associator_witness_left`, with `associator a b c = a * b * c - a * (b * c)`
   from `Associator.lean:47`).
3. Sloppy: the header cited `sed_mul_fused_basis_xor`, whose conclusion is about `sed_mul_fused`. Confirmed
   (`CDFusedBilinear.v:204`). Fixed in 58a91fc25: the header also names `sed_mul_fused_eq` (`CDFusedBilinear.v:67`).
4. Cosmetic: the header stated the basis-unit law as a negation. Fixed: it states the law positively.

Codex computed the signs (-1, +1) and the alternator (2 e_15) by hand from the sign table and the XOR rule. It found
the predecessor's digest cited once in gororoba-open (an audit checksum list), and the predecessor keeps its bytes.

## Advisor verdict

The Advisor confirmed findings 1-3 and the direction of 4. It struck an inference that the first rewrite of finding 4
added, which no theorem states, and asked that the bridge comment's alternator be checked against the Lean
`associator` definition. Both are done in the commit after 58a91fc25. It also required:
- the hosted checks green on the final head, the ledger edit included;
- this record free of local paths;
- the pull-request body updated.

It noted, without blocking, that the README still states 41 quantum sources while the gate compiles 63. That count
is outside this change and stays a separate correction.

## Validation

The hosted `rocq` workflow compiled all 373 project-listed `rocq/open` sources and kernel-checked them, with
axioms matching the ledger (135). Its only failure, on ed2d2ac98's parent, was the two allow-list pairs of the new
source's Stdlib Reals warnings. Both warning names have cause rows in `ci/rocq-warnings/causes.tsv`, and
ed2d2ac98 adds the pairs. The final head's `rocq` and `lean` runs are this pull request's checks.
