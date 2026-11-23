# Brief: review of gororoba-math PR 97, the Rocq proof that A_5 Stiefel elements are zero divisors

Role: adversarial reviewer (codex) or red team (opencode).

Read first: /home/eirikr/Projects/gororoba-workspace/AGENTS.md, then /home/eirikr/Projects/gororoba-workspace/gororoba-math/AGENTS.md ("Statements and proofs", "Rocq sources"). Work read-only: change no file (print your report as your answer); never commit or push; spawn no subagents. This host is a build host: run no Rocq compile, gate or test suite, and keep any computation under two minutes. Name machines by role.

Material: branch rocq-a5-stiefel-pfaffian at d97e68dd0, checked out in your working directory; `git diff origin/main...HEAD` is the change. Sources: rocq/quantum/Pfaffian.v, StiefelA5Certificate.v, StiefelA5Pfaffian.v, StiefelA5Transport.v, StiefelA5ZeroDivisor.v, StiefelA5Real.v; ci/claims/ledger.tsv, ci/rocq-warnings/allowed.tsv, rocq/quantum/_RocqProject. The PR body: `gh pr view 97 -R Oichkatzelesfrettschen/gororoba-math`. The gate passed in CI (rocq job 1 h 45 min, lean job 20 min). The mathematics: gororoba-quantum docs/evidence/a5-stiefel-pfaffian-germs/README.md, Theorem 1 (read it in /home/eirikr/Projects/gororoba-workspace/gororoba-quantum).

## Questions
1. Do the final statements (StiefelZeroDivisor.stiefel_zero_divisor, real_stiefel_zero_divisor) state what the ledger rows claim (a5-stiefel-universal proved; A5-364 partial)? Is the hypothesis set exactly Moreno's Stiefel condition (pure halves, a.a = b.b, a.b = 0), and is y5 the tower element it should be (coordinates, index layout, the cd_core doubling of CdTowerRing.v)?
2. Pfaffian theory: is pf_zero_kernel stated with the right hypotheses (skew, even length, distinct indices, characteristic not 2), and do pf_swap_at, pf_move_front and pf_transv prove what their names say? Any lemma whose statement is weaker or stronger than its use?
3. Certificate: can check_table tbl = true hold for a table that does not compute the Pfaffian of Amat (lookup by key with list equality, entry_ok, the root check)? Does pf_A_eval's induction cover every stored entry it uses?
4. Transport: do phi and psi and the 32 component lemmas tie the certificate's matrix to the tower product without a hidden convention change (sgn_tab against sgn16, Aent against Amat in evM_Aent)?
5. The real corollary: is Cplx a field as claimed (inverse, eq_dec), and do re/im/emb and mul_emb justify the real statement?
6. The PR body and ledger notes: any claim the sources do not support (nullity, cost figures, generality)?

Report ranked by consequence, each item marked documented, computed or hypothesis, with file:line. Print it as your answer, under 180 lines.
