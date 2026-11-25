# Review record: gororoba-math PR 131

Head under review: 6ab5427d7. Reviewers chosen by the owner on 2026-11-25: codex on gpt-daybreak-blue (brief.md, codex-report.md) and agy on gemini-4-neon-medium as red team (brief-red.md, agy-neon-report.md); the Advisor runs last. Fixes after the round: 13a2c016c. With comments removed, the two versions of the file differ only in the two import lines (parent check, a comment-stripping diff).

| Finding | Reviewers | Parent check | Outcome |
|---|---|---|---|
| Claims 1 and 2 (congruences of C, sign lists of jm_flip_*) | codex, agy | - | justified; five jm_flip_* theorems (four base flips and their product T2) |
| "the flip that changes i to -i" and "root r to root -r" hide that T2 also negates s2, s3, s4, s6, s7, s8; a flip of i alone is no symmetry (detB_N- goes from (s2 - i)^2 to (s2 + i)^2) | codex (serious), agy | read flipx and T2; the wording came from the parent's brief | fixed: every comment names the complete involution (13a2c016c); PR description corrected. The detB sentence follows from detB_Nm (E8ConjugationMap.v): the i-only flipped point also has i^2 = -1, where detBD Cm Fm equals -1024 (s2^2 - 1)^2 (s2 + i)^2 |
| root_exchange_detB is stated on detBD Cm Fm, so it mentions Fm | codex | read the statement | comment says so and that no law for F or G is proved |
| docstring names checkEq and jp, which the file does not use; polarity of signed unstated; symm_* called identities of integer polynomials | agy, codex | read the file | fixed |
| RootExchange requires CommutativeRingWithI though only root_exchange_detB uses i^2 = -1 | codex, agy | evSP exists only in the ConjugationMap functor over CommutativeRingWithI | Boundary: layout kept; the docstring states which theorems use no property of D.i |
| unused imports Lia, InitialRing, StiefelA5Certificate, StiefelA5Pfaffian | agy | compile after removal | removed |
| vm_compute cost not in the file | agy | AGENTS.md, Evidence axis | docstring states 9 s compile, 97 s bytecode check, 2584 s pure check (at 6ab5427d7) |
| Conjectures: 16 generator-wise sign flips of J_N-, a kernel of order 4, T1 with the character of T2, J_N+ under T2p with the same character | agy | computed by the parent over the 27 parsed generators: the three generator statements hold (scalar action per generator); the detB_Np clause of conjecture 4 follows from detB_Np by the substitution s2 -> -s2, i -> -i (read, not compiled) | recorded as a local finding; not stated in this file |
| Conjecture: Fm(T2 x) = D2 Fm(x) E2, so detB_N- is invariant under T2 with i free | agy | the F compatibility with the flips matches an earlier parent computation on the sing data; agy's E2 vector and the i-free determinant consequence are not checked | open |

The Advisor ran last on 2026-11-25 over both reports and the parent's checks.
