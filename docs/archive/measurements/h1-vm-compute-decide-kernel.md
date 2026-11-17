# Measurement: Rocq vm_compute against Lean decide +kernel on one table

Placement clause P7 of AGENTS.md ("Statements and proofs", Evidence) keeps large finite certificates in Rocq by default and states both costs of a certificate: evaluation and kernel re-check. This record holds the measurement behind that sentence (hypothesis H1 of the formalization program: Rocq `vm_compute` is at least ten times faster than Lean `decide +kernel` on one shared certificate). H1 is falsified on the library sign function.

## Proposition

For every pair p, q below 2^k with p, q nonzero and p != q, the sign of e_p e_q differs from the sign of e_q e_p (anticommutativity of distinct imaginary basis elements; both libraries prove it symbolically, so the decision is a pure evaluation benchmark).

- Lean: `CayleyDickson.Tower.negSign k` on `BitVec k`, folded over `List.range (2^k)` twice into `chk k : Bool`; proof `example : chk K = true := by decide +kernel`.
- Rocq: `CdTowerBasisSign.sigma k` on unary `nat`, folded with `forallb` over `seq 0 (2^k)` twice; proof `Lemma h1 : chk K = true. Proof. vm_compute. reflexivity. Qed.`
- Rocq binary variant: `sigmaN`, the same recursion over `N`, checked equal to `sigma` on the full level-6 table.

## Setup

Lean 4.35.0 (Lake 5.0.0, Mathlib v4.35.0, compiled with warnings as errors), Rocq 9.3.0 on OCaml 5.5.1 (`-w +default`); one Azure host with 4 vCPU (Intel Xeon Platinum 8573C). Each figure is the mean of three wall-clock runs of the file minus the mean of three runs of the same file without the check (import baseline: Lean 2.54 s, Rocq 0.27 s); spread at most 0.3 s. Level 5 ran 50 copies per file and divides.

## Results (net seconds)

| Level | Lean decide +kernel | Rocq vm_compute (sigma) | Ratio | Rocq vm_compute (sigmaN) | Ratio |
|---|---|---|---|---|---|
| 5 | 0.137 | 0.016 | 8.5 | not run | |
| 6 | 0.72 | 0.11 | 6.7 | 0.120 | 6.0 |
| 7 | 3.71 | 0.80 | 4.6 | 0.367 | 10.1 |
| 8 | 18.88 | 5.52 | 3.4 | 1.737 | 10.9 |

Kernel re-check of the compiled Rocq object (`rocq check -silent -o`, one run per level, net of the same check on a file without the lemma): level 7, 6.6 s; level 8, 51.4 s. Peak memory at level 8: Lean about 10 GB, Rocq about 0.4 GB.

## Reading

- On the library function the ratio falls from 8.5 to 3.4 as the level grows: unary `nat` arithmetic in `sigma` grows about 7x per level while the pair count grows 4x. The binary variant reaches the threshold at levels 7 and 8; its level-7 figure rests on 0.37 s at 10 ms timer resolution.
- The kernel re-check reverses the order: at level 8 Rocq's checker takes 51 s against 19 s for Lean's kernel decision, which already runs in the kernel.
- Not run: `native_compute` (the switch is configured without the native compiler), Lean `leanchecker` on the decision, levels above 8.
