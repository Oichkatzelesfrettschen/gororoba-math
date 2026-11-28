# K2 cofactor instances of the fiber E8-bar to VB

The 65 Rocq modules of this directory certify, over F_32029, that each of the 21 quadrics q of K2 satisfies
q(G) in J + m G^2, and bind the tables they use: `K2CofactorE8barVBTables.v` proves that `k2_J` and `k2_G` of the
header equal `a5_108_J` and `a5_108_G` of `rocq/quantum/HilbertCellA5_108.v`, the canonical header of this fiber.
Of the other 64, `K2CofactorE8barVB.v` states it for all 21 (`k2_quadrics_in_ideal`) from the chain
modules `K2CofactorE8barVBcNN.v`, each of which sums the steps `K2CofactorE8barVBsNN_MM.v` of quadric NN through
`LI_tele` and `LI_recover` of `rocq/quantum/K2CofactorSplit.v`. A step holds at most about 600,000 monomial
products and is accepted by `check_step_sound` under `vm_compute`. `K2Split.order` lists the modules in compile
order; they compile under the empty logical root beside `rocq/quantum` (`-Q . "" -Q ../quantum ""`).

`ci/quantum-sources/k2_cofactor_split.py` renders every file here from the certificate export
`a5-k2-cofactor-certificate-v1` of gororoba-quantum (39,644,470 bytes, sha256
`2d330081a19eb2e21dcc615185ace7b4f9e946597d6acde591786be2c5324c6f`, which the generator requires; the file
itself is untracked there). A source changes through the generator: `--write` renders the directory and
`--check` compares it.

`ci/check_k2_instances.sh` is the gate of this directory and the `k2-instances` workflow runs it nightly and on
dispatch. The admission gate `ci/check_rocq.sh` compiles and checks none of these modules (the changed tier scans
a changed one for declared assumptions): one `rocq check` process over all
of them was killed at 15 GB in both conversion modes, so the script checks one module per process
(`rocq check -norec`), and compares the axioms of the context summaries with `kernel-assumptions.txt`. Its 26
lines are fields of Stdlib and Corelib modules that `-norec` lists because it admits what a module imports; a
full check of `From Stdlib Require Import ZArith List Lia` lists none, and `-norec` also lists an axiom that an
admitted module declares (measured 2026-11-27).

Measured on 2026-11-27 (Rocq 9.3.0, a 32-thread x86-64 host that other jobs shared), on the 64 modules without
the table binding, which compiles in under a second:

- Compile of the 64 modules: 15 min 49 s at three jobs, 1,933 s summed over the modules, peak 6.65 GB in one
  compile; the objects take 821 MB.
- `rocq check -norec` with the bytecode machine, all 64 modules: 880 s of processor time; at most 5.86 GB and
  45 s a step, and 10.64 GB and 72 s on `K2CofactorE8barVB`, which loads the 63 other modules.
- `rocq check -norec` with the checker's own reduction, all 64 modules: every one passes, with the same 26
  ledger lines; 6,041 s of processor time (6,266 s of wall time on the shared host), at most 9.17 GB (s17_01),
  and 4.52 GB on `K2CofactorE8barVB`.
- The whole script with the bytecode machine, drift step included: 29 min 46 s at three compile jobs, 32 min 23 s
  and 44 min 24 s at two (the last beside the pure-kernel pass above); peak 10.63 GB.

The nightly run uses the bytecode machine; `gh workflow run k2-instances.yml -f kernel=pure` runs the checker's
own reduction. No hosted run of either has been timed yet.
