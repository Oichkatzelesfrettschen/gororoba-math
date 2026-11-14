# gororoba-math

Machine-checked mathematics of the gororoba workspace: the statements that
[gororoba-quantum](https://github.com/Oichkatzelesfrettschen/gororoba-quantum)
and [gororoba-open](https://github.com/Oichkatzelesfrettschen/gororoba-open)
rest on, each compiled by a proof assistant and audited for the axioms it
uses.

## Lean library

`lean/` is a Lake package, `GororobaMath`, over Mathlib.

| Module | Result | Reads on |
|---|---|---|
| `GororobaMath.CayleyDickson.Basic` | the Cayley-Dickson double of a nonassociative ring with a star is again one (`instNonAssocRing`, `instStarRing`); `x * star x` lies in the first half (`mul_star_self`); the reflection `(a, b) -> (a, -b)` and the embedding `a -> (a, 0)` preserve products | the doubling `(a, b)(c, d) = (ac - conj(d) b, da + b conj(c))` of `gororoba_quantum/cd_core.py` |
| `GororobaMath.CayleyDickson.Tower` | at every level `k` and over every such ring, `e_p * e_q = sign(p, q) e_(p xor q)` (`Tower.e_mul_e`, `Tower.e_mul_e_sign`), conjugation negates every basis element but `1` (`Tower.star_e`), each of those squares to `-1` (`Tower.e_mul_self`) and two distinct ones anticommute (`Tower.e_mul_e_anticomm`); `Pathion R` is level 5, the 32-dimensional algebra `A_5` | `cd_core.cd_sign`, by the comparison below |
| `GororobaMath.CayleyDickson.TwoTerm` | an aligned pair `{x, x xor i xor j}` gives the zero product `(e_i + e_j)(e_x +- e_x') = 0` at every level over every ring (`Tower.two_term_mul_add_eq_zero`, `Tower.two_term_mul_sub_eq_zero`); `partner` is an involution without a fixed point for `i != j` and alignment is a property of the pair; the aligned-pair counts of the measured operands, evaluated in the kernel: 12 for `e_1 + e_18` and `e_1 + e_24`, 4 for `e_1 + e_26` and `e_2 + e_27`, 0 for `e_1 + e_17` in `A_5`, 4 for `e_1 + e_10` in the sedenions | the nullity reading of `docs/evidence/pathion-kernel-map/README.md`; the library defines no nullity yet, so the equality of the count with the nullity is a hypothesis that waits on the module structure of the tower |
| `GororobaMath.KernelMap.Estimator` | the bias identity of the hardware nullity estimator, `N_hat - N = \|B+\|\|B-\|/\|B\| (Vbar+ - Vbar-)/V_hat` for every observed contrast with `V_hat` nonzero (`nHat_sub_nullity`), and the forced reading `N_hat = \|B\|/2` of a block with no bin of ideal contrast `-1` (`nHat_eq_card_div_two_of_negBins_eq_empty`) | `docs/evidence/pathion-kernel-map/nhat-bias/README.md` in gororoba-quantum, claims 1 and 3 |

The tower theorems hold for every level and every coefficient ring, so they
cover the 64- and 128-dimensional runs as well as `A_5`. The estimator
theorems hold over every field of characteristic zero.

## Rocq trees

`rocq/open` is the proof tree of gororoba-open (350 sources under
`theories/` and `verified/`, with checkpoints, extraction targets and the
frozen quantum-observable evidence its bindings cite). `rocq/quantum` holds
33 sources: the 29 proof files of gororoba-quantum (the Cayley-Dickson
tower over ordered domains and commutative rings with its basis, base change,
order-three map and the kernel certificates of the canonical `A_5`
points, basis-sign and associator normal
forms, the Python-semantics certificate of `cd_sign`, the Stiefel witness
and the terminal-channel separation) and four that began here. The two
imported trees arrived with their history; `rocq/open/README.md` describes
that tree in the words of its origin, where it sat at `proofs/`. The four
sources that began here are
`GaussianIntegerHom.v` (the homomorphism `(a, b) -> a + b i` from the
Gaussian integers to a commutative ring with a square root of -1),
`MatrixLeftInverseCertificate.v` (a matrix `L` with `L M = d I` makes the
columns of `M` independent over every ring where the image of `d` is a
nonzero divisor), and two files generated in gororoba-quantum for the
`A_5` program: `CdTowerG2Derivations.v` (14 derivations of the sedenions
as Gaussian-integer tables, linearly independent over every ring that
receives the Gaussian integers) and `A5W8ArcMatrixRanks.v` (independent
columns of eight 24 x 6 matrices over every such ring where the scalar of
the certificate maps to a nonzero divisor).

## Toolchain

- Lean: the release `lean/lean-toolchain` names, installed through
  [elan](https://github.com/leanprover/elan) (`elan` reads the file and
  fetches the release on first use).
- Mathlib: the tag `lean/lakefile.toml` names, resolved to the commits of
  `lean/lake-manifest.json`.
- `shellcheck`, `ruff` and `actionlint` for the gate's lint of shell scripts,
  Python files and workflows.
- Rocq: opam with the switch `sh ci/install_rocq.sh` builds (OCaml 5.5.1,
  rocq-core 9.3.0, rocq-stdlib 9.2.0, Flocq, MathComp, Hierarchy Builder,
  Elpi, Equations, ExtLib), `make`, and `rustc` for the admission scanner.

```sh
cd lean
lake exe cache get   # prebuilt Mathlib, about 7 GB with the sources
lake build
```

With the prebuilt Mathlib present and no library object built, `lake build
GororobaMath` took 29 s and its largest process peaked at 3.0 GB of resident
memory (`/usr/bin/time -f '%es %MkB'` at commit d47b053 on a 12-thread
x86-64 workstation, Lean 4.35.0, Mathlib v4.35.0). The first `lake build`
after `lake exe cache get` took 161 s. A file that imports Mathlib outside
the module system peaks at 6.8 GB, against 3.8 GB as `module` with `public
import Mathlib`.

## Checks

```sh
sh ci/check.sh
```

runs the admission gate: the shell lint, the library build with warnings as
errors, and the axiom audit. `#audit_axioms GororobaMath`
(defined in `lean/AxiomAudit.lean`) fails when any declaration of the library depends
on an axiom other than `propext`, `Classical.choice` and `Quot.sound`, which
excludes `sorry`, `native_decide` and declared axioms. The gate builds and
audits every tracked module under `lean/GororobaMath/`, taken from git's
file list, and separately requires `lean/GororobaMath.lean` to import each
one; it also requires the audit to reject `lean/AuditFixture.lean`, which
holds one of each.

```sh
sh ci/check_rocq.sh
```

runs the Rocq half on an export of `HEAD` outside the checkout: every
tracked source of `rocq/open/theories`, `rocq/open/verified` and
`rocq/quantum` is listed in its `_RocqProject` and compiles (350 and 33
sources), `rocq/open` passes `make all check-schur-geometry check-admissions
check-plugins extract-check`, the build log of `rocq/quantum` holds no
warning, and none of the three directories holds `Admitted` or `admit`. Of
the eleven sources elsewhere under `rocq/open`, those make targets compile
seven and the script compiles `NullityTwelveCoefficientCertificate.v`;
`ExtractFP24Admit.v`, `ExtractR2VBDP4.v` and `RustExtractSpike.v` stay
uncompiled, and the script names all eleven and fails on a twelfth.

The script then re-checks all 383 project-listed modules with Rocq's kernel
checker and compares the axioms it reports with a ledger in each tree.
`rocq/quantum/kernel-assumptions.txt` holds four axioms of the standard
library: functional extensionality, excluded middle and the two axioms of
the classical real numbers. `rocq/open/kernel-assumptions.txt` holds 135:
37 that five modules of the tree declare (`SStructuralGaps`,
`CarlsonIntegrals`, `TightBindingTopology`, `CDFidelity`,
`C958_ZDGraphTopology`), five of the standard library, and 93 primitive
operations and their specifications from Rocq's core library (floats,
63-bit integers, strings). The summary's fourth section stays
unconstrained: it lists the inductive types checked under Rocq's default
rule that an index does not raise the universe of its type (the rule the
`-indices-matter` option turns off), and `Corelib.Init.Logic.eq` is on it
in every development.

```sh
GOROROBA_QUANTUM=../gororoba-quantum sh ci/compare_signs.sh
```

compares `Tower.sign` with `cd_core.cd_sign` on every index pair of levels
3 to 6, and

```sh
GOROROBA_QUANTUM=../gororoba-quantum sh ci/compare_estimator.sh
```

compares `KernelMap.vHat`, `KernelMap.nHat` and `KernelMap.nullity`, evaluated
over the rationals, with `pathion_kernel_map._pair_summary` on twelve fixed
blocks whose bins are all decided. Each prints the gororoba-quantum commit it
read and runs on demand, since it reads another repository; the second also
needs that repository's Python packages.

## License

Apache-2.0, in [LICENSE](LICENSE), for the library and the proof trees. The
package descriptions, the patch and the switch export under `rocq/open/opam`
describe third-party Rocq libraries and carry the license each `opam` entry
names.
