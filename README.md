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
| `GororobaMath.CayleyDickson.Tower` | at every level `k` and over every such ring, `e_p * e_q = sign(p, q) e_(p xor q)` (`Tower.e_mul_e`, `Tower.e_mul_e_sign`), conjugation negates every basis element but `1` (`Tower.star_e`), each of those squares to `-1` (`Tower.e_mul_self`) and two distinct ones anticommute (`Tower.e_mul_e_anticomm`); the sign of `e_p * e_(p xor q)` is that of `e_p * e_q`, reversed for `p != 0` (`Tower.negSign_xor_right`); `Pathion R` is level 5, the 32-dimensional algebra `A_5` | `cd_core.cd_sign`, by the comparison below |
| `GororobaMath.CayleyDickson.TwoTerm` | an aligned pair `{x, x xor i xor j}` gives the zero product `(e_i + e_j)(e_x +- e_x') = 0` at every level over every ring (`Tower.two_term_mul_add_eq_zero`, `Tower.two_term_mul_sub_eq_zero`); `partner` is an involution without a fixed point for `i != j` and alignment is a property of the pair; the aligned-pair counts of the measured operands, evaluated in the kernel: 12 for `e_1 + e_18` and `e_1 + e_24`, 4 for `e_1 + e_26` and `e_2 + e_27`, 0 for `e_1 + e_17` in `A_5`, 4 for `e_1 + e_10` in the sedenions | the nullity reading of gororoba-quantum's `docs/evidence/pathion-kernel-map/README.md`; `TwoTermNullity` proves that the count is the nullity |
| `GororobaMath.CayleyDickson.TowerModule` | every level of the tower over a commutative star ring `R` is an `R`-module with the basis `e_p`, of rank `2^k` (`Tower.basis`, `Tower.finrank_eq`); over a ring with the identity as star, left multiplication is `R`-linear (`Tower.mulLeft`) and acts on coordinates as a signed permutation (`Tower.repr_e_mul`) | the coordinates in which gororoba-quantum's `pathion_kernel_map.py` writes the operator |
| `GororobaMath.CayleyDickson.TwoTermNullity` | over a nontrivial commutative ring with the identity as star in which `2` is a non-zero-divisor, the kernel of left multiplication by `e_i + e_j` is a free module of rank `alignedPairCount k i j` (`Tower.free_ker_mulLeft_e_add_e`, `Tower.finrank_ker_mulLeft_e_add_e`), and the same for `e_i - e_j` with `i != j`; 12 for `e_1 + e_18` in `A_5` over the rationals and over the integers | the nullity that the hardware estimator of `KernelMap.Estimator` targets; no theorem yet links `KernelMap.nullity` to this rank |
| `GororobaMath.CayleyDickson.TwoTermRecursion` | the recursion of `alignedPairCount` on the top index bit, with low parts `a`, `b` of `i`, `j`: twice the level-`k` count of `a`, `b` for `i` and `j` in the same half (`Tower.alignedPairCount_succ_of_msb_eq`), `0` for different halves with `a = 0`, `b = 0` or `a = b` (`Tower.alignedPairCount_succ_eq_zero`), and `N(k+1, i, j) + 2 N(k, a, b) + 4 = 2^k` for different halves otherwise (`Tower.alignedPairCount_succ_add`); hence no aligned pair at levels `k <= 3` or for an operand with the term `e_0` or the unit the last doubling adjoins (index `2^(k-1)` at level `k`), every count a multiple of 4, and a nonzero count at level `k` at most `2^(k-1) - 4` | the counts of the measured operands in `TwoTerm`; over the reals, the same-half case is Theorem 10.1 of Biss, Dugger and Isaksen (arXiv:math/0511691) on sums of two basis vectors; the mixed case matches their Proposition 11.1 and Lemmas 8.7 and 8.8 under an associator-dimension identity that is computed and unproved |
| `GororobaMath.KernelMap.Estimator` | the bias identity of the hardware nullity estimator, `N_hat - N = \|B+\|\|B-\|/\|B\| (Vbar+ - Vbar-)/V_hat` for every observed contrast with `V_hat` nonzero (`nHat_sub_nullity`), and the forced reading `N_hat = \|B\|/2` of a block with no bin of ideal contrast `-1` (`nHat_eq_card_div_two_of_negBins_eq_empty`) | `docs/evidence/pathion-kernel-map/nhat-bias/README.md` in gororoba-quantum, claims 1 and 3 |

The tower theorems hold for every level and every coefficient ring, so they
cover the 64- and 128-dimensional runs as well as `A_5`. The estimator
theorems hold over every field of characteristic zero.

## Rocq trees

`rocq/open` is the proof tree of gororoba-open (351 sources under
`theories/` and `verified/`, with checkpoints, extraction targets and the
frozen quantum-observable evidence its bindings cite). `rocq/quantum` holds
41 sources: the 29 proof files of gororoba-quantum (the Cayley-Dickson
tower over ordered domains and commutative rings with its basis, base change,
order-three map and the kernel certificates of the canonical `A_5`
points, basis-sign and associator normal
forms, the Python-semantics certificate of `cd_sign`, the Stiefel witness
and the terminal-channel separation) and twelve that began here. The two
imported trees arrived with their history; `rocq/open/README.md` describes
that tree in the words of its origin, where it sat at `proofs/`. Nine of
the sources that began here are
`GaussianIntegerHom.v` (the homomorphism `(a, b) -> a + b i` from the
Gaussian integers to a commutative ring with a square root of -1),
`MatrixLeftInverseCertificate.v` (a matrix `L` with `L M = d I` makes the
columns of `M` independent over every ring where the image of `d` is a
nonzero divisor), `MatrixSplittingCertificate.v` (matrices with
`P M + V C = d I` make every solution of `M x = 0`, after multiplication by
the image of `d`, a combination of the columns of `V`),
`CdTowerLeibnizSystem.v` (the Leibniz rule of a linear map on the basis
units of a level of the ring tower as linear forms in its coordinates),
`CdTowerE1E18Kernel.v` (the kernel certificate of `e_1 + e_18` in `A_5`, which no
point of `CdTowerCanonicalKernels.v` is: twelve vectors, twelve functionals
and a table of 32 images with `d = 2`, free of rank 12 where 2 is invertible),
`CdTowerRealKernels.v` (the certificates of the twelve canonical points and of
`e_1 + e_18`, base-changed to the reals and carried through `TowerBridge.v`:
the kernel of left multiplication in `OpenGororoba.cd_tower 5` is free of rank
8, 12 or 16, `left_kernel_free`), and
three files generated in gororoba-quantum for the `A_5` program:
`CdTowerG2Derivations.v` (14 derivations of the sedenions
as Gaussian-integer tables, linearly independent over every ring that
receives the Gaussian integers), `CdTowerG2DerivationSpan.v` (over every
such ring, six times a linear map of the sedenions that satisfies the
Leibniz rule on the basis units is a combination of those 14, and the map
itself is one where the image of 6 is a nonzero divisor) and
`A5W8ArcMatrixRanks.v` (independent
columns of eight 24 x 6 matrices over every such ring where the scalar of
the certificate maps to a nonzero divisor).

Three sources join the two trees, which each define the Cayley-Dickson
tower recursively; `rocq/quantum/_RocqProject` reads `rocq/open/theories`
as `OpenGororoba` for them. `TowerBridge.v` maps the real tower of
`OpenGororoba.RecursiveCDTower` onto the real instance of the tower of
`CdTowerDomain`, with a two-sided inverse, and the map preserves
multiplication (`to_quantum_mul`). `SignBridge.v` proves that the sign
functions of the two trees agree at every level `k`, each under the
bound its spelling needs: the fuel-indexed function of
`rocq/open/theories` for fuel at least `k` (`open_fuel_sign_sigma`), that
of `rocq/open/verified` for fuel above `k` (`verified_fuel_sign_sigma`),
the Boolean sign law for indices below `2^k` (`open_cube_sign_sigma`),
and the Python semantics of `cd_sign` for such indices and fuel at least
`k + 7` (`python_cd_sign_returns_open_sign`). `QuantumChannelFromOpen.v`
derives `observed_means_exclude_common_binary_channel` of `rocq/quantum`,
in its rational and its real form, from the general theorem
`separated_centers_exclude_common_binary_channel` of `rocq/open`; the
other statements of the two terminal-channel files are not rederived.
A fourth source, `CdTowerRealKernels.v`, reads `TowerBridge.v` the same way: `to_quantum` is a
bijection that preserves zero, sums, scalar multiples and products, so the
kernel statements of the certificates (free of rank 8, 12 or 16 over every
commutative ring where the image of `d` is invertible) become statements
about `OpenGororoba.RecursiveCDTower.tower_mul` over the real numbers
(`NAME_open_kernel_free`, for the twelve points of
`CdTowerCanonicalKernels.v` and for `e_1 + e_18`).

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

## Building

```sh
make lean
make rocq
```

build the files as they stand in the checkout, edits included, with GNU
make. `make lean` runs `lake build --wfail` in `lean/`, whose build tree is
`lean/.lake`. `make rocq` copies `rocq/` into `build/rocq` and compiles
`rocq/open` (`make all`) and then `rocq/quantum` there, so the source
directories hold no build product. `make rocq-open` builds the first tree
alone; `make rocq-quantum` is the same as `make rocq`, since `rocq/quantum`
reads the objects of `rocq/open`. `BUILD_DIR` names another build
directory, which lies outside the checkout (any path inside it other than
`build` is refused), `ROCQ_JOBS` the number of parallel compilations and
`ROCQ_SWITCH` the opam switch. `build`, `lean/.lake` and the compiler's
products are ignored by git. The warning options are the option lines of
each tree's `_RocqProject`. `make clean` removes a build tree that
`make rocq` created and no other directory. `make help` lists the targets.

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
`rocq/quantum` is listed in its `_RocqProject` and compiles (351 and 41
sources), `rocq/open` passes `make all check-schur-geometry check-admissions
check-plugins extract-check`, the build log of `rocq/quantum` holds no
warning, and none of the three directories holds `Admitted` or `admit`. Of
the eleven sources elsewhere under `rocq/open`, those make targets compile
seven and the script compiles `NullityTwelveCoefficientCertificate.v`;
`ExtractFP24Admit.v`, `ExtractR2VBDP4.v` and `RustExtractSpike.v` stay
uncompiled, and the script names all eleven and fails on a twelfth.

The script then re-checks all 392 project-listed modules with Rocq's kernel
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
GOROROBA_QUANTUM=../gororoba-quantum ROCQ_BUILD_TREE=build/rocq sh ci/compare_signs.sh
```

compares `Tower.sign` with `cd_core.cd_sign` and with the two Rocq sign
functions of `SignBridge.v` (`CdTowerBasisSign.sigma` and `open_cube_sign`)
on every index pair of levels 3 to 6; `ROCQ_BUILD_TREE` names the `rocq`
directory of a tree that `make rocq` compiled, and `ci/audit/SignTable.v`
prints the two Rocq tables, and

```sh
GOROROBA_QUANTUM=../gororoba-quantum sh ci/compare_estimator.sh
```

compares `KernelMap.vHat`, `KernelMap.nHat` and `KernelMap.nullity`, evaluated
over the rationals, with `pathion_kernel_map._pair_summary` on twelve fixed
blocks whose bins are all decided. Each prints the gororoba-quantum commit it
read and runs on demand, since it reads another repository; the second also
needs that repository's Python packages.

```sh
GOROROBA_QUANTUM=../gororoba-quantum sh ci/check_quantum_sources.sh
```

renders the eight sources of `rocq/quantum` that `ci/quantum-sources/` generates
(the sign semantics and source certificates, the N = 21 target-flip witnesses,
the canonical kernel certificates, the Gaussian-integer certificates of the
G_2 derivation tables, the W8 arc matrices and the derivation span, and the
Stiefel witness) from the records and `cd_core.py` of that checkout, requires
each rendering to equal the tracked file, and requires each generator to reject
a copy of its source with one digit changed (eight copies, one per rendered
source), and runs four more calibrations: a copy of the gororoba-quantum
package whose `cd_core.py` has one changed shift must be rejected by the
generators that read it, the Stiefel package cross-check
(`stiefel_witness_certificate.py --package-cross-check`, python-hypercomplex) must
equal the retained `package_cross_check.json` (reported as skipped when
`hypercomplex` is not installed), six refused writes (an override, `--output`, an
unknown flag, a linked source, a linked `rocq/quantum`, an override naming no
directory) must leave the checkout unchanged, and `make_mutants.py` and
`make_span_mutants.py` must build their mutants from the tracked sources. It
needs python-flint under `PYTHON`; a missing module or tool exits
with status 2, a rendering difference with status 1. A write of a generator
(`--write`, `--generate`) goes only to `rocq/quantum` of this checkout and to the
JSON record beside it; a destination override is honored only with `--check`.

```sh
GOROROBA_QUANTUM=../gororoba-quantum opam exec --switch=rocq-9.3 -- \
  sh ci/replay_quantum_bundles.sh [--ledgers-only] [BUNDLE...]
```

compares, for each retained bundle of `docs/evidence/` in gororoba-quantum, the
`proofs/NAME.v` rows of its ledgers with the files of `rocq/quantum` (the
`proofs/theories/` and `proofs/verified/` rows belong to gororoba-open and are
compared with `GOROROBA_ROOT` when it is set), then runs the bundle's replay and
the `TargetFlipN21` compile and kernel check. `--ledgers-only` stops after the
comparison and needs no Rocq. A `BUNDLE` is one plain path component naming a
bundle; any other word exits with status 2. It runs on demand, since it reads
another repository and compiles for minutes; a bundle that reads a gororoba-open
checkout is skipped unless `GOROROBA_ROOT` names one.

The Rocq half of the span and Gaussian mutation controls has no caller. Nothing in
`ci/check.sh`, `ci/check_rocq.sh` or `ci/check_quantum_sources.sh` runs
`ci/quantum-sources/run_span_checks.sh`, which compiles the three span sources
and `SpanQueries.v`, kernel-checks them, builds the six mutants of
`make_span_mutants.py` and requires each to be rejected in the lemma named for it;
the six mutants of `make_mutants.py` (the Gaussian-integer sources) have no
compile driver. The span checks run by hand, with a build directory outside the
checkout:

```sh
B=$(mktemp -d)
cp rocq/quantum/*.v ci/quantum-sources/SpanQueries.v ci/quantum-sources/make_span_mutants.py "$B"
(cd "$B" && opam exec --switch=rocq-9.3 -- rocq makefile --no-rocq-package-warning -Q . "" -o Makefile.span \
  CdTowerDomain.v CdTowerDomainR.v CdTowerReal.v CdTwistedProduct.v CdTowerRing.v CdTowerRingBasis.v \
  CdTowerRingBaseChange.v GaussianIntegerHom.v MatrixLeftInverseCertificate.v CdTowerG2Derivations.v && \
  opam exec --switch=rocq-9.3 -- make -f Makefile.span)
opam exec --switch=rocq-9.3 -- sh ci/quantum-sources/run_span_checks.sh "$B"
```

`run_span_checks.sh` compiles the span sources itself, takes `$HOME/.opam/rocq-9.3/bin/rocq`,
writes `span-checks-record.txt` in `$B`, ends with one verdict line and exits 0
when every expectation held.
The `make` above runs one job at a time: measured with `-j4`, it stopped on a
missing dependency of `CdTowerDomain` (hypothesis: the generated makefile
lacks an edge for the empty logical root; untraced).

## License

Apache-2.0, in [LICENSE](LICENSE), for the library and the proof trees. The
package descriptions, the patch and the switch export under `rocq/open/opam`
describe third-party Rocq libraries and carry the license each `opam` entry
names.
