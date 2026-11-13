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

## Toolchain

- Lean: the release `lean/lean-toolchain` names, installed through
  [elan](https://github.com/leanprover/elan) (`elan` reads the file and
  fetches the release on first use).
- Mathlib: the tag `lean/lakefile.toml` names, resolved to the commits of
  `lean/lake-manifest.json`.
- `shellcheck` for the gate's shell lint.

```sh
cd lean
lake exe cache get   # prebuilt Mathlib, about 7 GB with the sources
lake build
```

The first build of the library took 161 s, and its largest process peaked
at 6.8 GB of resident memory (`/usr/bin/time -f '%es %MkB' lake build` on a
12-thread x86-64 workstation, Lean 4.35.0, Mathlib v4.35.0, with the
prebuilt Mathlib present and the library then one module that imports all
of Mathlib).

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
GOROROBA_QUANTUM=../gororoba-quantum sh ci/compare_signs.sh
```

compares `Tower.sign` with `cd_core.cd_sign` on every index pair of levels
3 to 6 and prints the gororoba-quantum commit it read. It runs on demand,
since it reads another repository.

## License

Apache-2.0, in [LICENSE](LICENSE).
