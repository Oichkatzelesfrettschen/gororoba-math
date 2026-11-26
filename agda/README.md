# Agda pilot: the unit-norm octonions as a Moufang loop

This directory is an Agda library, `gororoba-math` (`gororoba-math.agda-lib`),
that type-checks on its own and outside both admission gates. It holds one
result, that the unit-norm octonions over every commutative ring form a Moufang
loop in the sense of agda-stdlib, and the two modules it rests on.
`ci/check_agda.sh` type-checks it on demand. Neither `ci/check.sh` nor
`ci/check_rocq.sh` reads this directory, and the claims ledger cites none of
its declarations.

## Convention

`GororobaMath.CayleyDickson.Doubling` builds level `k + 1` from pairs of level-`k`
elements with

    (a , b) (c , d) = (a c - conj d b , d a + b conj c),    conj (a , b) = (conj a , - b),

the product and star of `lean/GororobaMath/CayleyDickson/Tower.lean`
(`CayleyDickson.Tower.mk_mul_mk`, `CayleyDickson.Tower.star_mk`). Over a commutative
ring `R` whose star is the identity, level 3 is the octonion algebra `Tower R 3`
of that file. Coordinate `p` of `flatten` is the basis index `p` of `Tower.e`,
with the top bit selecting the second half of the outermost double. The trace form
`N x` is the sum of the squares of the eight coordinates, `Tower.dot 3 x x` of
`lean/GororobaMath/CayleyDickson/AnnihilatorSymmetry.lean`.

## The result

`GororobaMath.CayleyDickson.OctonionMoufangLoop` is parametrised by a
`CommutativeRing` bundle `R` of agda-stdlib. Its carrier `Unit` is the set of
octonions `x` with `N x ≈ 1#`. The operations are the product, the left
division `conj x · y`, the right division `y · conj x` and the unit `one`.
Equality is the coordinatewise setoid equality of `R`.

- `N-mul`: `N (x · y) ≈ N x * N y`, the eight-square identity.
- `isMoufangLoop`, `moufangLoop`: `IsMoufangLoop` of agda-stdlib
  (`Algebra.Structures`). It packages a quasigroup with both division laws, a
  two-sided unit, the left and right Bol laws and the law `Identical`.
- `moufang-left`, `moufang-right`, `moufang-middle`: the identities in the form
  of claim C-578 of gororoba-open, for units:
  `a (x (a y)) = ((a x) a) y`, `((x a) y) a = x (a (y a))` and
  `(a x) (y a) = (a (x y)) a`. The proofs read them off the structure
  through `Algebra.Properties.MoufangLoop`.
- `solution-left`, `solution-right`: `a x = b` forces `x = a \\ b`, and
  `y a = b` forces `y = b // a` (`Algebra.Properties.Quasigroup`).
- `associator-e₁e₂e₄`, `not-associative`: `(e₁ e₂) e₄ = e₇` and
  `e₁ (e₂ e₄) = - e₇`, so coordinate 7 of the associator is `1# + 1#`. If the
  loop associates, then `1# + 1# ≈ 0#`.

Each octonion identity is a polynomial identity over every commutative ring, and
it is checked coordinate by coordinate. The raw operations run on
integer-coefficient ring expressions, and the type checker normalises the
difference of the two sides to the zero polynomial.
`GororobaMath.Solver.IntegerCoefficients` proves the step from that normal form to
the equation in `R`. It supplies the homomorphism from the integers to `R` that the Horner
normal form of agda-stdlib (`Tactic.RingSolver.Core`) needs. agda-stdlib's
reflective `solve-∀` keeps its coefficients in the carrier, so over an abstract
ring it cannot cancel: `x + y - y ≈ x` fails there (measured).

## Partners and what stays open against C-578

- Lean: `CayleyDickson.Tower.moufang_left_three`, `moufang_middle_three` and
  `moufang_right_three` (`lean/GororobaMath/CayleyDickson/Alternative.lean`) state the
  three identities for all octonions. `CayleyDickson.Tower.dot_mul_self_of_le_three`
  (`NormMultiplicative.lean`) states the norm law. The Rocq trees here state no
  Moufang identity, and no source here packages the units as a loop. Mathlib v4.35.0
  and MathComp 2.6.0 define no quasigroup, loop or Moufang loop (source search of
  both trees).
- Open: the nucleus is not stated. The carrier is a setoid over an arbitrary
  commutative ring, and agda-stdlib has no real numbers, so the real sphere S^7 is
  the instance at the reals and is not built here. Non-associativity is stated as
  `(∀ u v w → (u ∙ v) ∙ w ≈₁ u ∙ (v ∙ w)) → 1# + 1# ≈ 0#`.
- Residual risk: no comparison under `ci/` binds `Doubling.agda` to `Tower.lean`.
  The convention above is read from both sources, and an independent evaluation
  of the formula agreed on `(e₁ e₂) e₄ = e₇` and on the left Bol identity at
  random integer points. That evaluation was a session check and is not retained.

## Pins and running the check

| Item | Pin |
|---|---|
| Agda | 2.8.0.2, the release binary `Agda-v2.8.0.2-linux.tar.xz` (sha256 `2bcf24bb561b1be859bba841e5d67962d1616b3251bc147f878e4f60a2fbd9f7`), statically linked |
| agda-stdlib | v2.4, commit `2a5a0dec0a3cb5c87468ce101388a513d39dbf10` (its changelog: tested with Agda 2.8.0) |
| Options | `--safe --without-K` in every source, `-Werror` on the command line |

    AGDA=PATH/TO/agda AGDA_STDLIB=PATH/TO/agda-stdlib-2.4 sh ci/check_agda.sh

The script fails unless the library type-checks and two planted copies fail. The
first copy appends `planted/associativity.agda-fragment`, a claim that the
product associates; it is rejected at that claim because a coordinate
normalises to a nonzero polynomial. The second copy holds a `postulate`, which
`--safe` refuses.

Measured on a 32-core x86-64 Linux host (WSL2), 2026-11-26, single runs, each
in a scope capped at 16 GiB:

| Run | Wall time | Peak memory |
|---|---|---|
| Release binary download and unpack | 1 s | - |
| Root module, agda-stdlib interfaces already built | 154.5 s (root module 151.4 s) | 0.70 GB |
| Root module with agda-stdlib cold (162 interface files, 33 MB) | 191.6 s | 1.18 GB |
| `ci/check_agda.sh` on an export of the commit (library and both planted copies) | 309.6 s | 0.68 GB |

Disk: 55 MB binary, 1 MB of primitive modules unpacked into the user data
directory, 14 MB agda-stdlib checkout, 33 MB of its interface files.
