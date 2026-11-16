/- SPDX-License-Identifier: Apache-2.0 -/
module

public import Challenge.AlignedPairClosedForm
public import Challenge.AlignedPairSpectrum
public import Challenge.AnnihilatorSymmetry
public import Challenge.AssociatorSpace
public import Challenge.NonAssociative
public import Challenge.TwoTermBins
public import Challenge.TwoTermNullity
public import Challenge.TwoTermRecursion

/-!
# Challenge modules

This file imports the challenge modules that one environment can hold together. `Challenge.Basic`,
`Challenge.Tower`, `Challenge.TowerModule`, `Challenge.TwoTerm` and `Challenge.Estimator` restate
definitions that library modules, which the modules above import, also declare, so a file that imports them
beside those reports a duplicate declaration. The `Challenge.*` glob of `lakefile.toml` builds each of
them on its own, and `lake comparator --config Challenge/NAME.json` names each one.
-/
