/- SPDX-License-Identifier: Apache-2.0 -/
import GororobaMath

/-!
Prints the sign table of `CayleyDickson.Tower.sign` at one level:
`lake env lean --run audit/SignTable.lean K` writes `2 ^ K` lines of `2 ^ K`
space-separated entries `1` or `-1`, row `p` and column `q` holding the sign
of `e_p * e_q`. `ci/compare_signs.sh` compares the output with
`cd_core.cd_sign` of a gororoba-quantum checkout.
-/

open CayleyDickson Tower

def signRow (k p : Nat) : String :=
  String.intercalate " " ((List.range (2 ^ k)).map fun q =>
    toString (sign k (BitVec.ofNat k p) (BitVec.ofNat k q)))

def main (args : List String) : IO UInt32 := do
  match args with
  | [arg] =>
    match arg.toNat? with
    | some k =>
      for p in List.range (2 ^ k) do
        IO.println (signRow k p)
      return 0
    | none =>
      IO.eprintln s!"SignTable: level {arg} is not a natural number"
      return 2
  | _ =>
    IO.eprintln "usage: lake env lean --run audit/SignTable.lean LEVEL"
    return 2
