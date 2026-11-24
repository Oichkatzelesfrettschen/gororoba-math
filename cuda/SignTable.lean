/- SPDX-License-Identifier: Apache-2.0 -/
import Cuda

/-!
The Cayley-Dickson sign table of one level, computed on a CUDA device.

`negSign` mirrors `CayleyDickson.Tower.negSign` of `lean/GororobaMath/CayleyDickson/Tower.lean`
on machine words: an index of level `k` is the low `k` bits of a `UInt32`, its top bit selects the
half of the outermost double, and the remaining bits index the level below. The recursion of
`Tower.negSign` is a tail call in three cases and a flip of its result in the fourth, which
`negSignFrom` carries as a flag. One device thread
evaluates one pair `(p, q)`, and the host evaluates the same definition on every pair and counts
the entries that differ.

`sign-table LEVEL` writes `2 ^ LEVEL` lines of `2 ^ LEVEL` space-separated entries `1` or `-1`
from the device, the format of `lean/audit/SignTable.lean`; `ci/compare_cuda_signs.sh` compares
that output with the table of `Tower.sign`. Exit status: 0 device and host agree, 3 they differ,
2 a usage error, 1 an uncaught CUDA error.
-/

/-- One level of `Tower.negSign` per call, outermost double first, on machine words: the four
top-bit cases either pass the low bits down unchanged, swap them, flip the gathered sign when the
right index has a nonzero low part, or end at `true` flipped by the gathered sign. Every recursive
call is a tail call over machine words, and `fuel` bounds the recursion at the 32 bits of an index. -/
@[cuda_device]
def negSignFrom : Nat → UInt32 → UInt32 → UInt32 → Bool → Bool
  | 0, _, _, _, neg => neg
  | fuel + 1, level, p, q, neg =>
    if level == 0 then neg
    else
      let level := level - 1
      let top : UInt32 := 1 <<< level
      let pl := p &&& (top - 1)
      let ql := q &&& (top - 1)
      if p &&& top == 0 then
        if q &&& top == 0 then negSignFrom fuel level pl ql neg
        else negSignFrom fuel level ql pl neg
      else if q &&& top == 0 then negSignFrom fuel level pl ql (xor neg (ql != 0))
      else if ql == 0 then !neg
      else negSignFrom fuel level ql pl neg

/-- `true` when `e k p * e k q = -e k (p ^^^ q)`, `CayleyDickson.Tower.negSign` on machine words. -/
@[cuda_device]
def negSign (k p q : UInt32) : Bool := negSignFrom 32 k p q false

structure TableParams where
  level : UInt32
  deriving Cuda.POD

/-- Thread `t` writes `1` at `out[t]` when the pair `p = t >>> level`, `q = t &&& (2 ^ level - 1)`
has a negative sign and `0` otherwise. -/
@[cuda_kernel]
def signTable (params : TableParams) (out : Cuda.DeviceSlice UInt32) : Cuda.DeviceM Unit := do
  let t := (← Cuda.blockIdxX) * (← Cuda.blockDimX) + (← Cuda.threadIdxX)
  if t.toUSize < out.size then
    let p := t >>> params.level
    let q := t &&& ((1 <<< params.level) - 1)
    Cuda.storeUInt32 out.ptr t.toUSize (if negSign params.level p q then 1 else 0)

def word (b : ByteArray) (i : Nat) : UInt32 :=
  (b.get! (4 * i)).toUInt32 ||| ((b.get! (4 * i + 1)).toUInt32 <<< 8) |||
    ((b.get! (4 * i + 2)).toUInt32 <<< 16) ||| ((b.get! (4 * i + 3)).toUInt32 <<< 24)

def run (k : Nat) : IO UInt32 := do
  let size := 2 ^ k
  let pairs := size * size
  let stream ← Cuda.Stream.default
  let out ← Cuda.Buffer.alloc UInt32 pairs.toUSize
  out.copyFrom (ByteArray.mk (Array.replicate (4 * pairs) 0xff)) stream
  -- A device thread allocates in its block's bump arena while it evaluates `negSign`, and
  -- `forElements` sets that arena to zero bytes. Measured on compute capability 8.9: a block of 256
  -- threads needs between 8 and 16 KiB at level 4 and between 16 and 64 KiB at level 10; a launch
  -- whose arena runs out ends in `unspecified launch failure`.
  let config := { (Cuda.LaunchConfig.forElements pairs.toUSize) with blockArenaBytes := (131072 : USize) }
  let handle ← signTable.launchOn stream config { level := k.toUInt32 } out
  handle.waitChecked "signTable"
  let table ← out.copyTo stream
  let stdout ← IO.getStdout
  let mut bad := 0
  for p in [0:size] do
    let mut row := ""
    for q in [0:size] do
      let device := word table (p * size + q)
      let host : UInt32 := if negSign k.toUInt32 p.toUInt32 q.toUInt32 then 1 else 0
      if device != host then bad := bad + 1
      row := row ++ (if q == 0 then "" else " ") ++ (if device == 1 then "-1" else if device == 0 then "1" else "?")
    stdout.putStrLn row
  IO.eprintln s!"sign-table: level {k}, {pairs} pairs, {bad} differ between device and host"
  return (if bad == 0 && table.size == 4 * pairs then 0 else 3)

def main (args : List String) : IO UInt32 := do
  match args with
  | [arg] =>
    match arg.toNat? with
    | some k =>
      if 1 ≤ k ∧ k ≤ 10 then run k
      else
        IO.eprintln s!"sign-table: level {k} is outside 1 to 10"
        return 2
    | none =>
      IO.eprintln s!"sign-table: level {arg} is not a natural number"
      return 2
  | _ =>
    IO.eprintln "usage: sign-table LEVEL"
    return 2
