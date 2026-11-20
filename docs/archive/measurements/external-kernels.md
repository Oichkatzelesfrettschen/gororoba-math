# External kernels for the Lean library

Measured 2026-11-20 on the Windows compute workstation (WSL, 32 threads, 54 GB), Lean 4.35.0, gororoba-math at b00bb43 (the head of pull request 89).

## Tools

| Tool | Revision | Role |
|---|---|---|
| lean4export | tag v4.35.0, NDJSON format 3.1.0 | writes named declarations and their dependency closure |
| nanoda_lib | commit 0da9f98feadd3a0a2ef4b3dbcf52a298a6fef929 (2026-11-07) | type checker for Lean, written independently in Rust |
| lean4lean | master 67f63b0 (toolchain v4.33.0-rc2) | kernel reimplemented in Lean; its README notes that it derives from the C++ kernel and likely shares some of its bugs |

The nanoda release v0.3.2 rejects the configuration key `stack_size_bytes` that its current README documents. Its help text names an older lean4export fork as the export format, so the pin is the master commit above. lean4lean builds on 4.33.1. On 4.35.0 it fails twice:
- `Lean.reduceBool` and `Lean.reduceNat` no longer exist in core. lean4lean names them only to refuse native reduction, and a name comparison compiles.
- Its check of primitive definitions rejects 4.35's `Nat.div` ("invalid form for primitive def Nat.div"). Changing the accepted forms of a checker's primitives belongs upstream, so lean4lean is not used for the 4.35 library.

## Calibration

The bad inputs are exports of exactly `ReplayFixture.bogus` and its dependencies, a 36-line file. That declaration has type `False` and value `True.intro`, and was added with `debug.skipKernelTC`.

| Input | lean4export | nanoda | lean4lean |
|---|---|---|---|
| 4.35.0 `ReplayFixture.bogus` (36 lines) | ok | rejected: `assertion failed: self.def_eq(u, v)`, status 101 | not built |
| 4.35.0 `Tower.kernel_swap_iff_two_eq_zero`, `Tower.zmod5_not_pure_kernel_swap` (176,017 lines) | ok | accepted | not built |
| 4.33.1 fixture, the same false declaration | ok | rejected, status 101 | rejected: `(kernel) declaration type mismatch` |
| 4.33.1 fixture, a theorem of type `True` | ok | accepted | accepted |

A first calibration on whole-module exports misled. The bad fixture failed in every tool, but nanoda failed on the rejected configuration key and lean4lean on a pretty-printer panic. The good fixture failed in nanoda because `Lean.reduceBool`, exported with all of `Init`, depends on the unpermitted axiom `Lean.trustCompiler`. The check therefore exports only the named theorems and their dependencies. It counts a rejection only as nanoda's type-checker panic, and it treats any other failure as a tool error.

## Run over the headline theorems

All 110 Lean rows of `ci/headline-results.tsv`, grouped into their 34 solution modules, were accepted by nanoda, with only `propext`, `Classical.choice` and `Quot.sound` permitted. The closures ran from 26,034 export lines (`CayleyDickson.Basic`) to 3,207,192 (`CayleyDickson.HalfFold`), and the run took about 10 minutes at 12 checker threads.
