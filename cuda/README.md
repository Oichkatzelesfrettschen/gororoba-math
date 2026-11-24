# Device kernels

`cuda/` is a Lake package of Lean programs whose marked declarations run on an NVIDIA device. It builds with the
toolchain `cuda/lean-toolchain` names, an experimental Lean 4.33.0 compiler with a CUDA backend (Ranvier Labs
nightly of 2026-11-21, binaries only), and stays apart from `lean/`: no module here is a library module, the
admission gate builds none of it, and no proof imports it.

A device result is runtime evidence: one execution on a named device, driver, toolkit and architecture, for the
inputs that run enumerated. A statement reaches the library only through a proof that the kernel of the Lean
release in `lean/lean-toolchain` checks; a table or a witness computed here is a candidate that such a proof
accepts or rejects, and an exact comparison against a library definition accepts it for the enumerated inputs
alone. No record cites a device table as a certificate; a certificate that a proof evaluates follows the evidence
axis of the guide ("Statements and proofs") and is a Rocq artifact.

| Program | Computes | Mirrors | Comparison |
|---|---|---|---|
| `sign-table LEVEL` (`SignTable.lean`) | the sign of `e_p * e_q` for every pair of level 1 to 10, one device thread per pair, each entry also evaluated on the host from the same definition | `CayleyDickson.Tower.negSign` | `ci/compare_cuda_signs.sh` against the table of `Tower.sign`, with a negated-entry control |

## Building and running

`cuda/lean-toolchain` names a toolchain linked into elan by hand, since `elan toolchain install` of this release
channel downloads the archive without comparing it to the channel's checksum file (the project's install page
says so):

| Field | Value |
|---|---|
| Release | `nightly-2026-11-21` of `ranvier-labs/lean4-cuda-nightly`, version `4.33.0-cuda-nightly.20261121.ge8f10c9ff5fe` |
| Archive (x86_64) | `https://github.com/ranvier-labs/lean4-cuda-nightly/releases/download/nightly-2026-11-21/lean-4.33.0-cuda-nightly.20261121.ge8f10c9ff5fe-linux.tar.zst` |
| sha256 | `990269ab74d9620c5809b8c22146d2264778bbb18b0c18713bebaa80458dfb82` |

Check the archive with `sha256sum`, extract it with `tar --zstd -xf`, and register the extracted root with
`elan toolchain link lean4-cuda-nightly-2026-11-21 ROOT`; `lean --features` then prints `CUDA`. The build needs a
CUDA 13 toolkit, and the final link names `libgmp`, `libssl`, `libcrypto` and `libuv`. The Lake tree goes outside
the checkout:

```sh
CUDA_HOME=/opt/cuda CUDA_BUILD_DIR="$HOME/build/gororoba-math-cuda" sh ci/compare_cuda_signs.sh 3 4 5 6
```

`-Karch=sm_NN` selects the device architecture. Measured for this release: the device runtime compiles for
`sm_80` and `sm_89` and fails for `sm_75` in the runtime header, and execution is measured on compute capability
8.9 alone.

## Measured constraints of the backend

Measured with nightly-2026-11-21 on compute capability 8.9 (RTX 4070 Ti, driver 620.70.06, CUDA 13.4).

- A device thread that calls `negSign` allocates in its block's bump arena. `LaunchConfig.forElements` sets that
  arena to zero bytes, and a launch whose arena is missing or runs out ends in
  `CUDA kernel completion: unspecified launch failure`, with no table returned.
- The arena a block of 256 threads needs depends on the form of the function. The tail-recursive form here passes
  with 16 KiB at level 4 (8 KiB fails) and with 64 KiB at level 10 (16 KiB fails). A form of the same function
  written as a `for` loop over a range with four mutable variables passes level 4 only from 256 KiB (128 KiB
  fails) and fails level 10 at 256 KiB. `SignTable.lean` launches with 128 KiB per block, 512 MiB of device memory
  at level 10.
- The device has no individual free, so the arena bounds a block's total allocation. The host evaluation of every
  entry covers the other failure class, a device value that differs.
