/- SPDX-License-Identifier: Apache-2.0 -/
import Lake
open Lake DSL System

package gororobaCuda

/-- `-Karch=sm_NN` selects the device architecture; `-KcudaLib=DIR` names the
directory that holds `libcudart.so`. -/
def cudaArch : String := (get_config? arch).getD "sm_89"
def cudaLibDir : String := (get_config? cudaLib).getD "/opt/cuda/lib64"

/- The CUDA unit is emitted with the module's own setup file so that its
launch symbols carry the package prefix the module's C output links against.
`-fno-exceptions` keeps the g++-compiled CUDA objects free of the
`DW.ref.__gxx_personality_v0` COMDAT group. Lake localizes hidden symbols in
those objects, and with that group present the native link fails on the
reference from `libleancpp.a` (measured with nightly-2026-11-21 and GCC 15
and 16). -/
def cudaCfg (pkg : Package) : CudaBuildConfig where
  architecture := cudaArch
  nvccArgs := #["-Xcompiler=-fno-exceptions"]
  leanArgs := #["--setup", (pkg.irDir / "SignTable.setup.json").toString]

lean_lib SignTable

target signTableCudaO pkg : FilePath := do
  let some mod ← findModule? `SignTable | error "module SignTable is not in the workspace"
  let src := (← mod.olean.fetch).map fun _ => pkg.dir / "SignTable.lean"
  buildLeanCudaO (pkg.buildDir / "cuda" / "SignTable.cu.o") (pkg.buildDir / "cuda" / "SignTable.cu") src
    (cudaCfg pkg)

target cudaLink pkg : CudaDeviceLinkArtifacts := do
  buildCudaDeviceLink (pkg.buildDir / "cuda" / "dlink.o") (pkg.buildDir / "cuda" / "runtime.o")
    #[← signTableCudaO.fetch] (cudaCfg pkg)

target cudaRuntimeO : FilePath := do
  return (← cudaLink.fetch).map (·.runtimeObject)

target cudaDlinkO : FilePath := do
  return (← cudaLink.fetch).map (·.deviceLinkObject)

@[default_target]
lean_exe «sign-table» where
  root := `SignTable
  moreLinkObjs := #[signTableCudaO, cudaRuntimeO, cudaDlinkO]
  moreLinkArgs := #[s!"-L{cudaLibDir}", s!"-Wl,-rpath,{cudaLibDir}", "-lcudart"]
