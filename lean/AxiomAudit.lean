/- SPDX-License-Identifier: Apache-2.0 -/
import Lean

/-!
# Axiom audit by module

`#audit_axioms Root` collects the axioms of every declaration that an
imported module named `Root` or `Root.*` defines and fails when one lies
outside the allow list `propext`, `Classical.choice`, `Quot.sound`. A proof
that holds `sorry` depends on `sorryAx`, one closed by `native_decide` on an
axiom that tactic declares for the proof (measured under Lean 4.35.0), and a
declared `axiom` on itself, so each fails the audit. The audit selects by defining module, since the library declares its
results in the namespace of their subject (`CayleyDickson`, `KernelMap`).

Output: one line `axiom audit: Root: N declarations, M outside the allow
list`, then one line per offending declaration with its axioms. A root that
matches no declaration fails, so a misspelled root cannot pass.
-/

open Lean Elab Command

/-- The axioms a library declaration may depend on. -/
def AxiomAudit.allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

/-- `#audit_axioms Root` fails unless every declaration of the imported
modules under `Root` depends only on the allowed axioms. -/
elab "#audit_axioms " root:ident : command => do
  let env ← getEnv
  let rootName := root.getId
  let moduleNames := env.header.moduleNames
  let names := env.constants.map₁.fold (init := #[]) fun acc name _ =>
    match env.getModuleIdxFor? name with
    | some idx =>
      if rootName.isPrefixOf moduleNames[idx.toNat]! then acc.push name else acc
    | none => acc
  let mut offending : Array (Name × Array Name) := #[]
  for name in names do
    let axioms ← liftCoreM (collectAxioms name)
    let extra := axioms.filter fun a => !AxiomAudit.allowed.contains a
    unless extra.isEmpty do
      offending := offending.push (name, extra)
  let sorted := offending.qsort fun a b => a.1.toString < b.1.toString
  let summary :=
    s!"axiom audit: {rootName}: {names.size} declarations, {sorted.size} outside the allow list"
  if names.isEmpty then
    throwError "{summary}\nno imported module is named {rootName} or {rootName}.*"
  if sorted.isEmpty then
    logInfo summary
  else
    let lines := sorted.map fun (name, extra) => s!"  {name}: {extra.toList}"
    throwError "{summary}\n{String.intercalate "\n" lines.toList}"
