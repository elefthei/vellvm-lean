import Lean

open Lean

namespace ProofAudit

private def fail {α} (msg : String) : IO α := throw <| IO.userError msg

private def requireInfo (env : Environment) (name : Name) : IO ConstantInfo :=
  match env.find? name with
  | some info => pure info
  | none => fail s!"missing declaration: {name}"

private def checkType (env : Environment) (key : String) (target : ConstantInfo) : IO Unit := do
  let spec ← requireInfo env (.str `PortChecks.Expected key)
  let witness ← requireInfo env (.str `PortChecks.Checked key)
  let some type := spec.value? | fail s!"{key}: missing expected type"
  let some (.const witnessName levels) := witness.value? (allowOpaque := true)
    | fail s!"{key}: check must ascribe the unapplied target"
  unless witnessName == target.name && levels == witness.levelParams.map Level.param do
    fail s!"{key}: expected unspecialized {target.name}, found {witnessName} at {levels}"
  unless spec.levelParams.length == target.levelParams.length &&
      Kernel.isDefEqGuarded env {} target.type
        (type.instantiateLevelParams spec.levelParams (target.levelParams.map Level.param)) do
    fail s!"{key}: independent expected type differs from {target.name}"

private def readRows (path : System.FilePath) (header : List String) : IO (List (List String)) := do
  let lines := (← IO.FS.readFile path).splitOn "\n"
  unless lines.head? == some (String.intercalate "\t" header) do fail s!"{path}: invalid header"
  let rows := (lines.drop 1 |>.dropLast).map (·.splitOn "\t")
  unless lines.getLast? == some "" && !rows.isEmpty && rows.all (·.length == header.length) do
    fail s!"{path}: empty or malformed inventory"
  return rows

private def forbidden (n : Name) : Bool :=
  [`ITree.ITree, `ITree.ITreeF, `CTree.embed, `CTree.embed', `Paco].any (·.isPrefixOf n)

def checkAxioms (env : Environment) (n : Name) : IO Unit := do
  let _ ← requireInfo env n
  let axs ← (collectAxioms (m := CoreM) n).toIO' { fileName := "proof-audit", fileMap := default }
    { env }
  let bad := axs.filter fun ax => ![``propext, ``Classical.choice, ``Quot.sound].contains ax
  unless bad.isEmpty do fail s!"{n}: forbidden axioms: {bad}"

/-- Audit compiled private module data, not a handpicked list of final theorems. -/
def audit (env : Environment) (port : System.FilePath) : IO Unit := do
  let mods ← readRows (port / "modules.tsv") ["source", "formal_blob", "oracle_blob", "role", "target"]
  let mut modules : Std.HashMap String Name := {}
  for row in mods do
    let [file, _, _, role, target] := row | fail "bad module row"
    if role == "extraction" then continue
    let mod := target.toName
    unless role == "module" && !modules.contains file && env.header.moduleNames.contains mod do
      fail s!"{file}: duplicate, invalid or missing module: {target}"
    let checker := mod.replacePrefix `Vellvm `PortChecks
    unless env.header.moduleNames.contains checker do fail s!"missing checking module: {checker}"
    modules := modules.insert file mod
  unless modules.size == 85 do fail s!"expected 85 formal modules; found {modules.size}"
  let rows ← readRows (port / "declarations.tsv") ["source", "module", "declaration", "kind", "role",
    "start_byte", "end_byte", "name_start_byte", "name_end_byte", "lean_target", "rocq_sort", "rocq_type"]
  let mut keys : Std.HashSet String := {}
  let mut proofs := 0
  for row in rows do
    let [file, scope, decl, _, role, _, _, _, _, target, _, _] := row | fail "bad declaration row"
    let key := String.intercalate "|" [file, scope, decl]
    if keys.contains key then fail s!"duplicate source key: {key}"
    keys := keys.insert key
    let some mod := modules[file]? | fail s!"unknown source: {key}"
    let n := target.toName
    if role == "module" then
      unless env.contains n || env.isNamespace n do
        fail s!"{key}: missing target namespace {n}"
      continue
    -- Rocq constructors and projections are module-level; Lean's `export` exposes that spelling
    -- without duplicating their declarations outside the enclosing inductive/structure namespace.
    let n ← if env.contains n || !["constructor", "field"].contains role then pure n
      else match getAliases env n false with
        | [canonical] => pure canonical
        | _ => fail s!"{key}: missing or ambiguous constructor/field {n}"
    let info ← requireInfo env n
    let some idx := env.getModuleIdxFor? n | fail s!"{n}: unknown provenance"
    unless mod.isPrefixOf env.header.moduleNames[idx.toNat]! do
      fail s!"{n}: expected in {mod} or one of its implementation submodules"
    let required := role == "proof" || role == "instance"
    if required then
      unless info.hasValue (allowOpaque := true) && !env.isProjectionFn n do
        fail s!"{key}: expected a proved result or concrete instance, not {n}"
      proofs := proofs + 1
    if required || env.contains (.str `PortChecks.Expected key) then checkType env key info
  unless keys.size == 5195 && proofs == 2322 do
    fail s!"incomplete frozen inventory: {keys.size}/5195 globals, {proofs}/2322 proof and instance keys"
  for n in [`Vellvm.Semantics.interp_mcfg_is_resolution, `Vellvm.Semantics.interpreter_param_is_resolution,
      `Vellvm.Semantics.TopLevel.interpreter_cursor_adequate, `Vellvm.Semantics.TopLevel.instrumentation_erasure] do
    let info ← requireInfo env n
    unless info.isTheorem do fail s!"{n}: expected a proved semantic result"
  let mut audited := 0
  for (mod, data) in env.header.moduleNames.zip env.header.moduleData do
    unless Name.isPrefixOf `Vellvm mod || Name.isPrefixOf `PortChecks mod do continue
    for imp in data.imports do
      if imp.module == `CTree.Interp.ITree || (Name.isPrefixOf `ITree imp.module &&
          ![`ITree.Effect, `ITree.InterpM].contains imp.module) then
        fail s!"{mod}: forbidden direct import {imp.module}"
    for n in data.constNames do
      let info ← requireInfo env n
      if let .str p key := n then
        if (p == `PortChecks.Expected || p == `PortChecks.Checked) && !keys.contains key then
          fail s!"{n}: unknown source key"
      if Name.isPrefixOf `Vellvm mod then
        for dep in info.getUsedConstantsAsSet do
          if forbidden dep then fail s!"{n}: forbidden dependency {dep}"
        -- Lean implements each inductive's ctorIdx via getObjTagNat; it is not a source override.
        let generatedTag := fun (base impl : Name) ↦
          (isCtorIdxCore? env base).isSome && impl == .str base "_impl" &&
          Compiler.getImplementedBy? env base == some impl
        if let some impl := Compiler.getImplementedBy? env n then
          unless generatedTag n impl do fail s!"{n}: unverified implementation override {impl}"
        if info.isUnsafe && !generatedTag n.getPrefix n then
          fail s!"{n}: unsafe declaration in the formal library"
      -- Includes helper lemmas, opaque proofs, generated declarations and instances.
      checkAxioms env n
      audited := audited + 1
  IO.println s!"{modules.size} modules; {keys.size} source keys; {proofs} required type checks; {audited} declarations audited"

end ProofAudit

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let env ← importModules #[{ module := `PortChecks }] {} (level := .private) (loadExts := true)
  ProofAudit.audit env "port"
