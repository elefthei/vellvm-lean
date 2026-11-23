import Lean

open Lean Elab Command

namespace PortChecks

/-- Each source key names exactly one independent type. The kernel compares it with the un-applied
constant: elaborating only `(@target : expected)` could silently specialize the target. -/
elab "#source_check " key:str target:ident " : " expected:term : command => do
  let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo target
  let typeName := Name.str `PortChecks.Expected key.getString
  let typeId := mkIdentFrom key <| Name.str `_root_.PortChecks.Expected key.getString
  elabCommand (← `(abbrev $typeId:ident := $expected))
  let actual ← getConstInfo name
  let contract ← getConstInfo typeName
  let levels := actual.levelParams.map Level.param
  unless contract.levelParams.length == levels.length do
    throwErrorAt target "{name}: universe arity differs from source key {key}"
  let some body := contract.value? | throwErrorAt key "missing expected type"
  let type := body.instantiateLevelParams contract.levelParams levels
  let env ← getEnv
  unless Kernel.isDefEqGuarded env {} actual.type type do
    throwErrorAt target "{name}: type differs from source key {key}\nactual: {actual.type}\nexpected: {type}"
  let checkedId := mkIdentFrom key <| Name.str `_root_.PortChecks.Checked key.getString
  if ← liftTermElabM <| Meta.isProp actual.type then
    elabCommand (← `(theorem $checkedId:ident : $expected := @$target))
  else
    elabCommand (← `(noncomputable abbrev $checkedId:ident : $expected := @$target))

end PortChecks
