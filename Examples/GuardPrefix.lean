import Vellvm.Tree.Execution

open ITree (Effect)
open Vellvm.Tree

namespace GuardPrefix

abbrev EmptyE : Effect := ⟨Empty, fun _ ↦ Empty⟩

def loop : Producer EmptyE EmptyE Nat := ⟨Nat, 0, fun n ↦ .guard (n + 1)⟩

def cursor : Producer EmptyE EmptyE Nat := loop.translate (fun e ↦ ⟨e, id⟩)

def guards (p : Producer EmptyE EmptyE Nat) (s : p.S) : Nat → Option p.S
  | 0 => some s
  | n + 1 => match p.next s with | .guard j => guards p j n | _ => none

theorem every_prefix (s count : Nat) : guards cursor s count = some (s + count) := by
  induction count generalizing s with
  | zero => rfl
  | succ n ih =>
    exact (ih (s + 1)).trans (congrArg some (show s + 1 + n = s + (n + 1) by omega))

end GuardPrefix

def main : IO Unit := do
  let state : Option Nat := GuardPrefix.guards GuardPrefix.cursor GuardPrefix.cursor.initial 32
  unless state == some 32 do throw <| IO.userError "guard cycle failed to resume"
  IO.println s!"32 guards; resumable state: {state}"
