import PortChecks.SourceType
import Vellvm.Semantics.LLVMEvents

open ITree (Effect)
open Vellvm.Semantics.LLVMEvents Vellvm.Semantics.DynamicValues Vellvm.Semantics.Interfaces.Params
open Vellvm.Tree
open CTree (CTree)

#source_check "src/rocq/Semantics/LLVMEvents.v|Vellvm.Semantics.LLVMEvents|ThrowUB"
  ThrowUB : Unit → UBERequest

#source_check "src/rocq/Semantics/LLVMEvents.v|Vellvm.Semantics.LLVMEvents|withCall"
  withCall : ∀ [Pa : Params] {X : Type}, MCFGtop X → CFGtop X

namespace PortChecks.LLVMEvents
variable [Pa : Params]

private abbrev ub : MCFGEbot.I := .inr (.inr (.inr (.inl (ThrowUB ()))))
private abbrev oom : MCFGEbot.I := .inr (.inl (ThrowOOM ()))
private abbrev failure : MCFGEbot.I := .inr (.inr (.inr (.inr (.inr (Throw ())))))
private abbrev stop (e : MCFGEbot.I) (k : MCFGEbot.O e → MCFGbot Unit) := CTree.vis e k

example : ¬eutt Eq (stop ub nofun) (stop failure nofun) :=
  eutt_vis_ne ub failure (by intro h; cases h) _ _ _

private abbrev cuts : Comparison MCFGEbot MCFGEbot Unit Unit :=
  ⟨true, true, (· = ub), (· = oom), Eq, fun _ a _ b ↦ HEq a b, Eq⟩

example : Related cuts (stop ub nofun) (CTree.ret ()) := Related.cut_left _ _ _ rfl
example : Related cuts (CTree.ret ()) (stop oom nofun) := Related.cut_right _ _ _ rfl
example : ¬Related cuts (stop oom nofun) (CTree.ret ()) :=
  fun h ↦ by cases (related_vis_ret_iff (p := cuts) oom nofun ()).mp h
example : ¬Related cuts (CTree.ret ()) (stop ub nofun) :=
  fun h ↦ by cases (related_ret_vis_iff (p := cuts) () ub nofun).mp h

end PortChecks.LLVMEvents
