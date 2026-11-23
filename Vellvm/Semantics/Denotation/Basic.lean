module

public import Vellvm.Semantics.LLVMEvents
public import Vellvm.Syntax.CFG
public import Vellvm.Syntax.ShowAST

@[expose] public section
namespace Vellvm.Semantics.Denotation
open Interfaces.Params DynamicValues Syntax.LLVMAst

structure fast_mode where
  mk_fast_mode ::
  fast_mode_set : Bool → Unit
  fast_mode_get : Unit → Bool
export fast_mode (mk_fast_mode fast_mode_set fast_mode_get)

def fast_mode_object : fast_mode := ⟨fun _ ↦ (), fun _ ↦ false⟩

def blockaddress_id (f : function_id) (b : block_id) : raw_id :=
  .Name ("blockaddress(@".toUTF8 ++ Syntax.ShowAST.show_raw_id f ++ ", %".toUTF8 ++
    Syntax.ShowAST.show_raw_id b ++ ")".toUTF8)

def indirectbr_target (z : Int) : List (block_id × Option Int) → Option block_id
  | [] => none
  | (b, a) :: rest => if a == some z then some b else indirectbr_target z rest

theorem indirectbr_target_In (z : Int) (brs : List block_id) (addrs : List (Option Int))
    {b : block_id} : indirectbr_target z (brs.zip addrs) = some b → b ∈ brs := by
  induction brs generalizing addrs with
  | nil => simp [indirectbr_target]
  | cons j js ih =>
    cases addrs with
    | nil => simp [indirectbr_target]
    | cons a as =>
      simp only [List.zip_cons_cons, indirectbr_target]
      split
      · rintro ⟨⟩; exact .head _
      · exact fun h ↦ .tail _ (ih as h)

def NONE [Params] : dvalue := .DVALUE_Base .DVALUE_None

end Vellvm.Semantics.Denotation
