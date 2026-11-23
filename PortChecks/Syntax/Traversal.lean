/- Copyright (c) 2026 Vellvm developers. Distributed under the MIT License. -/
import PortChecks.SourceType
import Vellvm.Syntax.Traversal

open Vellvm Vellvm.Syntax.LLVMAst Vellvm.Syntax.CFG Vellvm.Syntax.Traversal ITree

universe u

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_list"
  Endo_list : ∀ {T : Type} [Endo T], Endo (List T)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_option"
  Endo_option : ∀ {T : Type} [Endo T], Endo (Option T)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_prod"
  Endo_prod : ∀ {T U : Type} [Endo T] [Endo U], Endo (T × U)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_ident"
  Endo_ident : ∀ [Endo raw_id], Endo «ident»

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_instr_id"
  Endo_instr_id : ∀ [Endo raw_id], Endo instr_id

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_typ"
  Endo_typ : ∀ [Endo raw_id], Endo typ

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_exp"
  Endo_exp : ∀ {T : Type} [Endo T] [Endo raw_id] [Endo ibinop] [Endo icmp] [Endo fbinop] [Endo fcmp] [Endo IRString], Endo (exp T)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_texp"
  Endo_texp : ∀ {T : Type} [Endo T] [Endo (exp T)], Endo (texp T)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_metadata"
  Endo_metadata : ∀ {T : Type} [Endo T] [Endo raw_id] [Endo ibinop] [Endo icmp] [Endo fbinop] [Endo fcmp] [Endo IRString], Endo (metadata T)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_tint_literal"
  Endo_tint_literal : Endo tint_literal

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_clause"
  Endo_clause : ∀ {T : Type} [Endo T] [Endo (exp T)], Endo (@landingpad_clause T)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_operand"
  Endo_operand : ∀ {T : Type} [Endo T] [Endo (exp T)] [Endo (metadata T)], Endo (@operand T)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_operand_bundle"
  Endo_operand_bundle : ∀ {T : Type} [Endo T] [Endo (exp T)] [Endo (metadata T)] [Endo IRString], Endo (@operand_bundle T)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_instr"
  Endo_instr : ∀ {T : Type} [Endo T] [Endo (exp T)] [Endo (metadata T)] [Endo raw_id] [Endo IRString] [Endo param_attr] [Endo (annotation T)], Endo (instr T)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_terminator"
  Endo_terminator : ∀ {T : Type} [Endo T] [Endo (exp T)] [Endo (metadata T)] [Endo IRString] [Endo raw_id] [Endo param_attr] [Endo (annotation T)], Endo (terminator T)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_phi"
  Endo_phi : ∀ {T : Type} [Endo T] [Endo raw_id] [Endo (exp T)], Endo (phi T)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_block"
  Endo_block : ∀ {T : Type} [Endo raw_id] [Endo (code T)] [Endo (terminator T)] [Endo (phi T)] [Endo (metadata T)], Endo (block T)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_annotation"
  Endo_annotation : ∀ {T : Type} [Endo T] [Endo raw_id] [Endo (exp T)] [Endo (metadata T)], Endo (annotation T)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_global"
  Endo_global : ∀ {T : Type} [Endo raw_id] [Endo T] [Endo Bool] [Endo int_ast] [Endo IRString] [Endo (exp T)] [Endo (metadata T)], Endo («global» T)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_declaration"
  Endo_declaration : ∀ {T : Type} [Endo function_id] [Endo T] [Endo IRString] [Endo int_ast] [Endo param_attr] [Endo fn_attr] [Endo (annotation T)] [Endo (exp T)], Endo (declaration T)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_definition"
  Endo_definition : ∀ {T F : Type} [Endo (declaration T)] [Endo raw_id] [Endo F], Endo (definition T F)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_toplevel_entity"
  Endo_toplevel_entity : ∀ {T F : Type} [Endo F] [Endo T] [Endo («global» T)] [Endo raw_id] [Endo (metadata T)] [Endo (declaration T)] [Endo (definition T F)] [Endo fn_attr] [Endo int_ast] [Endo IRString], Endo (toplevel_entity T F)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_modul"
  Endo_modul : ∀ {T F : Type} [Endo F] [Endo IRString] [Endo T] [Endo («global» T)] [Endo (declaration T)] [Endo fn_attr] [Endo raw_id], Endo (@modul T F)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_cfg"
  Endo_cfg : ∀ {T : Type} [Endo raw_id] [Endo (block T)], Endo (cfg T)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_mcfg"
  Endo_mcfg : ∀ {T F : Type} [Endo T] [Endo F] [Endo IRString] [Endo raw_id] [Endo («global» T)] [Endo (declaration T)] [Endo (definition T F)], Endo (@modul T F)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_of_sum1"
  Endo_of_sum1 : ∀ {A B : ITree.Effect.{u}} {X : Type u} [Endo (RequestAt A X)] [Endo (RequestAt B X)], Endo (RequestAt (A ⊕ₑ B) X)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_itree"
  Endo_itree : ∀ {X : Type u} {E B : ITree.Effect.{u}} [Endo X] [∀ T, Endo (RequestAt E T)], Endo (CTree.CTree E B X)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|Endo_id"
  Endo_id : ∀ (T : Type), Endo T

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_list"
  TFunctor_list : TFunctor List

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_list'"
  TFunctor_list' : ∀ {F : Type → Type} [TFunctor F], TFunctor (fun T ↦ List (F T))

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_option"
  TFunctor_option : ∀ {F : Type → Type} [TFunctor F], TFunctor (fun T ↦ Option (F T))

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_exp"
  TFunctor_exp : ∀ [Endo raw_id] [Endo ibinop] [Endo icmp] [Endo fbinop] [Endo fcmp], TFunctor exp

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_metadata"
  TFunctor_metadata : ∀ [TFunctor exp] [Endo raw_id] [Endo IRString], TFunctor metadata

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_texp"
  TFunctor_texp : ∀ [TFunctor exp], TFunctor texp

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_cmpxchg"
  TFunctor_cmpxchg : ∀ [Endo Bool] [Endo icmp] [Endo int_ast] [Endo IRString] [Endo ordering] [TFunctor texp], TFunctor cmpxchg

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_atomicrmw"
  TFunctor_atomicrmw : ∀ [Endo Bool] [Endo atomic_rmw_operation] [Endo IRString] [Endo ordering] [Endo int_ast] [TFunctor texp], TFunctor atomicrmw

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_landingpad_clause"
  TFunctor_landingpad_clause : ∀ [TFunctor exp], TFunctor (@landingpad_clause)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_operand"
  TFunctor_operand : ∀ [TFunctor exp], TFunctor (@operand)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_operand_bundle"
  TFunctor_operand_bundle : ∀ [TFunctor exp], TFunctor (@operand_bundle)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_instr"
  TFunctor_instr : ∀ [TFunctor exp] [TFunctor annotation], TFunctor instr

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_tident"
  TFunctor_tident : ∀ [Endo «ident»], TFunctor (@tident)

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_terminator"
  TFunctor_terminator : ∀ [Endo tint_literal] [Endo raw_id] [TFunctor exp] [TFunctor annotation], TFunctor terminator

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_phi"
  TFunctor_phi : ∀ [Endo raw_id] [TFunctor exp], TFunctor phi

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_code"
  TFunctor_code : ∀ [Endo raw_id] [TFunctor instr] [TFunctor metadata], TFunctor code

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_block"
  TFunctor_block : ∀ [Endo raw_id] [TFunctor instr] [TFunctor terminator] [TFunctor phi] [TFunctor metadata], TFunctor block

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_annotation"
  TFunctor_annotation : ∀ [TFunctor exp] [Endo raw_id] [TFunctor metadata] [Endo param_attr], TFunctor annotation

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_global"
  TFunctor_global : ∀ [Endo raw_id] [Endo Bool] [Endo int_ast] [TFunctor exp] [TFunctor metadata], TFunctor «global»

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_declaration"
  TFunctor_declaration : ∀ [Endo function_id] [Endo IRString] [Endo int_ast] [Endo param_attr] [Endo linkage] [Endo visibility] [Endo dll_storage] [Endo cconv] [Endo fn_attr] [TFunctor exp] [TFunctor metadata], TFunctor declaration

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_definition"
  TFunctor_definition : ∀ {F : Type → Type} [TFunctor declaration] [Endo raw_id] [TFunctor F], TFunctor (fun T ↦ definition T (F T))

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_toplevel_entity"
  TFunctor_toplevel_entity : ∀ {F : Type → Type} [TFunctor F] [TFunctor «global»] [Endo raw_id] [TFunctor metadata] [TFunctor declaration] [TFunctor (fun T ↦ definition T (F T))] [Endo fn_attr] [Endo int_ast] [Endo IRString], TFunctor (fun T ↦ toplevel_entity T (F T))

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_modul"
  TFunctor_modul : ∀ {F : Type → Type} [TFunctor F] [Endo IRString] [TFunctor «global»] [TFunctor declaration] [Endo raw_id], TFunctor (fun T ↦ @modul T (F T))

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_cfg"
  TFunctor_cfg : ∀ [Endo raw_id] [TFunctor block], TFunctor cfg

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|TFunctor_mcfg"
  TFunctor_mcfg : ∀ {F : Type → Type} [TFunctor F] [Endo IRString] [Endo raw_id] [TFunctor «global»] [TFunctor declaration] [TFunctor (fun T ↦ definition T (F T))], TFunctor (fun T ↦ @modul T (F T))

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|tfmap_list_app"
  tfmap_list_app : ∀ {U V : Type} (r : Endo raw_id) (i : TFunctor instr) (m : TFunctor metadata) (a b : code U) (f : U → V), @tfmap code (@TFunctor_code r i m) U V f (a ++ b) = @tfmap code (@TFunctor_code r i m) U V f a ++ @tfmap code (@TFunctor_code r i m) U V f b

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|swap_endo_raw_id"
  swap_endo_raw_id : raw_id → raw_id → Endo raw_id

#source_check "src/rocq/Syntax/Traversal.v|Vellvm.Syntax.Traversal|subst_cfg_endo_cfg"
  subst_cfg_endo_cfg : ∀ {T : Type}, function_id → cfg T → Endo (definition T (cfg T))

-- Both instruction identifiers and local expression operands use the overridden raw_id traversal.
example : (swap_code (.Anon 1) (.Raw 2) typ)
    [((.IId (.Anon 1), .INSTR_Op (.EXP_Ident (.ID_Local (.Raw 2)))), [])] =
    [((.IId (.Raw 2), .INSTR_Op (.EXP_Ident (.ID_Local (.Anon 1)))), [])] := rfl

-- The source deliberately does not apply a string endomorphism to inline assembly.
example (s : IRString) :
    letI : Endo IRString := ⟨fun _ ↦ s⟩
    endo (.EXP_Metadata (.METADATA_Debug default default) : exp typ) =
      .EXP_Metadata (.METADATA_Debug s s) ∧
    endo (.EXP_Asm false false false false default default : exp typ) =
      .EXP_Asm false false false false default default := ⟨rfl, rfl⟩
