import PortChecks.SourceType
import Vellvm.Syntax.ReprAST

namespace Vellvm.Syntax.ReprAST
open LLVMAst DynamicTypes

universe u v

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprList"
  reprList : ∀ (A : Type u) [Repr A], Repr (List A)

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprInt"
  reprInt : Repr int_ast

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprBool"
  reprBool : Repr Bool

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprUnit"
  reprUnit : Repr Unit

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprString"
  reprString : Repr IRString

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprRawId"
  reprRawId : Repr raw_id

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprIdent"
  reprIdent : Repr «ident»

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprN"
  reprN : Repr Nat

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprPos"
  reprPos : Repr Positive

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprFile_info"
  reprFile_info : Repr file_info

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|repr_floating_point_variant"
  repr_floating_point_variant : Repr floating_point_variant

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|repr_dtyp_base_Repr"
  repr_dtyp_base_Repr : Repr dtyp_base

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprTyp"
  reprTyp : Repr typ

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprIBinop"
  reprIBinop : Repr ibinop

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprICmp"
  reprICmp : Repr icmp

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprPair"
  reprPair : ∀ (A : Type u) (B : Type v) [Repr A] [Repr B], Repr (A × B)

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprFastMath"
  reprFastMath : Repr fast_math

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|ReprPureConversion"
  ReprPureConversion : Repr pure_conversion

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|ReprImpureConversion"
  ReprImpureConversion : Repr impure_conversion

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprConversionType"
  reprConversionType : Repr conversion_type

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprFBinop"
  reprFBinop : Repr fbinop

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprFCmp"
  reprFCmp : Repr fcmp

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprDecimalUINT"
  reprDecimalUINT : Repr Decimal.uint

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprDecimalSignedInt"
  reprDecimalSignedInt : Repr Decimal.signed_int

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprDecimalDecimal"
  reprDecimalDecimal : Repr Decimal.decimal

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprHexadecimalUINT"
  reprHexadecimalUINT : Repr Hexadecimal.uint

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprHexadecimalSignedInt"
  reprHexadecimalSignedInt : Repr Hexadecimal.signed_int

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprNumberSignedInt"
  reprNumberSignedInt : Repr Number.signed_int

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprIntSyntax"
  reprIntSyntax : Repr int_syntax

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprFloatHexType"
  reprFloatHexType : Repr float_hex_type

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprFloatSyntax"
  reprFloatSyntax : Repr float_syntax

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprExp"
  reprExp : Repr (exp typ)

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprTExp"
  reprTExp : Repr (texp typ)

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprMetadata"
  reprMetadata : Repr (metadata typ)

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprOption"
  reprOption : ∀ (A : Type u) [Repr A], Repr (Option A)

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprParamAttr"
  reprParamAttr : Repr param_attr

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprLinkage"
  reprLinkage : Repr linkage

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprVisibility"
  reprVisibility : Repr visibility

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprDll_Storage"
  reprDll_Storage : Repr dll_storage

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprCconv"
  reprCconv : Repr cconv

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprMemLoc"
  reprMemLoc : Repr mem_loc

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprMemAccessKind"
  reprMemAccessKind : Repr mem_access_kind

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprFn_Attr"
  reprFn_Attr : Repr fn_attr

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprThread_Local_Storage"
  reprThread_Local_Storage : Repr thread_local_storage

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprPremptionSpecifier"
  reprPremptionSpecifier : Repr preemption_specifier

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprUnnamedAddr"
  reprUnnamedAddr : Repr unnamed_addr

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprTailcall"
  reprTailcall : Repr tailcall

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprOrdering"
  reprOrdering : Repr ordering

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprAnnotation"
  reprAnnotation : Repr (annotation typ)

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprAtomicRMWOperation"
  reprAtomicRMWOperation : Repr atomic_rmw_operation

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprAtomicRMW"
  reprAtomicRMW : Repr (atomicrmw typ)

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprCmpxchg"
  reprCmpxchg : Repr (cmpxchg typ)

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprClause"
  reprClause : Repr (@landingpad_clause typ)

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprOperand"
  reprOperand : Repr (@operand typ)

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|ReprOperand_bundle"
  ReprOperand_bundle : Repr (@operand_bundle typ)

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprInstr"
  reprInstr : Repr (instr typ)

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprInstrId"
  reprInstrId : Repr instr_id

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprTintLiteral"
  reprTintLiteral : Repr tint_literal

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprTerminator"
  reprTerminator : Repr (terminator typ)

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprPhi"
  reprPhi : Repr (phi typ)

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprBlock"
  reprBlock : Repr (block typ)

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprDeclaration"
  reprDeclaration : Repr (declaration typ)

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprDefinition"
  reprDefinition : Repr (definition typ (block typ × List (block typ)))

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprGlobal"
  reprGlobal : Repr («global» typ)

#source_check "src/rocq/Syntax/ReprAST.v|Vellvm.Syntax.ReprAST|reprTLE"
  reprTLE : Repr (toplevel_entity typ (block typ × List (block typ)))

end Vellvm.Syntax.ReprAST
