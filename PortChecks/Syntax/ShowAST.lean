import PortChecks.SourceType
import Vellvm.Syntax.ShowAST

open Vellvm Vellvm.Utils.StringUtil Vellvm.Syntax.LLVMAst
open Vellvm.Syntax.DynamicTypes (dtyp)
open Vellvm.Syntax.ShowAST

universe u v

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|Show_Pos"
  Show_Pos : Show Positive

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|DShowList"
  DShowList : ∀ {A : Type u} [DShow A], DShow (List A)

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|DShowPair"
  DShowPair : ∀ {A : Type u} {B : Type v} [DShow A] [DShow B], DShow (Prod A B)

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|DShowShow"
  DShowShow : ∀ {A : Type u} [DShow A], Show A

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showIntSyntax"
  showIntSyntax : Show int_syntax

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowRawId"
  dshowRawId : DShow raw_id

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowIdent"
  dshowIdent : DShow «ident»

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showFloatingPointVariant"
  showFloatingPointVariant : Show floating_point_variant

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowFLoatingPointVariant"
  dshowFLoatingPointVariant : DShow floating_point_variant

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowTyp"
  dshowTyp : DShow typ

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowDTyp"
  dshowDTyp : Show dtyp

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showLinkage"
  showLinkage : Show linkage

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showDllStorage"
  showDllStorage : Show dll_storage

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showVisibility"
  showVisibility : Show visibility

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showCConv"
  showCConv : Show cconv

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showSum"
  showSum : ∀ {A : Type u} {B : Type v} [Show A] [Show B], Show (Sum A B)

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowParamAttr"
  dshowParamAttr : DShow param_attr

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showFnAttr"
  showFnAttr : Show fn_attr

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showTLS"
  showTLS : Show thread_local_storage

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showICmp"
  showICmp : Show icmp

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showFCmp"
  showFCmp : Show fcmp

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showIBinop"
  showIBinop : Show ibinop

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showFBinop"
  showFBinop : Show fbinop

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showFastMath"
  showFastMath : Show fast_math

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|ShowPureConversion"
  ShowPureConversion : Show pure_conversion

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|ShowImpureConversion"
  ShowImpureConversion : Show impure_conversion

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|ShowConversionType"
  ShowConversionType : Show conversion_type

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showFloatSyntax"
  showFloatSyntax : Show float_syntax

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowExp"
  dshowExp : ∀ {T : Type} [DShow T], DShow (exp T)

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowMetadata"
  dshowMetadata : ∀ {T : Type} [DShow T] (md : metadata T), DShow (metadata T)

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowTExp"
  dshowTExp : ∀ {T : Type} [DShow T], DShow (texp T)

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowPhi"
  dshowPhi : ∀ {T : Type} [DShow T], DShow (phi T)

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowOrdering"
  dshowOrdering : DShow ordering

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowCmpxchg"
  dshowCmpxchg : ∀ {T : Type} [DShow T], DShow (cmpxchg T)

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showARmwOperation"
  showARmwOperation : Show atomic_rmw_operation

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showAtomicrmw"
  showAtomicrmw : ∀ {T : Type} [DShow T], DShow (atomicrmw T)

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showUnnamedAddr"
  showUnnamedAddr : Show unnamed_addr

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showTailcall"
  showTailcall : Show tailcall

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowCallArg"
  dshowCallArg : ∀ {T : Type} [DShow T], DShow (Prod (texp T) (List param_attr))

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowInstr"
  dshowInstr : ∀ {T : Type} [DShow T], DShow (instr T)

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowInstrId"
  dshowInstrId : DShow instr_id

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showTintLiteral"
  showTintLiteral : Show tint_literal

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowTerminator"
  dshowTerminator : ∀ {T : Type} [DShow T], DShow (terminator T)

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowBlock"
  dshowBlock : ∀ {T : Type} [DShow T], DShow (block T)

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowTypInstr"
  dshowTypInstr : ∀ {T : Type} [DShow T], DShow (Prod T (instr T))

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowArg"
  dshowArg : ∀ {T : Type} [DShow T], DShow (Prod (Prod local_id T) (List param_attr))

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowDefinition"
  dshowDefinition : DShow (definition typ (Prod (block typ) (List (block typ))))

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowDeclaration"
  dshowDeclaration : DShow (declaration typ)

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowGlobal"
  dshowGlobal : DShow («global» typ)

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowTLE"
  dshowTLE : DShow (toplevel_entity typ (Prod (block typ) (List (block typ))))

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|dshowProg"
  dshowProg : DShow (List (toplevel_entity typ (Prod (block typ) (List (block typ)))))

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|showTyp"
  showTyp : Show typ

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|DShow_Z"
  DShow_Z : DShow Int

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|DShow_dtyp"
  DShow_dtyp : DShow dtyp

#source_check "src/rocq/Syntax/ShowAST.v|Vellvm.Syntax.ShowAST|DShow_N"
  DShow_N : DShow Nat
