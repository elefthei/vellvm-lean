/-
Rocq constructor serialization from src/rocq/Syntax/ReprAST.v.
Copyright (c) 2026 Vellvm developers. MIT License (see LICENSE.md).
-/
module

public import Vellvm.Syntax.DynamicTypes
public import Vellvm.Syntax.ShowAST

@[expose] public section
namespace Vellvm.Syntax.ReprAST

open LLVMAst DynamicTypes Utils.StringUtil

class Repr (A : Type u) where
  Build_Repr ::
  repr : A → IRString

export Repr (Build_Repr repr)

instance reprList (A : Type u) [Repr A] : Repr (List A) :=
  ⟨fun xs ↦ "[".toUTF8 ++ contents repr xs ++ "]".toUTF8⟩

instance reprInt : Repr int_ast := ⟨fun i ↦ "(".toUTF8 ++ «show» i ++ ")%Z".toUTF8⟩

instance reprBool : Repr Bool := ⟨«show»⟩

instance reprUnit : Repr Unit := ⟨fun _ ↦ "tt".toUTF8⟩

instance reprString : Repr IRString := ⟨«show»⟩

def repr_raw_id : raw_id → IRString
  | .Name s => "(Name ".toUTF8 ++ repr s ++ ")".toUTF8
  | .Anon i => "(Anon ".toUTF8 ++ repr i ++ ")".toUTF8
  | .Raw i => "(Raw ".toUTF8 ++ repr i ++ ")".toUTF8

instance reprRawId : Repr raw_id := ⟨repr_raw_id⟩

def repr_ident : «ident» → IRString
  | .ID_Global r => "(ID_Global ".toUTF8 ++ repr r ++ ")".toUTF8
  | .ID_Local r => "(ID_Local ".toUTF8 ++ repr r ++ ")".toUTF8

instance reprIdent : Repr «ident» := ⟨repr_ident⟩

instance reprN : Repr Nat := ⟨«show»⟩

instance reprPos : Repr Positive := ⟨«show»⟩

def repr_file_info (f : file_info) : IRString :=
  "(mk_file_info \"".toUTF8 ++ f.filename ++ "\" ".toUTF8 ++ repr f.start_line ++ " ".toUTF8 ++
    repr f.start_col ++ " ".toUTF8 ++ repr f.end_line ++ " ".toUTF8 ++ repr f.end_col ++ ")".toUTF8

instance reprFile_info : Repr file_info := ⟨repr_file_info⟩

def repr_fp_variant : floating_point_variant → IRString
  | .FP_half => "FP_half".toUTF8
  | .FP_bfloat => "FP_bfloat".toUTF8
  | .FP_float => "FP_float".toUTF8
  | .FP_double => "FP_double".toUTF8
  | .FP_fp128 => "FP_fp128".toUTF8
  | .FP_x86_fp80 => "FP_x86_fp80".toUTF8
  | .FP_ppc_fp128 => "FP_ppc_fp128".toUTF8

instance repr_floating_point_variant : Repr floating_point_variant := ⟨repr_fp_variant⟩

def repr_dtyp_base : dtyp_base → IRString
  | .DTYPE_I sz => "(DTYPE_I ".toUTF8 ++ repr sz ++ ")".toUTF8
  | .DTYPE_Iptr => "DTYPE_Iptr".toUTF8
  | .DTYPE_Pointer => "DTYPE_Pointer".toUTF8
  | .DTYPE_Void => "DTYPE_Void".toUTF8
  | .DTYPE_FP fp => "(DTYPE_FP ".toUTF8 ++ repr fp ++ ")".toUTF8
  | .DTYPE_Label => "DTYPE_Label".toUTF8
  | .DTYPE_Token => "DTYPE_Token".toUTF8
  | .DTYPE_Metadata => "DTYPE_Metadata".toUTF8
  | .DTYPE_X86_mmx => "DTYPE_X86_mmx".toUTF8
  | .DTYPE_Opaque => "DTYPE_Opaque".toUTF8
  | .DTYPE_B sz => "(DTYPE_B ".toUTF8 ++ repr sz ++ ")".toUTF8

instance repr_dtyp_base_Repr : Repr dtyp_base := ⟨repr_dtyp_base⟩

mutual
  def repr_dtyp : dtyp → IRString
    | .DTYPE_Base t => "(DTYPE_Base (".toUTF8 ++ repr t ++ "))".toUTF8
    | .DTYPE_Struct p fields =>
      "(DTYPE_Struct ".toUTF8 ++ repr p ++ " [".toUTF8 ++ reprDtypFields fields ++ "])".toUTF8
    | .DTYPE_Array v sz t =>
      "(DTYPE_Array ".toUTF8 ++ repr v ++ " (".toUTF8 ++ repr sz ++ ") (".toUTF8 ++ repr_dtyp t
        ++ "))".toUTF8

  def reprDtypFields (fields : List dtyp) (out : IRString := .empty) : IRString :=
    match fields with
    | [] => out
    | x :: xs =>
      let out := out ++ repr_dtyp x
      if xs.isEmpty then out else reprDtypFields xs (out ++ "; ".toUTF8)
end

mutual
  def repr_typ : typ → IRString
    | .TYPE_I sz => "(TYPE_I ".toUTF8 ++ repr sz ++ ")".toUTF8
    | .TYPE_B sz => "(TYPE_B ".toUTF8 ++ repr sz ++ ")".toUTF8
    | .TYPE_Iptr => "TYPE_Iptr".toUTF8
    | .TYPE_Pointer (some t) => "(TYPE_Pointer (Some ".toUTF8 ++ repr_typ t ++ "))".toUTF8
    | .TYPE_Pointer none => "(TYPE_Pointer None)".toUTF8
    | .TYPE_Void => "TYPE_Void".toUTF8
    | .TYPE_FP fp => "(TYPE_FP ".toUTF8 ++ repr fp ++ ")".toUTF8
    | .TYPE_Label => "TYPE_Label".toUTF8
    | .TYPE_Token => "TYPE_Token".toUTF8
    | .TYPE_Metadata => "TYPE_Metadata".toUTF8
    | .TYPE_X86_mmx => "TYPE_X86_mmx".toUTF8
    | .TYPE_Array sz t =>
      "(TYPE_Array (".toUTF8 ++ repr sz ++ ") (".toUTF8 ++ repr_typ t ++ "))".toUTF8
    | .TYPE_Function ret args varargs =>
      "(TYPE_Function (".toUTF8 ++ repr_typ ret ++ ")\n        [".toUTF8 ++ reprTypFields args
        ++ "]".toUTF8 ++ " ".toUTF8 ++ (if varargs then "true".toUTF8 else "false".toUTF8)
        ++ ")".toUTF8
    | .TYPE_Struct fields => "(TYPE_Struct [".toUTF8 ++ reprTypFields fields ++ "])".toUTF8
    | .TYPE_Packed_struct fields =>
      "(TYPE_Packed_struct [".toUTF8 ++ reprTypFields fields ++ "])".toUTF8
    | .TYPE_Opaque => "TYPE_Opaque".toUTF8
    | .TYPE_Vector sz t =>
      "(TYPE_Vector (".toUTF8 ++ repr sz ++ ") (".toUTF8 ++ repr_typ t ++ "))".toUTF8
    | .TYPE_Identified id => "(TYPE_Identified ".toUTF8 ++ repr id ++ ")".toUTF8

  def reprTypFields (fields : List typ) (out : IRString := .empty) : IRString :=
    match fields with
    | [] => out
    | x :: xs =>
      let out := out ++ repr_typ x
      if xs.isEmpty then out else reprTypFields xs (out ++ "; ".toUTF8)
end

instance reprTyp : Repr typ := ⟨repr_typ⟩

def repr_ibinop : ibinop → IRString
  | .Add a b => "(LLVMAst.Add ".toUTF8 ++ repr a ++ " ".toUTF8 ++ repr b ++ ")".toUTF8
  | .Sub a b => "(Sub ".toUTF8 ++ repr a ++ " ".toUTF8 ++ repr b ++ ")".toUTF8
  | .Mul a b => "(Mul ".toUTF8 ++ repr a ++ " ".toUTF8 ++ repr b ++ ")".toUTF8
  | .Shl a b => "(Shl ".toUTF8 ++ repr a ++ " ".toUTF8 ++ repr b ++ ")".toUTF8
  | .UDiv f => "(UDiv ".toUTF8 ++ repr f ++ ")".toUTF8
  | .SDiv f => "(SDiv ".toUTF8 ++ repr f ++ ")".toUTF8
  | .LShr f => "(LShr ".toUTF8 ++ repr f ++ ")".toUTF8
  | .AShr f => "(AShr ".toUTF8 ++ repr f ++ ")".toUTF8
  | .URem => "URem".toUTF8
  | .SRem => "SRem".toUTF8
  | .And => "And".toUTF8
  | .Or dj => "(Or ".toUTF8 ++ repr dj ++ ")".toUTF8
  | .Xor => "Xor".toUTF8

instance reprIBinop : Repr ibinop := ⟨repr_ibinop⟩

def repr_gep_flags (f : gep_flags) : IRString :=
  "(mk_gep_flags ".toUTF8 ++ repr f.gep_inbounds ++ " ".toUTF8 ++ repr f.gep_nusw ++
    " ".toUTF8 ++ repr f.gep_nuw ++ ")".toUTF8

def repr_icmp : icmp → IRString
  | .Eq => "Eq".toUTF8
  | .Ne => "Ne".toUTF8
  | .Ugt => "Ugt".toUTF8
  | .Uge => "Uge".toUTF8
  | .Ult => "Ult".toUTF8
  | .Ule => "Ule".toUTF8
  | .Sgt => "Sgt".toUTF8
  | .Sge => "Sge".toUTF8
  | .Slt => "Slt".toUTF8
  | .Sle => "Sle".toUTF8

instance reprICmp : Repr icmp := ⟨repr_icmp⟩

instance reprPair (A : Type u) (B : Type v) [Repr A] [Repr B] : Repr (A × B) :=
  ⟨fun (a, b) ↦ "(".toUTF8 ++ repr a ++ ", ".toUTF8 ++ repr b ++ ")".toUTF8⟩

def repr_fast_math : fast_math → IRString
  | .Nnan => "Nnan".toUTF8
  | .Ninf => "Ninf".toUTF8
  | .Nsz => "Nsz".toUTF8
  | .Arcp => "Arcp".toUTF8
  | .Contract => "Contract".toUTF8
  | .Afn => "Afn".toUTF8
  | .Reassoc => "Reassoc".toUTF8
  | .Fast => "Fast".toUTF8

instance reprFastMath : Repr fast_math := ⟨repr_fast_math⟩

def pair_repr {A : Type u} {B : Type v} (fa : A → IRString) (fb : B → IRString)
    (ab : A × B) : IRString := "(".toUTF8 ++ fa ab.1 ++ ", ".toUTF8 ++ fb ab.2 ++ ")".toUTF8

def repr_pure_conversion : pure_conversion → IRString
  | .Trunc a b => "(Trunc ".toUTF8 ++ repr a ++ " ".toUTF8 ++ repr b ++ ")".toUTF8
  | .Zext a => "(Zext ".toUTF8 ++ repr a ++ ")".toUTF8
  | .Sext => "Sext".toUTF8
  | .Fptrunc flags => "(Fptrunc ".toUTF8 ++ repr flags ++ ")".toUTF8
  | .Fpext flags => "(Fpext ".toUTF8 ++ repr flags ++ ")".toUTF8
  | .Uitofp a => "(Uitofp ".toUTF8 ++ repr a ++ ")".toUTF8
  | .Sitofp => "Sitofp".toUTF8
  | .Fptoui => "Fptoui".toUTF8
  | .Fptosi => "Fptosi".toUTF8

instance ReprPureConversion : Repr pure_conversion := ⟨repr_pure_conversion⟩

def repr_impure_conversion : impure_conversion → IRString
  | .Inttoptr => "Inttoptr ".toUTF8
  | .Ptrtoint => "Ptrtoint".toUTF8
  | .Ptrtoaddr => "Ptrtoaddr".toUTF8
  | .Addrspacecast => "Addrspacecast".toUTF8

instance ReprImpureConversion : Repr impure_conversion := ⟨repr_impure_conversion⟩

def repr_conversion_type : conversion_type → IRString
  | .CONV_Bitcast => "CONV_Bitcast".toUTF8
  | .CONV_Pure ct => "(CONV_Pure ".toUTF8 ++ repr ct ++ ")".toUTF8
  | .CONV_Impure ct => "(CONV_Impure ".toUTF8 ++ repr ct ++ ")".toUTF8

instance reprConversionType : Repr conversion_type := ⟨repr_conversion_type⟩

def repr_fbinop : fbinop → IRString
  | .FAdd => "FAdd".toUTF8
  | .FSub => "FSub".toUTF8
  | .FMul => "FMul".toUTF8
  | .FDiv => "FDiv".toUTF8
  | .FRem => "FRem".toUTF8

instance reprFBinop : Repr fbinop := ⟨repr_fbinop⟩

def repr_fcmp : fcmp → IRString
  | .FFalse => "FFalse".toUTF8
  | .FOeq => "FOeq".toUTF8
  | .FOgt => "FOgt".toUTF8
  | .FOge => "FOge".toUTF8
  | .FOlt => "FOlt".toUTF8
  | .FOle => "FOle".toUTF8
  | .FOne => "FOne".toUTF8
  | .FOrd => "FOrd".toUTF8
  | .FUno => "FUno".toUTF8
  | .FUeq => "FUeq".toUTF8
  | .FUgt => "FUgt".toUTF8
  | .FUge => "FUge".toUTF8
  | .FUlt => "FUlt".toUTF8
  | .FUle => "FUle".toUTF8
  | .FUne => "FUne".toUTF8
  | .FTrue => "FTrue".toUTF8

instance reprFCmp : Repr fcmp := ⟨repr_fcmp⟩

def repr_Decimal_uint : Decimal.uint → IRString
  | .Nil => "Decimal.Nil".toUTF8
  | .D0 u => "(Decimal.D0 ".toUTF8 ++ repr_Decimal_uint u ++ ")".toUTF8
  | .D1 u => "(Decimal.D1 ".toUTF8 ++ repr_Decimal_uint u ++ ")".toUTF8
  | .D2 u => "(Decimal.D2 ".toUTF8 ++ repr_Decimal_uint u ++ ")".toUTF8
  | .D3 u => "(Decimal.D3 ".toUTF8 ++ repr_Decimal_uint u ++ ")".toUTF8
  | .D4 u => "(Decimal.D4 ".toUTF8 ++ repr_Decimal_uint u ++ ")".toUTF8
  | .D5 u => "(Decimal.D5 ".toUTF8 ++ repr_Decimal_uint u ++ ")".toUTF8
  | .D6 u => "(Decimal.D6 ".toUTF8 ++ repr_Decimal_uint u ++ ")".toUTF8
  | .D7 u => "(Decimal.D7 ".toUTF8 ++ repr_Decimal_uint u ++ ")".toUTF8
  | .D8 u => "(Decimal.D8 ".toUTF8 ++ repr_Decimal_uint u ++ ")".toUTF8
  | .D9 u => "(Decimal.D9 ".toUTF8 ++ repr_Decimal_uint u ++ ")".toUTF8

instance reprDecimalUINT : Repr Decimal.uint := ⟨repr_Decimal_uint⟩

def repr_Decimal_signed_int : Decimal.signed_int → IRString
  | .Pos u => "(Decimal.Pos ".toUTF8 ++ repr u ++ ")".toUTF8
  | .Neg u => "(Decimal.Neg ".toUTF8 ++ repr u ++ ")".toUTF8

instance reprDecimalSignedInt : Repr Decimal.signed_int := ⟨repr_Decimal_signed_int⟩

def repr_Decimal_decimal : Decimal.decimal → IRString
  | .Decimal i f => "(Decimal.Decimal ".toUTF8 ++ repr i ++ " ".toUTF8 ++ repr f ++ ")".toUTF8
  | .DecimalExp i f e =>
    "(Decimal.DecimalExp ".toUTF8 ++ repr i ++ " ".toUTF8 ++ repr f ++ " ".toUTF8 ++ repr e
      ++ ")".toUTF8

instance reprDecimalDecimal : Repr Decimal.decimal := ⟨repr_Decimal_decimal⟩

def repr_Hexadecimal_uint : Hexadecimal.uint → IRString
  | .Nil => "Hexadecimal.Nil".toUTF8
  | .D0 u => "(Hexadecimal.D0 ".toUTF8 ++ repr_Hexadecimal_uint u ++ ")".toUTF8
  | .D1 u => "(Hexadecimal.D1 ".toUTF8 ++ repr_Hexadecimal_uint u ++ ")".toUTF8
  | .D2 u => "(Hexadecimal.D2 ".toUTF8 ++ repr_Hexadecimal_uint u ++ ")".toUTF8
  | .D3 u => "(Hexadecimal.D3 ".toUTF8 ++ repr_Hexadecimal_uint u ++ ")".toUTF8
  | .D4 u => "(Hexadecimal.D4 ".toUTF8 ++ repr_Hexadecimal_uint u ++ ")".toUTF8
  | .D5 u => "(Hexadecimal.D5 ".toUTF8 ++ repr_Hexadecimal_uint u ++ ")".toUTF8
  | .D6 u => "(Hexadecimal.D6 ".toUTF8 ++ repr_Hexadecimal_uint u ++ ")".toUTF8
  | .D7 u => "(Hexadecimal.D7 ".toUTF8 ++ repr_Hexadecimal_uint u ++ ")".toUTF8
  | .D8 u => "(Hexadecimal.D8 ".toUTF8 ++ repr_Hexadecimal_uint u ++ ")".toUTF8
  | .D9 u => "(Hexadecimal.D9 ".toUTF8 ++ repr_Hexadecimal_uint u ++ ")".toUTF8
  | .Da u => "(Hexadecimal.Da ".toUTF8 ++ repr_Hexadecimal_uint u ++ ")".toUTF8
  | .Db u => "(Hexadecimal.Db ".toUTF8 ++ repr_Hexadecimal_uint u ++ ")".toUTF8
  | .Dc u => "(Hexadecimal.Dc ".toUTF8 ++ repr_Hexadecimal_uint u ++ ")".toUTF8
  | .Dd u => "(Hexadecimal.Dd ".toUTF8 ++ repr_Hexadecimal_uint u ++ ")".toUTF8
  | .De u => "(Hexadecimal.De ".toUTF8 ++ repr_Hexadecimal_uint u ++ ")".toUTF8
  | .Df u => "(Hexadecimal.Df ".toUTF8 ++ repr_Hexadecimal_uint u ++ ")".toUTF8

instance reprHexadecimalUINT : Repr Hexadecimal.uint := ⟨repr_Hexadecimal_uint⟩

def repr_Hexadecimal_signed_int : Hexadecimal.signed_int → IRString
  | .Pos u => "(Hexadecimal.Pos ".toUTF8 ++ repr u ++ ")".toUTF8
  | .Neg u => "(Hexadecimal.Neg ".toUTF8 ++ repr u ++ ")".toUTF8

instance reprHexadecimalSignedInt : Repr Hexadecimal.signed_int := ⟨repr_Hexadecimal_signed_int⟩

def repr_Number_signed_int : Number.signed_int → IRString
  | .IntDecimal i => "(Number.IntDecimal ".toUTF8 ++ repr i ++ ")".toUTF8
  | .IntHexadecimal i => "(Number.IntHexadecimal ".toUTF8 ++ repr i ++ ")".toUTF8

instance reprNumberSignedInt : Repr Number.signed_int := ⟨repr_Number_signed_int⟩

def repr_int_syntax : int_syntax → IRString := repr_Number_signed_int

instance reprIntSyntax : Repr int_syntax := ⟨repr_int_syntax⟩

def repr_float_hex_type : float_hex_type → IRString
  | .FH_X => "FH_X".toUTF8
  | .FH_K => "FH_K".toUTF8
  | .FH_L => "FH_L".toUTF8
  | .FH_M => "FH_M".toUTF8
  | .FH_H => "FH_H".toUTF8
  | .FH_R => "FH_R".toUTF8

instance reprFloatHexType : Repr float_hex_type := ⟨repr_float_hex_type⟩

def repr_float_syntax : float_syntax → IRString
  | .FS_decimal d => "(FS_decimal ".toUTF8 ++ repr d ++ ")".toUTF8
  | .FS_hex t u => "(FS_hex ".toUTF8 ++ repr t ++ " ".toUTF8 ++ repr u ++ ")".toUTF8

instance reprFloatSyntax : Repr float_syntax := ⟨repr_float_syntax⟩

mutual
  def repr_exp : exp typ → IRString
    | .EXP_Ident id => "(EXP_Ident ".toUTF8 ++ repr id ++ ")".toUTF8
    | .EXP_Integer x => "(EXP_Integer ".toUTF8 ++ repr x ++ ")".toUTF8
    | .EXP_Float f => "(EXP_Float ".toUTF8 ++ repr f ++ ")".toUTF8
    | .EXP_Bool b => "(EXP_Bool ".toUTF8 ++ repr b ++ ")".toUTF8
    | .EXP_Null => "EXP_Null".toUTF8
    | .EXP_Zero_initializer => "EXP_Zero_initializer".toUTF8
    | .EXP_Cstring s => "(EXP_Cstring [".toUTF8 ++ reprTypedFields s ++ "])".toUTF8
    | .EXP_Undef => "EXP_Undef".toUTF8
    | .EXP_Poison => "EXP_Poison".toUTF8
    | .EXP_Struct fields => "(EXP_Struct [".toUTF8 ++ reprTypedFields fields ++ "])".toUTF8
    | .EXP_Packed_struct fields =>
      "(EXP_Packed_struct [".toUTF8 ++ reprTypedFields fields ++ "])".toUTF8
    | .EXP_Array fields => "(EXP_Array [".toUTF8 ++ reprTypedFields fields ++ "])".toUTF8
    | .EXP_Vector fields => "(EXP_vector [".toUTF8 ++ reprTypedFields fields ++ "])".toUTF8
    | .OP_IBinop iop t v1 v2 =>
      "(OP_IBinop ".toUTF8 ++ repr iop ++ " ".toUTF8 ++ repr t ++ " ".toUTF8 ++ repr_exp v1
        ++ " ".toUTF8 ++ repr_exp v2 ++ ")".toUTF8
    | .OP_ICmp s cmp t v1 v2 =>
      "(OP_ICmp ".toUTF8 ++ repr s ++ " ".toUTF8 ++ repr cmp ++ " ".toUTF8 ++ repr t ++ " ".toUTF8
        ++ repr_exp v1 ++ " ".toUTF8 ++ repr_exp v2 ++ ")".toUTF8
    | .OP_FBinop fop fm t v1 v2 =>
      "(OP_FBinop ".toUTF8 ++ repr fop ++ " [".toUTF8 ++ contents repr_fast_math fm ++ "] ".toUTF8
        ++ repr t ++ " ".toUTF8 ++ repr_exp v1 ++ " ".toUTF8 ++ repr_exp v2 ++ ")".toUTF8
    | .OP_Fneg fm v =>
      "(OP_Fneg [".toUTF8 ++ contents repr_fast_math fm ++ "] ".toUTF8 ++ reprTyped v ++ ")".toUTF8
    | .OP_FCmp cmp fm t v1 v2 =>
      "(OP_FCmp ".toUTF8 ++ repr cmp ++ " [".toUTF8 ++ contents repr_fast_math fm ++ "] ".toUTF8
        ++ repr t ++ " ".toUTF8 ++ repr_exp v1 ++ " ".toUTF8 ++ repr_exp v2 ++ ")".toUTF8
    | .OP_Conversion c srcTy v dstTy =>
      "(OP_Conversion ".toUTF8 ++ repr c ++ " ".toUTF8 ++ repr srcTy ++ " ".toUTF8 ++ repr_exp v
        ++ " ".toUTF8 ++ repr dstTy ++ ")".toUTF8
    | .OP_GetElementPtr flags t ptrval idxs =>
      "(OP_GetElementPtr ".toUTF8 ++ repr_gep_flags flags ++ " ".toUTF8 ++ repr t ++ "(".toUTF8
        ++ reprTyped ptrval ++ ") [".toUTF8 ++ reprTypedFields idxs ++ "])".toUTF8
    | .OP_ExtractElement v i =>
      "(OP_ExtractElement ".toUTF8 ++ reprTyped v ++ " ".toUTF8 ++ reprTyped i ++ ")".toUTF8
    | .OP_InsertElement v e i =>
      "(OP_ExtractElement ".toUTF8 ++ reprTyped v ++ " ".toUTF8 ++ reprTyped e ++ " ".toUTF8
        ++ reprTyped i ++ ")".toUTF8
    | .OP_ShuffleVector v1 v2 mask =>
      "(OP_ShuffleVector ".toUTF8 ++ reprTyped v1 ++ " ".toUTF8 ++ reprTyped v2 ++ " ".toUTF8
        ++ reprTyped mask ++ ")".toUTF8
    | .OP_ExtractValue v idxs =>
      "(OP_ExtractValue ".toUTF8 ++ reprTyped v ++ " [".toUTF8
        ++ contents ShowAST.show_int_syntax idxs ++ "])".toUTF8
    | .OP_InsertValue v e idxs =>
      "(OP_ExtractValue ".toUTF8 ++ reprTyped v ++ " ".toUTF8 ++ reprTyped e ++ " [".toUTF8
        ++ contents ShowAST.show_int_syntax idxs ++ "])".toUTF8
    | .OP_Select fm cnd v1 v2 =>
      "(OP_Select [".toUTF8 ++ contents repr_fast_math fm ++ "] ".toUTF8 ++ reprTyped cnd
        ++ " ".toUTF8 ++ reprTyped v1 ++ " ".toUTF8 ++ reprTyped v2 ++ ")".toUTF8
    | .OP_Freeze v => "(OP_Freeze ".toUTF8 ++ reprTyped v ++ ")".toUTF8
    | .EXP_Asm sideffect alignstack inteldialect unwind template operand_constraints =>
      "(EXP_Asm ".toUTF8 ++ (repr sideffect) ++ " ".toUTF8 ++ (repr alignstack) ++ " ".toUTF8
        ++ (repr inteldialect) ++ " ".toUTF8 ++ (repr unwind) ++ " ".toUTF8 ++ "\"".toUTF8
        ++ template ++ "\" ".toUTF8 ++ "\"".toUTF8 ++ operand_constraints ++ "\")".toUTF8
    | .EXP_Metadata md => "(EXP_Metadata ".toUTF8 ++ repr_metadata md ++ ")".toUTF8
    | .EXP_Splat elt => "(EXP_splt ".toUTF8 ++ reprTyped elt ++ ")".toUTF8
    | .EXP_BlockAddress func blk =>
      "(EXP_BlockAddress ".toUTF8 ++ repr func ++ " ".toUTF8 ++ repr blk ++ ")".toUTF8

  def repr_metadata : metadata typ → IRString
    | .METADATA_Null => "METADATA_Null".toUTF8
    | .METADATA_Const tv => "(METADATA_Const ".toUTF8 ++ reprTyped tv ++ ")".toUTF8
    | .METADATA_Id id => "(METADATA_Id ".toUTF8 ++ repr id ++ ")".toUTF8
    | .METADATA_Node mds => "(METADATA_Node [".toUTF8 ++ reprMetadataFields mds ++ "])".toUTF8
    | .METADATA_Pair md1 md2 =>
      "(METADATA_Pair ".toUTF8 ++ (repr_metadata md1) ++ " ".toUTF8 ++ (repr_metadata md2)
        ++ ")".toUTF8
    | .METADATA_Debug s1 s2 =>
      "(METADATA_Debug ".toUTF8 ++ repr s1 ++ ", ".toUTF8 ++ repr s2 ++ ")".toUTF8
    | .METADATA_File_info f => "(METADATA_File_info ".toUTF8 ++ (repr f) ++ ")".toUTF8

  def reprTyped : texp typ → IRString
    | (t, e) => "(".toUTF8 ++ repr_typ t ++ ", ".toUTF8 ++ repr_exp e ++ ")".toUTF8

  def reprTypedFields (fields : List (texp typ)) (out : IRString := .empty) : IRString :=
    match fields with
    | [] => out
    | x :: xs =>
      let out := out ++ reprTyped x
      if xs.isEmpty then out else reprTypedFields xs (out ++ "; ".toUTF8)

  def reprMetadataFields (fields : List (metadata typ)) (out : IRString := .empty) : IRString :=
    match fields with
    | [] => out
    | x :: xs =>
      let out := out ++ repr_metadata x
      if xs.isEmpty then out else reprMetadataFields xs (out ++ "; ".toUTF8)
end

instance reprExp : Repr (exp typ) := ⟨repr_exp⟩

instance reprTExp : Repr (texp typ) := ⟨reprTyped⟩

instance reprMetadata : Repr (metadata typ) := ⟨repr_metadata⟩

def repr_opt {A : Type u} [Repr A] : Option A → IRString
  | none => "None".toUTF8
  | some a => "(Some ".toUTF8 ++ repr a ++ ")".toUTF8

instance reprOption (A : Type u) [Repr A] : Repr (Option A) := ⟨repr_opt⟩

def repr_param_attr : param_attr → IRString
  | .PARAMATTR_Zeroext => "PARAMATTR_Zeroext".toUTF8
  | .PARAMATTR_Signext => "PARAMATTR_Signext".toUTF8
  | .PARAMATTR_Inreg => "PARAMATTR_Inreg".toUTF8
  | .PARAMATTR_Byval t => "PARAMATTR_Byval ".toUTF8 ++ repr t
  | .PARAMATTR_Byref t => "PARAMATTR_Byref ".toUTF8 ++ repr t
  | .PARAMATTR_Preallocated t => "PARAMATTR_Preallocated ".toUTF8 ++ repr t
  | .PARAMATTR_Inalloca t => "PARAMATTR_Inalloca ".toUTF8 ++ repr t
  | .PARAMATTR_Sret t => "PARAMATTR_Sret ".toUTF8 ++ repr t
  | .PARAMATTR_Elementtype t => "PARAMATTR_Elementtype ".toUTF8 ++ repr t
  | .PARAMATTR_Align a => "(PARAMATTR_Align ".toUTF8 ++ repr a ++ ")".toUTF8
  | .PARAMATTR_Noalias => "PARAMATTR_Noalias".toUTF8
  | .PARAMATTR_Nocapture => "PARAMATTR_Nocapture".toUTF8
  | .PARAMATTR_Nofree => "PARAMATTR_Nofree".toUTF8
  | .PARAMATTR_Nest => "PARAMATTR_Nest".toUTF8
  | .PARAMATTR_Returned => "PARAMATTR_Returned".toUTF8
  | .PARAMATTR_Nonnull => "PARAMATTR_Nonnull".toUTF8
  | .PARAMATTR_Dereferenceable a => "(PARAMATTR_Dereferenceable ".toUTF8 ++ repr a ++ ")".toUTF8
  | .PARAMATTR_Dereferenceable_or_null a =>
    "(PARAMATTR_Dereferenceable_or_null ".toUTF8 ++ repr a ++ ")".toUTF8
  | .PARAMATTR_Swiftself => "PARAMATTR_Swiftself".toUTF8
  | .PARAMATTR_Swiftasync => "PARAMATTR_Swiftasync".toUTF8
  | .PARAMATTR_Swifterror => "PARAMATTR_Swifterror".toUTF8
  | .PARAMATTR_Immarg => "PARAMATTR_Immarg".toUTF8
  | .PARAMATTR_Noundef => "PARAMATTR_Noundef".toUTF8
  | .PARAMATTR_Nofpclass mask => "(PARAMATTR_Nofpclass ".toUTF8 ++ repr mask ++ ")".toUTF8
  | .PARAMATTR_Nofreeobj => "PARAMATTR_Nofreeobj".toUTF8
  | .PARAMATTR_Alignstack a => "PARAMATTR_Alignstack ".toUTF8 ++ repr a
  | .PARAMATTR_Allocalign => "PARAMATTR_Allocalign".toUTF8
  | .PARAMATTR_Allocptr => "PARAMATTR_Allocptr".toUTF8
  | .PARAMATTR_Readnone => "PARAMATTR_Readnone".toUTF8
  | .PARAMATTR_Readonly => "PARAMATTR_Readonly".toUTF8
  | .PARAMATTR_Writeonly => "PARAMATTR_Writeonly".toUTF8
  | .PARAMATTR_Writable => "PARAMATTR_Writable".toUTF8
  | .PARAMATTR_Dead_on_unwind => "PARAMATTR_Dead_on_unwind".toUTF8
  | .PARAMATTR_Dead_on_return size =>
    "(PARAMATTR_Dead_on_return ".toUTF8 ++ repr size ++ ")".toUTF8
  | .PARAMATTR_Range t a b =>
    "(PARAMATTR_Range ".toUTF8 ++ repr t ++ " ".toUTF8 ++ repr a ++ " ".toUTF8 ++ repr b
      ++ ")".toUTF8
  | .PARAMATTR_Initializes l => "(PARAMATTR_Initializes ".toUTF8 ++ repr l ++ ")".toUTF8
  | .PARAMATTR_Captures p => "(PARAMATTR_Captures ".toUTF8 ++ repr p ++ ")".toUTF8

instance reprParamAttr : Repr param_attr := ⟨repr_param_attr⟩

def repr_linkage : linkage → IRString
  | .LINKAGE_Private => "LINKAGE_Private".toUTF8
  | .LINKAGE_Internal => "LINKAGE_Internal".toUTF8
  | .LINKAGE_Available_externally => "LINKAGE_Available_externally".toUTF8
  | .LINKAGE_Linkonce => "LINKAGE_Linkonce".toUTF8
  | .LINKAGE_Weak => "LINKAGE_Weak".toUTF8
  | .LINKAGE_Common => "LINKAGE_Common".toUTF8
  | .LINKAGE_Appending => "LINKAGE_Appending".toUTF8
  | .LINKAGE_Extern_weak => "LINKAGE_Extern_weak".toUTF8
  | .LINKAGE_Linkonce_odr => "LINKAGE_Linkonce_odr".toUTF8
  | .LINKAGE_Weak_odr => "LINKAGE_Weak_odr".toUTF8
  | .LINKAGE_External => "LINKAGE_External".toUTF8

instance reprLinkage : Repr linkage := ⟨repr_linkage⟩

def repr_visibility : visibility → IRString
  | .VISIBILITY_Default => "VISIBILITY_Default".toUTF8
  | .VISIBILITY_Hidden => "VISIBILITY_Hidden".toUTF8
  | .VISIBILITY_Protected => "VISIBILITY_Protected".toUTF8

instance reprVisibility : Repr visibility := ⟨repr_visibility⟩

def repr_dll_storage : dll_storage → IRString
  | .DLLSTORAGE_Dllimport => "DLLSTORAGE_Dllimport".toUTF8
  | .DLLSTORAGE_Dllexport => "DLLSTORAGE_Dllexport".toUTF8

instance reprDll_Storage : Repr dll_storage := ⟨repr_dll_storage⟩

def repr_cconv : cconv → IRString
  | .CC_Ccc => "CC_Ccc".toUTF8
  | .CC_Fastcc => "CC_Fastcc".toUTF8
  | .CC_Coldcc => "CC_Coldcc".toUTF8
  | .CC_Cc _ => "CC_Cc cc".toUTF8
  | .CC_Webkit_jscc => "CC_Webkit_jscc".toUTF8
  | .CC_Anyregcc => "CC_Anyregcc".toUTF8
  | .CC_Preserve_allcc => "CC_Preserve_allcc".toUTF8
  | .CC_Cxx_fast_tlscc => "CC_Cxx_fast_tlscc".toUTF8
  | .CC_Tailcc => "CC_Tailcc".toUTF8
  | .CC_Swiftcc => "CC_Swiftcc".toUTF8
  | .CC_Swifttailcc => "CC_Swifttailcc".toUTF8
  | .CC_cfguard_checkcc => "CC_cfguard_checkcc".toUTF8
  | .CC_Preserve_mostcc => "CC_Preserve_mostcc".toUTF8

instance reprCconv : Repr cconv := ⟨repr_cconv⟩

def repr_mem_loc : mem_loc → IRString
  | .LOC_Default => "LOC_Default".toUTF8
  | .LOC_Argmem => "LOC_Argmem".toUTF8
  | .LOC_Inaccessiblemem => "LOC_Inaccessiblemem".toUTF8
  | .LOC_Errnomem => "LOC_Errnomem".toUTF8

instance reprMemLoc : Repr mem_loc := ⟨repr_mem_loc⟩

def repr_mem_access_kind : mem_access_kind → IRString
  | .ACC_None => "ACC_None".toUTF8
  | .ACC_Read => "ACC_Read".toUTF8
  | .ACC_Write => "ACC_Write".toUTF8
  | .ACC_Readwrite => "ACC_Readwrite".toUTF8

instance reprMemAccessKind : Repr mem_access_kind := ⟨repr_mem_access_kind⟩

def repr_fn_attr : fn_attr → IRString
  | .FNATTR_Alignstack a => "(FNATTR_Alignstack ".toUTF8 ++ repr a ++ ")".toUTF8
  | .FNATTR_Allockind kind => "(FNATTR_Allockind ".toUTF8 ++ repr kind ++ ")".toUTF8
  | .FNATTR_Allocsize l l2 =>
    "(FNATTR_Allocsize ".toUTF8 ++ repr l ++ (l2.elim ByteArray.empty repr) ++ ")".toUTF8
  | .FNATTR_Alwaysinline => "FNATTR_Alwaysinline".toUTF8
  | .FNATTR_Builtin => "FNATTR_Builtin".toUTF8
  | .FNATTR_Cold => "FNATTR_Cold".toUTF8
  | .FNATTR_Convergent => "FNATTR_Convergent".toUTF8
  | .FNATTR_Disable_sanitizer_instrumentation =>
    "FNATTR__Disable_sanitizer_instrumentation".toUTF8
  | .FNATTR_Fn_ret_thunk_extern => "FNATTR_Fn_ret_thunk_extern".toUTF8
  | .FNATTR_Hot => "FNATTR_Hot".toUTF8
  | .FNATTR_Inaccessiblememonly => "FNATTR_Inaccessiblememonly".toUTF8
  | .FNATTR_Inaccessiblemem_or_argmemonly => "FNATTR_Inaccessiblemem_or_argmemonly".toUTF8
  | .FNATTR_Inlinehint => "FNATTR_Inlinehint".toUTF8
  | .FNATTR_Jumptable => "FNATTR_Jumptable".toUTF8
  | .FNATTR_Minsize => "FNATTR_Minsize".toUTF8
  | .FNATTR_Naked => "FNATTR_Naked".toUTF8
  | .FNATTR_No_jump_tables => "FNATTR_No_jump_tables".toUTF8
  | .FNATTR_Nobuiltin => "FNATTR_Nobuiltin".toUTF8
  | .FNATTR_Noduplicate => "FNATTR_Noduplicate".toUTF8
  | .FNATTR_Nofree => "FNATTR_Nofree".toUTF8
  | .FNATTR_Noimplicitfloat => "FNATTR_Noimplicitfloat".toUTF8
  | .FNATTR_Noinline => "FNATTR_Noinline".toUTF8
  | .FNATTR_Nomerge => "FNATTR_Nomerge".toUTF8
  | .FNATTR_Nonlazybind => "FNATTR_Nonlazybind".toUTF8
  | .FNATTR_Noprofile => "FNATTR_Noprofile".toUTF8
  | .FNATTR_Noredzone => "FNATTR_Noredzone".toUTF8
  | .FNATTR_Indirect_tls_seg_refs => "FNATTR_Indirect_tls_seg_refs".toUTF8
  | .FNATTR_Noreturn => "FNATTR_Noreturn".toUTF8
  | .FNATTR_Norecurse => "FNATTR_Norecurse".toUTF8
  | .FNATTR_Willreturn => "FNATTR_Willreturn".toUTF8
  | .FNATTR_Nosync => "FNATTR_Nosync".toUTF8
  | .FNATTR_Nounwind => "FNATTR_Nounwind".toUTF8
  | .FNATTR_Nocreateundeforpoison => "FNATTR_Nocreateundeforpoison".toUTF8
  | .FNATTR_Nosanitize_bounds => "FNATTR_Nosanitize_bounds".toUTF8
  | .FNATTR_Nosanitize_coverage => "FNATTR_Nosanitize_coverage".toUTF8
  | .FNATTR_Null_pointer_is_valid => "FNATTR_Null_pointer_is_valid".toUTF8
  | .FNATTR_Optforfuzzing => "FNATTR_Optforfuzzing".toUTF8
  | .FNATTR_Optnone => "FNATTR_Optnone".toUTF8
  | .FNATTR_Optsize => "FNATTR_Optsize".toUTF8
  | .FNATTR_Readnone => "FNATTR_Readnone".toUTF8
  | .FNATTR_Readonly => "FNATTR_Readonly".toUTF8
  | .FNATTR_Writeonly => "FNATTR_Writeonly".toUTF8
  | .FNATTR_Argmemonly => "FNATTR_Argmemonly".toUTF8
  | .FNATTR_Returns_twice => "FNATTR_Returns_twice".toUTF8
  | .FNATTR_Safestack => "FNATTR_Safestack".toUTF8
  | .FNATTR_Sanitize_address => "FNATTR_Sanitize_address".toUTF8
  | .FNATTR_Sanitize_memory => "FNATTR_Sanitize_memory".toUTF8
  | .FNATTR_Sanitize_thread => "FNATTR_Sanitize_thread".toUTF8
  | .FNATTR_Sanitize_hwaddress => "FNATTR_Sanitize_hwaddress".toUTF8
  | .FNATTR_Sanitize_memtag => "FNATTR_Sanitize_memtag".toUTF8
  | .FNATTR_Speculative_load_hardening => "FNATTR_Speculative_load_hardening".toUTF8
  | .FNATTR_Speculatable => "FNATTR_Speculatable".toUTF8
  | .FNATTR_Ssp => "FNATTR_Ssp".toUTF8
  | .FNATTR_Sspreq => "FNATTR_Sspreq".toUTF8
  | .FNATTR_Sspstrong => "FNATTR_Sspstrong".toUTF8
  | .FNATTR_Strictfp => "FNATTR_Strictfp".toUTF8
  | .FNATTR_Tls_load_hoist => "FNATTR_Tls_load_hoist".toUTF8
  | .FNATTR_Uwtable sync => "FNATTR_Uwtable ".toUTF8 ++ repr sync
  | .FNATTR_Nocf_check => "FNATTR_Nocf_check".toUTF8
  | .FNATTR_Shadowcallstack => "FNATTR_Shadowcallstack".toUTF8
  | .FNATTR_Mustprogress => "FNATTR_Mustprogress".toUTF8
  | .FNATTR_Vscale_range min max =>
    "(FNATTR_Denormal_fp_math32 ".toUTF8 ++ repr min ++ (max.elim ByteArray.empty repr)
      ++ ")".toUTF8
  | .FNATTR_String s => "(FNATTR_String ".toUTF8 ++ repr s ++ ")".toUTF8
  | .FNATTR_Key_value kv => "(FNATTR_Key_value ".toUTF8 ++ repr kv ++ ")".toUTF8
  | .FNATTR_Attr_grp g => "(FNATTR_Attr_grp ".toUTF8 ++ repr g ++ ")".toUTF8
  | .FNATTR_Memory l => "(FNATTR_Memory ".toUTF8 ++ repr l ++ ")".toUTF8
  | .FNATTR_UNKNOWN s => "(FNATTR_UNKNOWN ".toUTF8 ++ repr s ++ ")".toUTF8

instance reprFn_Attr : Repr fn_attr := ⟨repr_fn_attr⟩

def repr_thread_local_storage : thread_local_storage → IRString
  | .TLS_NONE => "TLS_NONE".toUTF8
  | .TLS_Localdynamic => "TLS_Localdynamic".toUTF8
  | .TLS_Initialexec => "TLS_Initialexec".toUTF8
  | .TLS_Localexec => "TLS_Localexec".toUTF8

instance reprThread_Local_Storage : Repr thread_local_storage := ⟨repr_thread_local_storage⟩

def repr_preemption_specifier : preemption_specifier → IRString
  | .PREEMPTION_Dso_preemptable => "PREEMPTION_Dso_preemptable".toUTF8
  | .PREEMPTION_Dso_local => "PREEMPTION_Dso_local".toUTF8

instance reprPremptionSpecifier : Repr preemption_specifier := ⟨repr_preemption_specifier⟩

def repr_unnamed_addr : unnamed_addr → IRString
  | .Unnamed_addr => "Unnamed_addr".toUTF8
  | .Local_Unnamed_addr => "Local_Unnamed_addr".toUTF8

instance reprUnnamedAddr : Repr unnamed_addr := ⟨repr_unnamed_addr⟩

def repr_tailcall : tailcall → IRString
  | .Tail => "Tail".toUTF8
  | .Musttail => "Musttail".toUTF8
  | .Notail => "Notail".toUTF8

instance reprTailcall : Repr tailcall := ⟨ShowAST.show_tailcall⟩

def repr_ordering : ordering → IRString
  | .Unordered => "Unordered".toUTF8
  | .Monotonic => "Monotonic".toUTF8
  | .Acquire => "Acquire".toUTF8
  | .Release => "Release".toUTF8
  | .Acq_rel => "Acq_rel".toUTF8
  | .Seq_cst => "Seq_cst".toUTF8

instance reprOrdering : Repr ordering := ⟨repr_ordering⟩

def repr_annotation : annotation typ → IRString
  | .ANN_linkage l => "ANN_linkage ".toUTF8 ++ (repr l)
  | .ANN_preemption_specifier p => "ANN_preemption_specifier ".toUTF8 ++ (repr p)
  | .ANN_visibility v => "ANN_visibility ".toUTF8 ++ (repr v)
  | .ANN_dll_storage d => "ANN_dll_storage ".toUTF8 ++ (repr d)
  | .ANN_thread_local_storage t => "ANN_thread_local_storage ".toUTF8 ++ (repr t)
  | .ANN_unnamed_addr u => "ANN_unnamed_addr ".toUTF8 ++ (repr u)
  | .ANN_addrspace n => "ANN_addrspace ".toUTF8 ++ (repr n)
  | .ANN_section s => "ANN_section ".toUTF8 ++ (repr s)
  | .ANN_partition s => "ANN_partition ".toUTF8 ++ (repr s)
  | .ANN_comdat l => "ANN_comdat ".toUTF8 ++ (repr l)
  | .ANN_align n => "ANN_align ".toUTF8 ++ (repr n)
  | .ANN_no_sanitize => "ANN_no_sanitize".toUTF8
  | .ANN_no_sanitize_address => "ANN_no_sanitize_address".toUTF8
  | .ANN_no_sanitize_hwaddress => "ANN_no_sanitize_hwaddress".toUTF8
  | .ANN_sanitize_address_dyninit => "ANN_sanitize_address_dyninit".toUTF8
  | .ANN_metadata m => "ANN_metadata ".toUTF8 ++ (repr m)
  | .ANN_cconv c => "ANN_cconv ".toUTF8 ++ (repr c)
  | .ANN_gc s => "ANN_gc ".toUTF8 ++ (repr s)
  | .ANN_prefix t => "ANN_prefix ".toUTF8 ++ (repr t)
  | .ANN_prologue t => "ANN_prologue ".toUTF8 ++ (repr t)
  | .ANN_personality t => "ANN_personality ".toUTF8 ++ (repr t)
  | .ANN_inalloca => "ANN_inalloca".toUTF8
  | .ANN_num_elements t => "ANN_num_elements ".toUTF8 ++ (repr t)
  | .ANN_volatile => "ANN_volatile".toUTF8
  | .ANN_tail t => "ANN_tail ".toUTF8 ++ (repr t)
  | .ANN_fast_math_flag f => "ANN_fast_math_flag ".toUTF8 ++ (repr f)
  | .ANN_ret_attribute r => "ANN_ret_attribute ".toUTF8 ++ (repr r)
  | .ANN_fun_attribute f => "ANN_fun_attribute ".toUTF8 ++ (repr f)
  | .ANN_atomic => "ANN_atomic".toUTF8
  | .ANN_syncscope s => "ANN_syncscope ".toUTF8 ++ (repr s)
  | .ANN_ordering o => "ANN_ordering ".toUTF8 ++ (repr o)

instance reprAnnotation : Repr (annotation typ) := ⟨repr_annotation⟩

def repr_atomic_rmw_operation : atomic_rmw_operation → IRString
  | .Axchg => "Axchg".toUTF8
  | .Aadd => "Aadd".toUTF8
  | .Asub => "Asub".toUTF8
  | .Aand => "Aand".toUTF8
  | .Anand => "Anand".toUTF8
  | .Aor => "Aor".toUTF8
  | .Axor => "Axor".toUTF8
  | .Amax => "Amax".toUTF8
  | .Amin => "Amin".toUTF8
  | .Aumax => "Aumax".toUTF8
  | .Aumin => "Aumin".toUTF8
  | .Afadd => "Afadd".toUTF8
  | .Afsub => "Afsub".toUTF8
  | .Afmax => "Afmax".toUTF8
  | .Afmin => "Afmin".toUTF8
  | .Afmaximum => "Afmaximum".toUTF8
  | .Afminimum => "Afminimum".toUTF8
  | .Auinc_wrap => "Auinc_wrap".toUTF8
  | .Audec_wrap => "Audec_wrap".toUTF8
  | .Ausub_cond => "Ausub_cond".toUTF8
  | .Ausub_sat => "Ausub_sat".toUTF8

instance reprAtomicRMWOperation : Repr atomic_rmw_operation := ⟨repr_atomic_rmw_operation⟩

def repr_atomicrmw : atomicrmw typ → IRString
  | .mk_atomicrmw a_volatile a_operation a_ptr a_val a_syncscope a_ordering a_align =>
    "(mk_atomicrmw ".toUTF8 ++ repr a_volatile ++ " ".toUTF8 ++ repr a_operation ++ " ".toUTF8
      ++ repr a_ptr ++ " ".toUTF8 ++ repr a_val ++ " ".toUTF8 ++ repr a_syncscope ++ " ".toUTF8
      ++ repr a_ordering ++ " ".toUTF8 ++ repr a_align ++ ")".toUTF8

instance reprAtomicRMW : Repr (atomicrmw typ) := ⟨repr_atomicrmw⟩

def repr_cmpxchg : cmpxchg typ → IRString
  | .mk_cmpxchg c_weak c_volatile c_ptr c_cmp c_new c_syncscope c_success_ordering c_failure_ordering c_align =>
    "(mk_cmpxchg ".toUTF8 ++ repr c_weak ++ " ".toUTF8 ++ repr c_volatile ++ " ".toUTF8
      ++ repr c_ptr ++ " ".toUTF8 ++ repr c_cmp ++ " ".toUTF8 ++ repr c_new ++ " ".toUTF8
      ++ repr c_syncscope ++ " ".toUTF8 ++ repr c_success_ordering ++ " ".toUTF8
      ++ repr c_failure_ordering ++ " ".toUTF8 ++ repr c_align ++ ")".toUTF8

instance reprCmpxchg : Repr (cmpxchg typ) := ⟨repr_cmpxchg⟩

instance reprClause : Repr (@landingpad_clause typ) where
  repr
    | .CATCH t => "(CATCH ".toUTF8 ++ repr t ++ ")".toUTF8
    | .FILTER t => "(FILTER ".toUTF8 ++ repr t ++ ")".toUTF8

instance reprOperand : Repr (@operand typ) where
  repr
    | .SSA_value t => "(SSA_value ".toUTF8 ++ (repr t) ++ ")".toUTF8
    | .Metadata_string m => "(Metadata_string ".toUTF8 ++ (repr m) ++ ")".toUTF8

instance ReprOperand_bundle : Repr (@operand_bundle typ) :=
  ⟨fun ob ↦ "(mk_operand_bundle ".toUTF8 ++ repr ob.ob_tag ++ repr ob.ob_ops ++ ")".toUTF8⟩

def repr_instr : instr typ → IRString
  | .INSTR_Comment s => "(INSTR_Comment ".toUTF8 ++ s ++ ")".toUTF8
  | .INSTR_Op e => "(INSTR_Op ".toUTF8 ++ repr e ++ ")".toUTF8
  | .INSTR_Call e params annotations obs =>
    "(INSTR_Call ".toUTF8 ++ repr e ++ " ".toUTF8 ++ repr params ++ " ".toUTF8 ++ repr annotations
      ++ repr obs ++ ")".toUTF8
  | .INSTR_Alloca t anns =>
    "(INSTR_Alloca ".toUTF8 ++ repr t ++ " ".toUTF8 ++ repr anns ++ ")".toUTF8
  | .INSTR_Load t ptr anns =>
    "(INSTR_Load ".toUTF8 ++ repr t ++ " ".toUTF8 ++ repr ptr ++ " ".toUTF8 ++ repr anns
      ++ ")".toUTF8
  | .INSTR_Store tval ptr anns =>
    "(INSTR_Store ".toUTF8 ++ repr tval ++ " ".toUTF8 ++ repr ptr ++ " ".toUTF8 ++ repr anns
      ++ ")".toUTF8
  | .INSTR_Fence str ord =>
    "(INSTR_Fence ".toUTF8 ++ «show» str ++ " ".toUTF8 ++ repr ord ++ ")".toUTF8
  | .INSTR_AtomicCmpXchg cmpx => "(INSTR_AtomicCmpXchg ".toUTF8 ++ repr cmpx ++ ")".toUTF8
  | .INSTR_AtomicRMW rmw => "(INSTR_AtomicRMW ".toUTF8 ++ repr rmw ++ ")".toUTF8
  | .INSTR_VAArg e t => "(INSTR_VAArg ".toUTF8 ++ repr e ++ " ".toUTF8 ++ repr t ++ ")".toUTF8
  | .INSTR_LandingPad t b cs =>
    "(INSTR_LandingPad ".toUTF8 ++ (repr t) ++ " ".toUTF8 ++ repr b ++ " ".toUTF8 ++ repr cs
      ++ ")".toUTF8

instance reprInstr : Repr (instr typ) := ⟨repr_instr⟩

instance reprInstrId : Repr instr_id where
  repr
    | .IId raw => ("(IId ".toUTF8 ++ repr raw ++ ")".toUTF8)
    | .IVoid n => ("(IVoid ".toUTF8 ++ repr n ++ ")".toUTF8)

instance reprTintLiteral : Repr tint_literal where
  repr
    | .TInt_Literal sz x => ("(TInt_Literal ".toUTF8 ++ repr sz ++ " ".toUTF8 ++ repr x ++ ")".toUTF8)

def repr_terminator : terminator typ → IRString
  | .TERM_Ret v => "(TERM_Ret ".toUTF8 ++ repr v ++ ")".toUTF8
  | .TERM_Ret_void => "TERM_Ret_void".toUTF8
  | .TERM_Br te b1 b2 =>
    "(TERM_Br ".toUTF8 ++ repr te ++ " ".toUTF8 ++ repr b1 ++ " ".toUTF8 ++ repr b2 ++ ")".toUTF8
  | .TERM_Br_1 b => "(TERM_Br_1 ".toUTF8 ++ repr b ++ ")".toUTF8
  | .TERM_Switch v dest brs =>
    "(TERM_Switch ".toUTF8 ++ repr v ++ " ".toUTF8 ++ repr dest ++ repr brs ++ ")".toUTF8
  | .TERM_IndirectBr v brs func =>
    "(TERM_IndirectBr ".toUTF8 ++ repr v ++ " ".toUTF8 ++ repr brs ++ " ".toUTF8 ++ repr func
      ++ ")".toUTF8
  | .TERM_Resume v => "(TERM_Resume ".toUTF8 ++ repr v ++ ")".toUTF8
  | .TERM_Invoke fnptrval args to_label unwind_label anns obs =>
    "(TERM_Invoke ".toUTF8 ++ repr fnptrval ++ " ".toUTF8 ++ repr args ++ " ".toUTF8
      ++ repr to_label ++ " ".toUTF8 ++ repr unwind_label ++ repr anns ++ repr obs ++ ")".toUTF8
  | .TERM_Unreachable => "TERM_Unreachable".toUTF8

instance reprTerminator : Repr (terminator typ) := ⟨repr_terminator⟩

def repr_phi : phi typ → IRString
  | .Phi fm t args =>
    "(Phi [".toUTF8 ++ contents repr_fast_math fm ++ "] ".toUTF8 ++ repr t ++ repr args
      ++ ")".toUTF8

instance reprPhi : Repr (phi typ) := ⟨repr_phi⟩

def repr_block : block typ → IRString
  | .mk_block blk_id blk_phis blk_code blk_term blk_comments =>
    "(mk_block ".toUTF8 ++ repr blk_id ++ " ".toUTF8 ++ repr blk_phis ++ " ".toUTF8
      ++ repr blk_code ++ " ".toUTF8 ++ repr blk_term ++ " ".toUTF8 ++ repr blk_comments
      ++ ")".toUTF8

instance reprBlock : Repr (block typ) := ⟨repr_block⟩

def repr_declaration : declaration typ → IRString
  | .mk_declaration dc_name dc_type dc_param_attrs dc_attrs dc_annotations =>
    "(mk_declaration ".toUTF8 ++ repr dc_name ++ " ".toUTF8 ++ repr dc_type ++ " ".toUTF8
      ++ repr dc_param_attrs ++ " ".toUTF8 ++ repr dc_attrs ++ " ".toUTF8 ++ repr dc_annotations
      ++ ")".toUTF8

instance reprDeclaration : Repr (declaration typ) := ⟨repr_declaration⟩

def repr_definition : definition typ (block typ × List (block typ)) → IRString
  | .mk_definition df_prototype df_args df_instrs =>
    "(mk_definition ".toUTF8 ++ repr df_prototype ++ " ".toUTF8 ++ repr df_args ++ " ".toUTF8
      ++ repr df_instrs ++ ")".toUTF8

instance reprDefinition : Repr (definition typ (block typ × List (block typ))) := ⟨repr_definition⟩

def repr_global : «global» typ → IRString
  | .mk_global g_ident g_typ g_constant g_exp g_externally_initialized g_alias g_annotations =>
    "(mk_global ".toUTF8 ++ repr g_ident ++ " ".toUTF8 ++ repr g_typ ++ " ".toUTF8
      ++ repr g_constant ++ " ".toUTF8 ++ repr g_exp ++ " ".toUTF8
      ++ repr g_externally_initialized ++ " ".toUTF8 ++ repr g_alias ++ " ".toUTF8
      ++ repr g_annotations ++ ")".toUTF8

instance reprGlobal : Repr («global» typ) := ⟨repr_global⟩

def repr_tle : toplevel_entity typ (block typ × List (block typ)) → IRString
  | .TLE_Comment msg => "(TLE_Comment ".toUTF8 ++ repr msg ++ ")".toUTF8
  | .TLE_Target tgt => "(TLE_Target ".toUTF8 ++ repr tgt ++ ")".toUTF8
  | .TLE_Datalayout layout => "(TLE_Datalayout ".toUTF8 ++ repr layout ++ ")".toUTF8
  | .TLE_Declaration decl => "(TLE_Declaration ".toUTF8 ++ repr decl ++ ")".toUTF8
  | .TLE_Definition defn => "(TLE_Definition ".toUTF8 ++ repr defn ++ ")".toUTF8
  | .TLE_Type_decl id t =>
    "(TLE_Type_decl ".toUTF8 ++ repr id ++ " ".toUTF8 ++ repr t ++ ")".toUTF8
  | .TLE_Source_filename s => "(TLE_Source_filename ".toUTF8 ++ repr s ++ ")".toUTF8
  | .TLE_Global g => "(TLE_Global ".toUTF8 ++ repr g ++ ")".toUTF8
  | .TLE_Metadata id b md =>
    "(TLE_Metadata ".toUTF8 ++ repr id ++ " ".toUTF8 ++ repr b ++ " ".toUTF8 ++ repr md
      ++ ")".toUTF8
  | .TLE_Attribute_group i attrs =>
    "(TLE_Attribute_group ".toUTF8 ++ repr i ++ " ".toUTF8 ++ repr attrs ++ ")".toUTF8

instance reprTLE : Repr (toplevel_entity typ (block typ × List (block typ))) := ⟨repr_tle⟩

end Vellvm.Syntax.ReprAST
