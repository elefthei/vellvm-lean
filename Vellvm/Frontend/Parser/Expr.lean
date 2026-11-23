/-
Copyright (c) 2012 Raphaël Proust <raphlalou@gmail.com>
Copyright (c) 2012 INRIA - Raphaël Proust <raphlalou@gmail.com>
Copyright (c) 2012 ENS - Raphaël Proust <raphlalou@gmail.com>
Copyright (c) 2014 OCamlPro - Julien Sagot <ju.sagot@gmail.com>
Copyright (c) 2026 U. Penn. Steve Zdancewic <stevez@cis.upenn.edu>

Permission to use, copy, modify, and distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
Adapted for use in Vellvm by Steve Zdancewic (c) 2017.
-/
module

public import Vellvm.Frontend.Parser.Types

public section
namespace Vellvm.Frontend.Parser
open Vellvm.Syntax.LLVMAst

private def readPredicate (decode : FixedToken → Option α) : P α := do
  let .fixed k ← peek | syntaxError
  let some result := decode k | syntaxError
  discard pop
  return result

private def parseICmp : P icmp := readPredicate fun
  | .KW_EQ => some .Eq
  | .KW_NE => some .Ne
  | .KW_UGT => some .Ugt
  | .KW_UGE => some .Uge
  | .KW_ULT => some .Ult
  | .KW_ULE => some .Ule
  | .KW_SGT => some .Sgt
  | .KW_SGE => some .Sge
  | .KW_SLT => some .Slt
  | .KW_SLE => some .Sle
  | _ => none

private def parseFCmp : P fcmp := readPredicate fun
  | .KW_FALSE => some .FFalse
  | .KW_OEQ => some .FOeq
  | .KW_OGT => some .FOgt
  | .KW_OGE => some .FOge
  | .KW_OLT => some .FOlt
  | .KW_OLE => some .FOle
  | .KW_ONE => some .FOne
  | .KW_ORD => some .FOrd
  | .KW_UNO => some .FUno
  | .KW_UEQ => some .FUeq
  | .KW_UGT => some .FUgt
  | .KW_UGE => some .FUge
  | .KW_ULT => some .FUlt
  | .KW_ULE => some .FUle
  | .KW_UNE => some .FUne
  | .KW_TRUE => some .FTrue
  | _ => none

def parseFastMath : P (List fast_math) := do
  let mut rev := []
  repeat
    let flag : fast_math ← match ← peek with
      | .fixed .KW_NNAN => pure .Nnan
      | .fixed .KW_NINF => pure .Ninf
      | .fixed .KW_NSZ => pure .Nsz
      | .fixed .KW_ARCP => pure .Arcp
      | .fixed .KW_CONTRACT => pure .Contract
      | .fixed .KW_AFN => pure .Afn
      | .fixed .KW_REASSOC => pure .Reassoc
      | .fixed .KW_FAST => pure .Fast
      | _ => break
    discard pop
    rev := flag :: rev
  return rev.reverse

private def noWrap (mk : Bool → Bool → α) : P α := do
  if ← eat .KW_NUW then return mk true (← eat .KW_NSW)
  if ← eat .KW_NSW then return mk (← eat .KW_NUW) true
  return mk false false

private def parseGepFlags : P gep_flags := do
  let mut flags := gep_no_flags
  repeat
    match ← peek with
    | .fixed .KW_INBOUNDS => flags := { flags with gep_inbounds := true }
    | .fixed .KW_NUSW => flags := { flags with gep_nusw := true }
    | .fixed .KW_NUW => flags := { flags with gep_nuw := true }
    | _ => break
    discard pop
  return flags

private def typed (value : P (exp typ)) : P (texp typ) := return (← parseTyp, ← value)

/-- A comma before instruction metadata belongs to `instr_metadata`, not to the index path. -/
private def commaPath (starts : Token → Bool) (p : P α) : P (List α) := do
  let mut rev := []
  while isFixed (← peek) .COMMA do
    unless starts (← peekNext) do break
    discard pop
    rev := (← p) :: rev
  return rev.reverse

private def parseIndices (constant : Bool) : P (List int_syntax) := do
  if constant then
    expect .COMMA
    parseSep1 parseInteger
  else
    commaPath (fun | .INTEGER _ => true | _ => false) parseInteger

private def parseOperation (constant : Bool) (value : P (exp typ)) : P (exp typ) := do
  let tv := typed value
  let nextTV := expect .COMMA *> tv
  let operands (p : P (exp typ)) := if constant then withParens p else p
  let instrFlags := if constant then pure [] else parseFastMath
  let binary (op : P (typ → exp typ → exp typ → exp typ)) : P (exp typ) := do
    discard pop
    let mk ← op
    operands do
      let (t, x) ← tv
      expect .COMMA
      if constant then discard parseTyp
      return mk t x (← value)
  let integer (op : P ibinop) := binary do return exp.OP_IBinop (← op)
  let floating (op : fbinop) := binary do return exp.OP_FBinop op (← parseFastMath)
  let cast (op : P conversion_type) : P (exp typ) := do
    discard pop
    let c ← op
    operands do
      let (t, x) ← tv
      expect .KW_TO
      return .OP_Conversion c t x (← parseTyp)
  let pureCast (op : P pure_conversion) := cast do return .CONV_Pure (← op)
  let .fixed k ← peek | syntaxError
  match k with
  | .KW_ADD => integer (noWrap .Add)
  | .KW_SUB => integer (noWrap .Sub)
  | .KW_MUL => integer (noWrap .Mul)
  | .KW_SHL => integer (noWrap .Shl)
  | .KW_UDIV => integer (.UDiv <$> eat .KW_EXACT)
  | .KW_SDIV => integer (.SDiv <$> eat .KW_EXACT)
  | .KW_LSHR => integer (.LShr <$> eat .KW_EXACT)
  | .KW_ASHR => integer (.AShr <$> eat .KW_EXACT)
  | .KW_UREM => integer (pure .URem)
  | .KW_SREM => integer (pure .SRem)
  | .KW_AND => integer (pure .And)
  | .KW_OR => integer (.Or <$> eat .KW_DISJOINT)
  | .KW_XOR => integer (pure .Xor)
  | .KW_ICMP => binary do return exp.OP_ICmp (← eat .KW_SAMESIGN) (← parseICmp)
  | .KW_FADD => floating .FAdd
  | .KW_FSUB => floating .FSub
  | .KW_FMUL => floating .FMul
  | .KW_FDIV => floating .FDiv
  | .KW_FREM => floating .FRem
  | .KW_FNEG =>
    discard pop
    return .OP_Fneg (← parseFastMath) (← tv)
  | .KW_FCMP => binary do
    let flags ← instrFlags
    return exp.OP_FCmp (← parseFCmp) flags
  | .KW_TRUNC => pureCast (noWrap .Trunc)
  | .KW_ZEXT => pureCast (.Zext <$> eat .KW_NNEG)
  | .KW_SEXT => pureCast (pure .Sext)
  | .KW_FPTRUNC => pureCast (.Fptrunc <$> parseFastMath)
  | .KW_FPEXT => pureCast (.Fpext <$> parseFastMath)
  | .KW_UITOFP => pureCast (.Uitofp <$> eat .KW_NNEG)
  | .KW_SITOFP => pureCast (pure .Sitofp)
  | .KW_FPTOUI => pureCast (pure .Fptoui)
  | .KW_FPTOSI => pureCast (pure .Fptosi)
  | .KW_BITCAST => cast (pure .CONV_Bitcast)
  | .KW_INTTOPTR => cast (pure (.CONV_Impure .Inttoptr))
  | .KW_PTRTOINT => cast (pure (.CONV_Impure .Ptrtoint))
  | .KW_PTRTOADDR => cast (pure (.CONV_Impure .Ptrtoaddr))
  | .KW_ADDRSPACECAST => cast (pure (.CONV_Impure .Addrspacecast))
  | .KW_GETELEMENTPTR =>
    discard pop
    let flags ← parseGepFlags
    operands do
      let t ← parseTyp
      let ptr ← nextTV
      let idx ← if constant then do
          if ← eat .COMMA then parseSep1 tv else pure []
        else commaPath startsTyp tv
      return .OP_GetElementPtr flags t ptr idx
  | .KW_SELECT =>
    discard pop
    let flags ← instrFlags
    operands do return .OP_Select flags (← tv) (← nextTV) (← nextTV)
  | .KW_FREEZE => discard pop; operands do return .OP_Freeze (← tv)
  | .KW_EXTRACTELEMENT => discard pop; operands do return .OP_ExtractElement (← tv) (← nextTV)
  | .KW_INSERTELEMENT =>
    discard pop
    operands do return .OP_InsertElement (← tv) (← nextTV) (← nextTV)
  | .KW_SHUFFLEVECTOR =>
    discard pop
    operands do return .OP_ShuffleVector (← tv) (← nextTV) (← nextTV)
  | .KW_EXTRACTVALUE =>
    discard pop
    operands do return .OP_ExtractValue (← tv) (← parseIndices constant)
  | .KW_INSERTVALUE =>
    discard pop
    operands do return .OP_InsertValue (← tv) (← nextTV) (← parseIndices constant)
  | _ => syntaxError

def startsMetadata : Token → Bool
  | .fixed .BANG | .METADATA_DEBUG .. | .METADATA_NAME _ => true
  | _ => false

def parseMetadataId : P (metadata typ) := do
  match ← peek with
  | .STRING s => discard pop; return .METADATA_Id (.Name (quoteBytes s))
  | .INTEGER n => discard pop; return .METADATA_Id (.Anon n.toInt)
  | _ => syntaxError

def parseBangMetadataId : P (metadata typ) := do
  if ← eat .BANG then return ← parseMetadataId
  let .METADATA_NAME s ← peek | syntaxError
  discard pop
  return .METADATA_Id (.Name s)

private def parseDebug : P (metadata typ) := do
  let .METADATA_DEBUG tag body ← peek | syntaxError
  discard pop
  return .METADATA_Debug tag body

private def cstringElts (s : IRString) : List (texp typ) := go s.size []
where
  go : Nat → List (texp typ) → List (texp typ)
    | 0, acc => acc
    | i + 1, acc => go i (byteToI8 s[i]! :: acc)

mutual
  private partial def expression (allowOp : Bool) : P (exp typ) := do
    match ← peek with
    | .INTEGER n => discard pop; return .EXP_Integer n
    | .FLOAT f => discard pop; return .EXP_Float f
    | .fixed .KW_TRUE => discard pop; return .EXP_Bool true
    | .fixed .KW_FALSE => discard pop; return .EXP_Bool false
    | .fixed .KW_NULL => discard pop; return .EXP_Null
    | .fixed .KW_UNDEF => discard pop; return .EXP_Undef
    | .fixed .KW_POISON => discard pop; return .EXP_Poison
    | .fixed .KW_ZEROINITIALIZER => discard pop; return .EXP_Zero_initializer
    | .GLOBAL i => discard pop; return .EXP_Ident (.ID_Global (rawId i))
    | .LOCAL i => discard pop; return .EXP_Ident (.ID_Local (rawId i))
    | .fixed .KW_BLOCKADDRESS =>
      discard pop
      withParens do
        let fn ← globalId
        expect .COMMA
        return .EXP_BlockAddress fn (← localId)
    | .fixed .LCURLY =>
      discard pop; return .EXP_Struct (← parseSep .RCURLY (typed (expression true)))
    | .fixed .LTLCURLY =>
      discard pop; return .EXP_Packed_struct (← parseSep .RCURLYGT (typed (expression true)))
    | .fixed .LSQUARE =>
      discard pop; return .EXP_Array (← parseSep .RSQUARE (typed (expression true)))
    | .fixed .LT =>
      discard pop; return .EXP_Vector (← parseSep .GT (typed (expression true)))
    | .fixed .KW_C => discard pop; return .EXP_Cstring (cstringElts (unescape (← parseString)))
    | .fixed .KW_ASM =>
      discard pop
      let se ← eat .KW_SIDEEFFECT
      let al ← eat .KW_ALIGNSTACK
      let id ← eat .KW_INTELDIALECT
      let uw ← eat .KW_UNWIND
      let template ← parseString
      expect .COMMA
      return .EXP_Asm se al id uw template (← parseString)
    | .fixed .KW_SPLAT => discard pop; return .EXP_Splat (← withParens (typed (expression true)))
    | t =>
      if startsMetadata t then return .EXP_Metadata (← parseMetadataValue)
      if allowOp then parseOperation true (expression true) else syntaxError

  partial def parseMetadataValue : P (metadata typ) := do
    match ← peek with
    | .fixed .BANG =>
      discard pop
      if isFixed (← peek) .LCURLY then parseMetadataNode else parseMetadataId
    | .METADATA_NAME _ => parseBangMetadataId
    | .METADATA_DEBUG .. => parseDebug
    | _ => syntaxError

  private partial def parseMetadataNode : P (metadata typ) := do
    expect .LCURLY
    let fields ← parseSep .RCURLY do
      if ← eat .KW_NULL then return .METADATA_Null
      if startsMetadata (← peek) then return ← parseMetadataValue
      return .METADATA_Const (← typed (expression true))
    return .METADATA_Node fields
end

def parseExp : P (exp typ) := expression true

def parseExprVal : P (exp typ) := expression false

def parseTExp : P (texp typ) := typed parseExp

def parseInstrOp : P (exp typ) := parseOperation false parseExp

def parseTleMetadata : P (metadata typ) := do
  match ← peek with
  | .fixed .BANG | .fixed .KW_METADATA => discard pop; parseMetadataNode
  | .METADATA_DEBUG .. => parseDebug
  | _ => syntaxError

def parseInstrMetadata : P (List (metadata typ)) := do
  let mut rev := []
  while ← eat .COMMA do
    let first ← parseMetadataValue
    let second ← parseMetadataValue
    rev := .METADATA_Pair first second :: rev
  return rev.reverse

end Vellvm.Frontend.Parser
