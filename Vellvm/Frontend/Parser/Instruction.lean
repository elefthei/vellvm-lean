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

public import Vellvm.Frontend.Parser.Expr

public section
namespace Vellvm.Frontend.Parser
open Vellvm.Syntax.LLVMAst

private def withInstrMetadata (p : P α) : P (α × List (metadata typ)) := do
  -- Menhir's first symbol for a call is `tailcall?`: its empty production starts at `$endpos($0)`.
  let start ← if isFixed (← peek) .KW_CALL then pure (← get).lastEnd else startPos
  let node ← p
  let md ← parseInstrMetadata
  return (node, (← fileMetadata start) :: md)

-- Leave the comma for instr_metadata unless it introduces this production.
private def eatCommaBefore (starts : Token → Bool) : P Bool := do
  unless isFixed (← peek) .COMMA do return false
  unless starts (← peekNext) do return false
  discard pop
  return true

private def parsePhiEntry : P (block_id × exp typ) := do
  expect .LSQUARE
  let v ← parseExp
  expect .COMMA
  let b ← localId
  expect .RSQUARE
  return (b, v)

def parsePhi : P (phi typ × List (metadata typ)) := withInstrMetadata do
  expect .KW_PHI
  let fm ← parseFastMath
  let t ← parseTyp
  let mut rev := [← parsePhiEntry]
  while ← eatCommaBefore (isFixed · .LSQUARE) do rev := (← parsePhiEntry) :: rev
  return .Phi fm t rev.reverse

private def takeKeyword? (f : FixedToken → Option α) : P (Option α) := do
  let .fixed k ← peek | return none
  let a := f k
  if a.isSome then discard pop
  return a

private def parseTail? : P (Option (annotation typ)) := takeKeyword? fun
  | .KW_TAIL => some (.ANN_tail .Tail)
  | .KW_MUSTTAIL => some (.ANN_tail .Musttail)
  | .KW_NOTAIL => some (.ANN_tail .Notail)
  | _ => none

private def parseOrdering? : P (Option ordering) := takeKeyword? fun
  | .KW_UNORDERED => some .Unordered
  | .KW_MONOTONIC => some .Monotonic
  | .KW_ACQUIRE => some .Acquire
  | .KW_RELEASE => some .Release
  | .KW_ACQ_REL => some .Acq_rel
  | .KW_SEQ_CST => some .Seq_cst
  | _ => none

private def parseOrdering : P ordering := do
  let some o ← parseOrdering? | syntaxError
  return o

private def parseRmwOp : P atomic_rmw_operation := do
  let some op ← takeKeyword? (fun
    | .KW_XCHG => some Axchg
    | .KW_ADD => some Aadd
    | .KW_SUB => some Asub
    | .KW_AND => some Aand
    | .KW_NAND => some Anand
    | .KW_OR => some Aor
    | .KW_XOR => some Axor
    | .KW_MAX => some Amax
    | .KW_MIN => some Amin
    | .KW_UMAX => some Aumax
    | .KW_UMIN => some Aumin
    | .KW_FADD => some Afadd
    | .KW_FSUB => some Afsub
    | .KW_FMAX => some Afmax
    | .KW_FMIN => some Afmin
    | .KW_FMAXIMUM => some Afmaximum
    | .KW_FMINIMUM => some Afminimum
    | .KW_UINC_WRAP => some Auinc_wrap
    | .KW_UDEC_WRAP => some Audec_wrap
    | .KW_USUB_COND => some Ausub_cond
    | .KW_USUB_SAT => some Ausub_sat
    | _ => none) | syntaxError
  return op

private def parseSyncscope? : P (Option IRString) := do
  unless ← eat .KW_SYNCSCOPE do return none
  return some (← withParens parseString)

private def parseCommaAlign? : P (Option int_syntax) := do
  unless ← eatCommaBefore (isFixed · .KW_ALIGN) do return none
  expect .KW_ALIGN
  return some (← parseInteger)

-- Only void followed by a parameter list begins a typ; bare void is a separate production.
private def eatBareVoid : P Bool := do
  unless isFixed (← peek) .KW_VOID do return false
  if isFixed (← peekNext) .LPAREN then return false
  discard pop
  return true

private def parseCallExp : P (texp typ) := do
  if ← eatBareVoid then return (.TYPE_Void, ← parseExp)
  parseTExp

private abbrev CallArg := texp typ × List param_attr

private def parseTypedCallArg : P CallArg := do
  let t ← parseNonMetadataType
  let attrs ← parseParams
  return ((t, ← parseExp), attrs)

private def parseCallArg : P CallArg := do
  -- metadata* is a (non-metadata) pointer type, not a metadata argument prefix.
  if isFixed (← peek) .KW_METADATA then
    unless isFixed (← peekNext) .STAR do
      discard pop
      if startsMetadata (← peek) then
        return ((.TYPE_Metadata, .EXP_Metadata (← parseMetadataValue)), [])
      let (tv, attrs) ← parseTypedCallArg
      return ((.TYPE_Metadata, .EXP_Metadata (.METADATA_Const tv)), attrs)
  parseTypedCallArg

private def parseOperand : P (@operand typ) := do
  if let .STRING s ← peek then
    discard pop
    return .Metadata_string (.METADATA_Id (.Name s))
  return .SSA_value (← parseTExp)

private def parseBundle : P (@operand_bundle typ) := do
  let tag ← parseString
  expect .LPAREN
  return ⟨tag, ← parseSep .RPAREN parseOperand⟩

private def parseCallParts (tailAttr : Option (annotation typ)) (testOnly : Bool) :
    P (texp typ × List CallArg × List (annotation typ) × List (@operand_bundle typ)) := do
  let fm ← parseFastMath
  let cc ← parseCconv?
  let ra ← parseParams
  let addr ← parseAddrspace?
  let f ← if testOnly then parseTExp else parseCallExp
  expect .LPAREN
  let args ← parseSep .RPAREN parseCallArg
  let fa ← parseFnAttrs
  let bundles ← if testOnly then pure [] else do
    if ← eat .LSQUARE then parseSep .RSQUARE parseBundle else pure []
  let mut anns := fa.map (ANN_fun_attribute (T := typ))
  if let some a := addr then anns := a :: anns
  anns := ra.foldr (fun a acc ↦ ANN_ret_attribute a :: acc) anns
  if let some c := cc then anns := c :: anns
  anns := fm.foldr (fun flag acc ↦ ANN_fast_math_flag flag :: acc) anns
  if let some a := tailAttr then anns := a :: anns
  return (f, args, anns, bundles)

private def parseCall (testOnly : Bool) : P (instr typ) := do
  let tailAttr ← parseTail?
  expect .KW_CALL
  let (f, args, anns, bundles) ← parseCallParts tailAttr testOnly
  return .INSTR_Call f args anns bundles

def parseTestCall : P (instr typ) := do
  let call ← parseCall true
  expect .EOF
  return call

private def parseAlloca : P (instr typ) := do
  let ia ← eat .KW_INALLOCA
  let t ← parseTyp
  let mut rev := if ia then [ANN_inalloca (T := typ)] else []
  if ← eatCommaBefore startsTyp then rev := ANN_num_elements (← parseTExp) :: rev
  if let some n ← parseCommaAlign? then rev := ANN_align n :: rev
  if ← eatCommaBefore (isFixed · .KW_ADDRSPACE) then
    let some a ← parseAddrspace? | syntaxError
    rev := a :: rev
  return .INSTR_Alloca t rev.reverse

private def parseLoadStore (load : Bool) : P (instr typ) := do
  let atomic ← eat .KW_ATOMIC
  let vol ← eat .KW_VOLATILE
  let t ← parseTyp
  let val ← if load then pure none else some <$> parseExp
  expect .COMMA
  let ptr ← parseTExp
  let scope ← parseSyncscope?
  let order ← parseOrdering?
  let align ← parseCommaAlign?
  let mut anns := align.elim [] (fun n ↦ [ANN_align (T := typ) n])
  if let some o := order then anns := ANN_ordering o :: anns
  if let some s := scope then anns := ANN_syncscope s :: anns
  if vol then anns := ANN_volatile :: anns
  if atomic then anns := ANN_atomic :: anns
  return match val with
    | none => .INSTR_Load t ptr anns
    | some v => .INSTR_Store (t, v) ptr anns

private def unitFlag (k : FixedToken) : P (Option Unit) := do
  return if ← eat k then some () else none

private def parseCmpXchg : P (instr typ) := do
  let weak ← unitFlag .KW_WEAK
  let vol ← unitFlag .KW_VOLATILE
  let ptr ← parseTExp
  expect .COMMA
  let cmp ← parseTExp
  expect .COMMA
  let val ← parseTExp
  let scope ← parseSyncscope?
  let success ← parseOrdering
  let failOrder ← parseOrdering
  return .INSTR_AtomicCmpXchg ⟨weak, vol, ptr, cmp, val, scope, success, failOrder, ← parseCommaAlign?⟩

private def parseRmw : P (instr typ) := do
  let vol ← unitFlag .KW_VOLATILE
  let op ← parseRmwOp
  let ptr ← parseTExp
  expect .COMMA
  let val ← parseTExp
  let scope ← parseSyncscope?
  let order ← parseOrdering
  return .INSTR_AtomicRMW ⟨vol, op, ptr, val, scope, order, ← parseCommaAlign?⟩

private def parseLandingPad : P (instr typ) := do
  let t ← parseTyp
  let cleanup ← eat .KW_CLEANUP
  let mut clauses : List (@landingpad_clause typ) := []
  repeat
    let isCatch ← eat .KW_CATCH
    unless isCatch do
      unless ← eat .KW_FILTER do break
    let ty ← parseTyp
    let v ← parseExprVal
    clauses := (if isCatch then CATCH (ty, v) else FILTER (ty, v)) :: clauses
  if !cleanup && clauses.isEmpty then syntaxError
  return .INSTR_LandingPad t cleanup clauses.reverse

def parseInstr : P (instr typ × List (metadata typ)) := withInstrMetadata do
  match ← peek with
  | .fixed .KW_CALL | .fixed .KW_TAIL | .fixed .KW_MUSTTAIL | .fixed .KW_NOTAIL => parseCall false
  | .fixed .KW_ALLOCA => discard pop; parseAlloca
  | .fixed .KW_LOAD => discard pop; parseLoadStore true
  | .fixed .KW_STORE => discard pop; parseLoadStore false
  | .fixed .KW_ATOMICCMPXCHG => discard pop; parseCmpXchg
  | .fixed .KW_ATOMICRMW => discard pop; parseRmw
  | .fixed .KW_LANDINGPAD => discard pop; parseLandingPad
  | .fixed .KW_VAARG =>
    discard pop
    let tv ← parseTExp
    expect .COMMA
    return .INSTR_VAArg tv (← parseTyp)
  | .fixed .KW_FENCE =>
    discard pop
    return .INSTR_Fence (← parseSyncscope?) (← parseOrdering)
  | _ => return .INSTR_Op (← parseInstrOp)

private def parseBranchLabel : P block_id := do
  expect .KW_LABEL
  localId

private def parseSwitchCase : P int_syntax := do
  if ← eat .KW_TRUE then return .IntDecimal (.Pos (.D1 .Nil))
  if ← eat .KW_FALSE then return .IntDecimal (.Pos (.D0 .Nil))
  parseInteger

private def parseSwitchTable : P (List (tint_literal × block_id)) := do
  expect .LSQUARE
  let mut rev := []
  while !(← eat .RSQUARE) do
    let .I sz ← peek | syntaxError
    discard pop
    let n ← parseSwitchCase
    expect .COMMA
    rev := (TInt_Literal sz n, ← parseBranchLabel) :: rev
  return rev.reverse

def startsTerm : Token → Bool
  | .fixed .KW_RET | .fixed .KW_BR | .fixed .KW_SWITCH | .fixed .KW_INDIRECTBR
  | .fixed .KW_RESUME | .fixed .KW_INVOKE | .fixed .KW_UNREACHABLE => true
  | _ => false

def parseTerm : P (terminator typ × List (metadata typ)) := withInstrMetadata do
  match ← peek with
  | .fixed .KW_RET =>
    discard pop
    if ← eatBareVoid then return .TERM_Ret_void
    return .TERM_Ret (← parseTExp)
  | .fixed .KW_BR =>
    discard pop
    if isFixed (← peek) .KW_LABEL then return .TERM_Br_1 (← parseBranchLabel)
    let c ← parseTExp
    expect .COMMA
    let b1 ← parseBranchLabel
    expect .COMMA
    return .TERM_Br c b1 (← parseBranchLabel)
  | .fixed .KW_SWITCH =>
    discard pop
    let c ← parseTExp
    expect .COMMA
    let dest ← parseBranchLabel
    return .TERM_Switch c dest (← parseSwitchTable)
  | .fixed .KW_INDIRECTBR =>
    discard pop
    let tv ← parseTExp
    expect .COMMA
    expect .LSQUARE
    return .TERM_IndirectBr tv (← parseSep .RSQUARE parseBranchLabel) none
  | .fixed .KW_RESUME => discard pop; return .TERM_Resume (← parseTExp)
  | .fixed .KW_INVOKE =>
    discard pop
    let (f, args, anns, bundles) ← parseCallParts none false
    expect .KW_TO
    let b1 ← parseBranchLabel
    expect .KW_UNWIND
    return .TERM_Invoke f args b1 (← parseBranchLabel) anns bundles
  | .fixed .KW_UNREACHABLE => discard pop; return .TERM_Unreachable
  | _ => syntaxError

end Vellvm.Frontend.Parser
