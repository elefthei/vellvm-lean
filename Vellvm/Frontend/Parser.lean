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

public import Vellvm.Frontend.Parser.Instruction
import Vellvm.Syntax.AstLib

public section
namespace Vellvm.Frontend.Parser
open Vellvm.Syntax.LLVMAst

abbrev FnBody := block typ × List (block typ)
abbrev Entity := toplevel_entity typ FnBody
private abbrev Ann := annotation typ

private def parseLinkage? : P (Option linkage) := do
  let x := match ← peek with
    | .fixed .KW_PRIVATE => some LINKAGE_Private
    | .fixed .KW_INTERNAL => some LINKAGE_Internal
    | .fixed .KW_AVAILABLE_EXTERNALLY => some LINKAGE_Available_externally
    | .fixed .KW_LINKONCE => some LINKAGE_Linkonce
    | .fixed .KW_WEAK => some LINKAGE_Weak
    | .fixed .KW_COMMON => some LINKAGE_Common
    | .fixed .KW_APPENDING => some LINKAGE_Appending
    | .fixed .KW_EXTERN_WEAK => some LINKAGE_Extern_weak
    | .fixed .KW_LINKONCE_ODR => some LINKAGE_Linkonce_odr
    | .fixed .KW_WEAK_ODR => some LINKAGE_Weak_odr
    | .fixed .KW_EXTERNAL => some LINKAGE_External
    | _ => none
  if x.isSome then discard pop
  return x

private def preemption? : P (Option Ann) := do
  if ← eat .KW_DSO_PREEMPTABLE then return some (.ANN_preemption_specifier .PREEMPTION_Dso_preemptable)
  if ← eat .KW_DSO_LOCAL then return some (.ANN_preemption_specifier .PREEMPTION_Dso_local)
  return none

private def visibility? : P (Option Ann) := do
  if ← eat .KW_DEFAULT then return some (.ANN_visibility .VISIBILITY_Default)
  if ← eat .KW_HIDDEN then return some (.ANN_visibility .VISIBILITY_Hidden)
  if ← eat .KW_PROTECTED then return some (.ANN_visibility .VISIBILITY_Protected)
  return none

private def dll? : P (Option Ann) := do
  if ← eat .KW_DLLIMPORT then return some (.ANN_dll_storage .DLLSTORAGE_Dllimport)
  if ← eat .KW_DLLEXPORT then return some (.ANN_dll_storage .DLLSTORAGE_Dllexport)
  return none

private def tls? : P (Option Ann) := do
  unless ← eat .KW_THREAD_LOCAL do return none
  unless ← eat .LPAREN do return some (.ANN_thread_local_storage .TLS_NONE)
  let t ← match ← peek with
    | .fixed .KW_LOCALDYNAMIC => pure TLS_Localdynamic
    | .fixed .KW_INITIALEXEC => pure TLS_Initialexec
    | .fixed .KW_LOCALEXEC => pure TLS_Localexec
    | _ => syntaxError
  discard pop; expect .RPAREN
  return some (.ANN_thread_local_storage t)

private def unnamed? : P (Option Ann) := do
  if ← eat .KW_UNNAMED_ADDR then return some (.ANN_unnamed_addr .Unnamed_addr)
  if ← eat .KW_LOCAL_UNNAMED_ADDR then return some (.ANN_unnamed_addr .Local_Unnamed_addr)
  return none

private def optionalKw (k : FixedToken) (p : P α) : P (Option α) := do
  if ← eat k then return some (← p)
  return none

private def metadataAnn : P Ann := do
  return .ANN_metadata [← parseBangMetadataId, ← parseMetadataValue]

private def startsBangId : Token → Bool
  | .fixed .BANG | .METADATA_NAME _ => true
  | _ => false

/-- Post-initializer annotations each occur in a fixed position, except metadata which repeats. -/
private def globalPost : P (List Ann) := do
  let mut rank := 0
  let mut rev := []
  while ← eat .COMMA do
    let (n, parseAnn) : Nat × P Ann ← match ← peek with
      | .fixed .KW_SECTION => pure (1, .ANN_section <$> (pop *> parseString))
      | .fixed .KW_PARTITION => pure (2, .ANN_partition <$> (pop *> parseString))
      | .fixed .KW_COMDAT => pure (3, .ANN_comdat <$> (pop *> withParens localId))
      | .fixed .KW_ALIGN => pure (4, .ANN_align <$> (pop *> parseInteger))
      | .fixed .KW_NO_SANITIZE => pure (5, pop *> pure .ANN_no_sanitize)
      | .fixed .KW_NO_SANITIZE_ADDRESS => pure (6, pop *> pure .ANN_no_sanitize_address)
      | .fixed .KW_NO_SANITIZE_HWADDRESS => pure (7, pop *> pure .ANN_no_sanitize_hwaddress)
      | .fixed .KW_SANITIZE_ADDRESS_DYNINIT => pure (8, pop *> pure .ANN_sanitize_address_dyninit)
      | _ => pure (9, metadataAnn)
    if n < rank || (n == rank && n != 9) then syntaxError
    rank := n
    rev := (← parseAnn) :: rev
  return rev.reverse

private def globalDecl : P Entity := do
  let id ← globalId
  expect .EQ
  let l ← parseLinkage?
  let anns : List Ann := [(l.map ANN_linkage), ← preemption?, ← visibility?, ← dll?,
    ← tls?, ← unnamed?, ← parseAddrspace?].reduceOption
  let external := match l with
    | some .LINKAGE_Extern_weak | some .LINKAGE_External => true
    | _ => false
  if !external && (← eat .KW_ALIAS) then
    let t ← parseTyp; expect .COMMA; discard parseTyp
    let target ← globalId
    return .TLE_Global ⟨id, t, false, some (.EXP_Ident (.ID_Global target)), false, true,
      anns ++ (← globalPost)⟩
  let init ← eat .KW_EXTERNALLY_INITIALIZED
  let constant ← if ← eat .KW_CONSTANT then pure true else expect .KW_GLOBAL *> pure false
  let t ← parseTyp
  let v ← if external then pure none else some <$> parseExp
  return .TLE_Global ⟨id, t, constant, v, init, false, anns ++ (← globalPost)⟩

private def optLocal : P (Option LexedId) := do
  if let .LOCAL i ← peek then discard pop; return some i
  return none

private def blockLabel? : P (Option IRString) := do
  if let .STRING s ← peek then
    discard pop; expect .COLON; return some (quoteBytes s)
  let s ← match ← peek with
    | .LABEL s => pure s
    | .fixed .KW_DEFAULT_COLON => pure "default".toUTF8
    | .fixed .KW_ARGMEM_COLON => pure "argmem".toUTF8
    | .fixed .KW_INACCESSIBLEMEM_COLON => pure "inaccessiblemem".toUTF8
    | .fixed .KW_ERRNOMEM_COLON => pure "errnomem".toUTF8
    | .fixed .KW_RET_COLON => pure "ret".toUTF8
    | _ => return none
  discard pop; return some s

local instance : Inhabited (P (P (block typ))) := ⟨syntaxError⟩

/-- Delay numbering until `}` as in Menhir: a malformed body must not be reported as an ID error. -/
private def parseBlock : P (P (block typ)) := do
  let labelPos ← startPos
  let label ← blockLabel?
  let mut phis := []
  let mut code := []
  repeat
    let pos ← startPos
    let id ← optLocal
    if id.isSome then expect .EQ
    let tk ← peek
    if startsTerm tk then
      let (term, md) ← parseTerm
      return do
        let blockId ← boundLabel label labelPos
        let ps ← phis.reverse.mapM fun (lhs, p, phiNode, m) ↦ do
          return ((← boundId lhs p, phiNode), m)
        let ins ← code.reverse.mapM fun (lhs, p, inst, m) ↦ do
          let rid ← if Vellvm.Syntax.AstLib.is_void_instr inst then do
              if lhs.isSome then failure "void function has defined left-hand-side"
              voidId
            else instr_id.IId <$> boundId lhs p
          return ((rid, inst), m)
        let termId ← if id.isNone then voidId else instr_id.IId <$> boundId id pos
        return ⟨blockId, ps, ins, ((termId, term), md), none⟩
    if isFixed tk .KW_PHI then
      unless id.isSome && code.isEmpty do syntaxError
      let (p, m) ← parsePhi
      phis := (id, pos, p, m) :: phis
    else
      let (i, m) ← parseInstr
      code := (id, pos, i, m) :: code

private abbrev Arg := (typ × List param_attr) × (Option LexedId × Position)

private def fnArgs : P (List Arg × Bool) := do
  let mut rev := []
  expect .LPAREN
  repeat
    if ← eat .RPAREN then return (rev.reverse, false)
    if ← eat .DOTDOTDOT then expect .RPAREN; return (rev.reverse, true)
    let t ← parseTyp
    let attrs ← parseParams
    let pos ← startPos
    let id ← optLocal
    rev := ((t, attrs), (id, pos)) :: rev
    unless ← eat .COMMA do expect .RPAREN; return (rev.reverse, false)

private def functionEntity (isDef : Bool) : P Entity := do
  discard pop
  let link ← parseLinkage?
  let pre : List (Option Ann) := [link.map ANN_linkage, ← preemption?, ← visibility?, ← dll?, ← parseCconv?]
  let retAttrs ← parseParams
  let ret ← parseRetTyp
  let name ← globalId
  modify fun s ↦ { s with voidCount := 0 }
  let (args, vararg) ← fnArgs
  let u ← unnamed?
  let ad ← if isDef then parseAddrspace? else pure none
  let attrs ← parseFnAttrs
  let sec ← if isDef then optionalKw .KW_SECTION (ANN_section <$> parseString) else pure none
  let part ← if isDef then optionalKw .KW_PARTITION (ANN_partition <$> parseString) else pure none
  let com ← if isDef then optionalKw .KW_COMDAT (ANN_comdat <$> withParens localId) else pure none
  let al ← optionalKw .KW_ALIGN (ANN_align <$> parseInteger)
  let gc ← optionalKw .KW_GC (ANN_gc <$> parseString)
  let px ← optionalKw .KW_PREFIX (ANN_prefix <$> parseTExp)
  let pro ← optionalKw .KW_PROLOGUE (ANN_prologue <$> parseTExp)
  let per ← if isDef then optionalKw .KW_PERSONALITY (ANN_personality <$> parseTExp) else pure none
  let mut md := []
  if isDef && startsBangId (← peek) then
    md := [← metadataAnn]
    while ← eat .COMMA do md := (← metadataAnn) :: md
  let header : declaration typ := ⟨name, .TYPE_Function ret (args.map (·.1.1)) vararg,
    (retAttrs, args.map (·.1.2)), attrs, (pre ++ [u, ad, sec, part, com, al, gc, px, pro, per]).reduceOption ++ md.reverse⟩
  unless isDef do return .TLE_Declaration header
  expect .LCURLY
  let entry ← parseBlock
  let mut rest := []
  while !(← eat .RCURLY) do rest := (← parseBlock) :: rest
  modify fun s ↦ { s with anon := 0 }
  let ids ← args.mapM fun a ↦ boundId a.2.1 a.2.2
  let first ← entry
  let body ← rest.reverse.mapM id
  return .TLE_Definition ⟨header, ids, first, body⟩

private def entity : P Entity := do
  match ← peek with
  | .fixed .KW_DEFINE => functionEntity true
  | .fixed .KW_DECLARE => functionEntity false
  | .GLOBAL _ => globalDecl
  | .fixed .KW_TARGET =>
    discard pop
    let layout ← if ← eat .KW_DATALAYOUT then pure true else expect .KW_TRIPLE *> pure false
    expect .EQ; let s ← parseString
    return if layout then .TLE_Datalayout s else .TLE_Target s
  | .fixed .KW_SOURCE_FILENAME =>
    discard pop; expect .EQ; return .TLE_Source_filename (← parseString)
  | .LOCAL _ =>
    let l ← localId; expect .EQ; expect .KW_TYPE; return .TLE_Type_decl (.ID_Local l) (← parseTyp)
  | .fixed .KW_ATTRIBUTES =>
    discard pop
    let .ATTR_GRP_ID i ← peek | syntaxError
    discard pop; expect .EQ; expect .LCURLY
    let attrs ← parseFnAttrs; expect .RCURLY
    return .TLE_Attribute_group i attrs
  | .fixed .BANG | .METADATA_NAME _ =>
    let mid ← parseBangMetadataId; expect .EQ
    return .TLE_Metadata mid (← eat .KW_DISTINCT) (← parseTleMetadata)
  | .COMMENT s => discard pop; return .TLE_Comment s
  | _ => syntaxError

private def entities : P (List Entity) := do
  let mut rev := []
  repeat
    match ← peek with
    | .fixed .EOF => discard pop; return rev.reverse
    | .COMMENT_EOF s => discard pop; return (.TLE_Comment s :: rev).reverse
    | _ => rev := (← entity) :: rev

/-- Module parser. `input` is the lexer buffer, without any decoding or path rewriting. -/
def toplevel_entities (input filename : ByteArray) (line : Nat := 1) :=
  run entities (.init input filename line)

def test_call (input filename : ByteArray) (line : Nat := 1) :=
  run parseTestCall (.init input filename line)

def texp (input filename : ByteArray) (line : Nat := 1) :=
  run parseTExp (.init input filename line)

def metadata_id (input filename : ByteArray) (line : Nat := 1) :=
  run parseMetadataId (.init input filename line)

end Vellvm.Frontend.Parser
