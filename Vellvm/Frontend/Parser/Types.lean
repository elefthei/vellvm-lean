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

public import Vellvm.Frontend.ParseUtil

public section
namespace Vellvm.Frontend.Parser
open Vellvm.Syntax.LLVMAst

private def atomTyp? : Token → Option typ
  | .I n => some (.TYPE_I n)
  | .B n => some (.TYPE_B n)
  | .fixed .KW_IPTR => some .TYPE_Iptr
  | .fixed .KW_PTR => some (.TYPE_Pointer none)
  | .fixed .KW_HALF => some (.TYPE_FP .FP_half)
  | .fixed .KW_FLOAT => some (.TYPE_FP .FP_float)
  | .fixed .KW_DOUBLE => some (.TYPE_FP .FP_double)
  | .fixed .KW_X86_FP80 => some (.TYPE_FP .FP_x86_fp80)
  | .fixed .KW_FP128 => some (.TYPE_FP .FP_fp128)
  | .fixed .KW_PPC_FP128 => some (.TYPE_FP .FP_ppc_fp128)
  | .fixed .KW_X86_MMX => some .TYPE_X86_mmx
  | .fixed .KW_OPAQUE => some .TYPE_Opaque
  | .fixed .KW_VOID => some .TYPE_Void
  | .fixed .KW_METADATA => some .TYPE_Metadata
  | _ => none

/-- First tokens of `typ`, including `void` at the start of a function type. -/
def startsTyp : Token → Bool
  | .LOCAL _ | .fixed .LSQUARE | .fixed .LT | .fixed .LCURLY | .fixed .LTLCURLY => true
  | t => (atomTyp? t).isSome

private def arraySize : int_syntax → P Nat
  | .IntDecimal (.Pos u) => pure u.toNat
  | .IntHexadecimal (.Pos u) => pure u.toNat
  | _ => failure "n_of_int_syntax got invalid syntax"

private def sizedType (elem : P typ) (close : FixedToken) (mk : Nat → typ → typ) : P typ := do
  discard pop
  let n ← parseInteger
  expect .KW_X
  let t ← elem
  expect close
  return mk (← arraySize n) t

/-- Unlike struct fields, a function type's arguments allow a trailing comma. -/
private def typeArgs (arg : P typ) : P (List typ × Bool) := do
  let mut rev := []
  repeat
    if ← eat .RPAREN then return (rev.reverse, false)
    if ← eat .DOTDOTDOT then
      expect .RPAREN
      return (rev.reverse, true)
    rev := (← arg) :: rev
    unless ← eat .COMMA do break
  expect .RPAREN
  return (rev.reverse, false)

private inductive TypePosition where
  | ordinary | nonMetadata | ret

private partial def typeAt (pos : TypePosition) : P typ := do
  let token ← peek
  let mut t : typ ← match token with
    | .LOCAL _ => (fun id ↦ TYPE_Identified (.ID_Local id)) <$> localId
    | .fixed .LSQUARE => sizedType (typeAt .ordinary) .RSQUARE .TYPE_Array
    | .fixed .LT => sizedType (typeAt .ordinary) .GT .TYPE_Vector
    | .fixed .LCURLY => pop *> (TYPE_Struct <$> parseSep .RCURLY (typeAt .ordinary))
    | .fixed .LTLCURLY => pop *> (TYPE_Packed_struct <$> parseSep .RCURLYGT (typeAt .ordinary))
    | _ => match atomTyp? token with
      | some t => pop *> pure t
      | none => syntaxError
  -- A star turns even a function or metadata type back into a non_function_type.
  repeat
    match ← peek with
    | .fixed .STAR =>
      if let .TYPE_Void := t then break
      discard pop
      t := .TYPE_Pointer (some t)
    | .fixed .LPAREN =>
      match t with
      | .TYPE_Metadata | .TYPE_Function .. => break
      | _ =>
        discard pop
        let (args, vararg) ← typeArgs (typeAt .ordinary)
        t := .TYPE_Function t args vararg
    | _ => break
  match pos, t with
  | .ret, .TYPE_Metadata | .ret, .TYPE_Function .. | .nonMetadata, .TYPE_Metadata
  | .ordinary, .TYPE_Void | .nonMetadata, .TYPE_Void => syntaxError
  | _, _ => return t

def parseTyp : P typ := typeAt .ordinary
def parseNonMetadataType : P typ := typeAt .nonMetadata
def parseRetTyp : P typ := typeAt .ret

/-- A present attribute commits to its operands; an absent attribute consumes nothing. -/
private def attrList (selectAttr : Token → Option (P α)) : P (List α) := do
  let mut rev := []
  repeat
    let some p := selectAttr (← peek) | break
    discard pop
    rev := (← p) :: rev
  return rev.reverse

private def bare (a : α) : Option (P α) := some (pure a)

private def captureComponent : P IRString := do
  let s : String ← match ← peek with
    | .fixed .KW_ADDRESS => pure "address"
    | .fixed .KW_ADDRESS_IS_NULL => pure "address_is_null"
    | .fixed .KW_PROVENANCE => pure "provenance"
    | .fixed .KW_READ_PROVENANCE => pure "read_provenance"
    | _ => syntaxError
  discard pop
  return s.toUTF8

private def captureGroup : P (List IRString × List IRString) := do
  if ← eat .KW_NONE then return ([], [])
  let mut rev := []
  repeat
    if ← eat .KW_RET_COLON then return (rev.reverse, ← parseSep1 captureComponent)
    rev := (← captureComponent) :: rev
    unless ← eat .COMMA do break
  return (rev.reverse, [])

private def intPair : P (int_syntax × int_syntax) := withParens do
  let a ← parseInteger
  expect .COMMA
  return (a, ← parseInteger)

private def fpClassWord? : Token → Option IRString
  | .KW_UNKNOWN w => some w
  | .fixed .KW_NINF => some "ninf".toUTF8
  | .fixed .KW_SUB => some "sub".toUTF8
  | _ => none

private def fpClass : P param_attr := do
  let line := (← get).lastStart.line
  expect .LPAREN
  if let .INTEGER n ← peek then
    discard pop
    expect .RPAREN
    let m := n.toInt
    unless nofpclass_mask_valid m do failure s!"line {line}: invalid mask value for nofpclass"
    return .PARAMATTR_Nofpclass m
  let mut rev := []
  repeat
    let some w := fpClassWord? (← peek) | break
    discard pop
    rev := w :: rev
  if rev.isEmpty then syntaxError
  expect .RPAREN
  let words := rev.reverse
  let some mask := nofpclass_mask words | do
    let names := String.intercalate " " (words.map String.fromUTF8!)
    failure s!"line {line}: nofpclass: expected a floating-point class name, got '{names}'"
  return .PARAMATTR_Nofpclass mask

private def paramAttr? : Token → Option (P param_attr)
  | .fixed .KW_ZEROEXT => bare .PARAMATTR_Zeroext
  | .fixed .KW_SIGNEXT => bare .PARAMATTR_Signext
  | .fixed .KW_INREG => bare .PARAMATTR_Inreg
  | .fixed .KW_BYVAL => some (PARAMATTR_Byval <$> withParens parseTyp)
  | .fixed .KW_BYREF => some (PARAMATTR_Byref <$> withParens parseTyp)
  | .fixed .KW_PREALLOCATED => some (PARAMATTR_Preallocated <$> withParens parseTyp)
  | .fixed .KW_INALLOCA => some (PARAMATTR_Inalloca <$> withParens parseTyp)
  | .fixed .KW_SRET => some (PARAMATTR_Sret <$> withParens parseTyp)
  | .fixed .KW_ELEMENTTYPE => some (PARAMATTR_Elementtype <$> withParens parseTyp)
  | .fixed .KW_ALIGN => some do
    if isFixed (← peek) .LPAREN then return .PARAMATTR_Align (← withParens parseInteger)
    return .PARAMATTR_Align (← parseInteger)
  | .fixed .KW_NOALIAS => bare .PARAMATTR_Noalias
  | .fixed .KW_NOCAPTURE => bare .PARAMATTR_Nocapture
  | .fixed .KW_NOFREE => bare .PARAMATTR_Nofree
  | .fixed .KW_NEST => bare .PARAMATTR_Nest
  | .fixed .KW_RETURNED => bare .PARAMATTR_Returned
  | .fixed .KW_NONNULL => bare .PARAMATTR_Nonnull
  | .fixed .KW_DEREFERENCEABLE => some (PARAMATTR_Dereferenceable <$> withParens parseInteger)
  | .fixed .KW_DEREFERENCEABLE_OR_NULL =>
    some (PARAMATTR_Dereferenceable_or_null <$> withParens parseInteger)
  | .fixed .KW_SWIFTSELF => bare .PARAMATTR_Swiftself
  | .fixed .KW_SWIFTASYNC => bare .PARAMATTR_Swiftasync
  | .fixed .KW_SWIFTERROR => bare .PARAMATTR_Swifterror
  | .fixed .KW_IMMARG => bare .PARAMATTR_Immarg
  | .fixed .KW_NOUNDEF => bare .PARAMATTR_Noundef
  | .fixed .KW_NOFPCLASS => some fpClass
  | .fixed .KW_NOFREEOBJ => bare .PARAMATTR_Nofreeobj
  | .fixed .KW_ALIGNSTACK => some (PARAMATTR_Alignstack <$> withParens parseInteger)
  | .fixed .KW_ALLOCALIGN => bare .PARAMATTR_Allocalign
  | .fixed .KW_ALLOCPTR => bare .PARAMATTR_Allocptr
  | .fixed .KW_READNONE => bare .PARAMATTR_Readnone
  | .fixed .KW_READONLY => bare .PARAMATTR_Readonly
  | .fixed .KW_WRITEONLY => bare .PARAMATTR_Writeonly
  | .fixed .KW_WRITABLE => bare .PARAMATTR_Writable
  | .fixed .KW_DEADONUNWIND => bare .PARAMATTR_Dead_on_unwind
  | .fixed .KW_DEADONRETURN => some do
    if isFixed (← peek) .LPAREN then
      return .PARAMATTR_Dead_on_return (some (← withParens parseInteger))
    return .PARAMATTR_Dead_on_return none
  | .fixed .KW_RANGE => some <| withParens do
    let t ← parseTyp
    let a ← parseInteger
    expect .COMMA
    return .PARAMATTR_Range t a (← parseInteger)
  | .fixed .KW_INITIALIZES => some (expect .LPAREN *> (PARAMATTR_Initializes <$> parseSep .RPAREN intPair))
  | .fixed .KW_CAPTURES => some (PARAMATTR_Captures <$> withParens captureGroup)
  | _ => none

def parseParams : P (List param_attr) := attrList paramAttr?

private def memAccess : P mem_access_kind := do
  let k ← match ← peek with
    | .fixed .KW_NONE => pure ACC_None
    | .fixed .KW_READ => pure ACC_Read
    | .fixed .KW_WRITE => pure ACC_Write
    | .fixed .KW_READWRITE => pure ACC_Readwrite
    | _ => syntaxError
  discard pop
  return k

private def memAttr : P (mem_loc × mem_access_kind) := do
  let l ← match ← peek with
    | .fixed .KW_DEFAULT => pop *> expect .COLON *> pure LOC_Default
    | .fixed .KW_ARGMEM => pop *> expect .COLON *> pure LOC_Argmem
    | .fixed .KW_INACCESSIBLEMEM => pop *> expect .COLON *> pure LOC_Inaccessiblemem
    | .fixed .KW_ERRNOMEM => pop *> expect .COLON *> pure LOC_Errnomem
    | .fixed .KW_DEFAULT_COLON => pop *> pure LOC_Default
    | .fixed .KW_ARGMEM_COLON => pop *> pure LOC_Argmem
    | .fixed .KW_INACCESSIBLEMEM_COLON => pop *> pure LOC_Inaccessiblemem
    | .fixed .KW_ERRNOMEM_COLON => pop *> pure LOC_Errnomem
    | _ => pure LOC_Default
  return (l, ← memAccess)

private def sizeAttr (mk : int_syntax → Option int_syntax → fn_attr) : P fn_attr := do
  expect .LPAREN
  let a ← parseInteger
  let b ← if ← eat .COMMA then some <$> parseInteger else pure none
  let mut tooLong := false
  while ← eat .COMMA do
    discard parseInteger
    tooLong := true
  expect .RPAREN
  if tooLong then failure "allocsize illegal - too long"
  return mk a b

private def fnAttr? : Token → Option (P fn_attr)
  | .fixed .KW_ALIGNSTACK => some (FNATTR_Alignstack <$> withParens parseInteger)
  | .fixed .KW_ALLOCKIND => some (FNATTR_Allockind <$> withParens parseString)
  | .fixed .KW_ALLOCSIZE => some (sizeAttr FNATTR_Allocsize)
  | .fixed .KW_ALWAYSINLINE => bare .FNATTR_Alwaysinline
  | .fixed .KW_BUILTIN | .fixed .KW_NOBUILTIN => bare .FNATTR_Nobuiltin
  | .fixed .KW_COLD => bare .FNATTR_Cold
  | .fixed .KW_CONVERGENT => bare .FNATTR_Convergent
  | .fixed .KW_DISABLE_SANITIZER_INSTRUMENTATION => bare .FNATTR_Disable_sanitizer_instrumentation
  | .fixed .KW_FN_RET_THUNK_EXTERN => bare .FNATTR_Fn_ret_thunk_extern
  | .fixed .KW_HOT => bare .FNATTR_Hot
  | .fixed .KW_INACCESSIBLEMEMONLY => bare .FNATTR_Inaccessiblememonly
  | .fixed .KW_INACCESSIBLEMEM_OR_ARGMEMONLY => bare .FNATTR_Inaccessiblemem_or_argmemonly
  | .fixed .KW_INLINEHINT => bare .FNATTR_Inlinehint
  | .fixed .KW_JUMPTABLE => bare .FNATTR_Jumptable
  | .fixed .KW_MINSIZE => bare .FNATTR_Minsize
  | .fixed .KW_NAKED => bare .FNATTR_Naked
  | .fixed .KW_NO_JUMP_TABLES => bare .FNATTR_No_jump_tables
  | .fixed .KW_NODUPLICATE => bare .FNATTR_Noduplicate
  | .fixed .KW_NOFREE => bare .FNATTR_Nofree
  | .fixed .KW_NOIMPLICITFLOAT => bare .FNATTR_Noimplicitfloat
  | .fixed .KW_NOINLINE => bare .FNATTR_Noinline
  | .fixed .KW_NOMERGE => bare .FNATTR_Nomerge
  | .fixed .KW_NONLAZYBIND => bare .FNATTR_Nonlazybind
  | .fixed .KW_NOREDZONE => bare .FNATTR_Noredzone
  | .fixed .KW_INDIRECT_TLS_SEG_REFS => bare .FNATTR_Indirect_tls_seg_refs
  | .fixed .KW_NORETURN => bare .FNATTR_Noreturn
  | .fixed .KW_NORECURSE => bare .FNATTR_Norecurse
  | .fixed .KW_WILLRETURN => bare .FNATTR_Willreturn
  | .fixed .KW_NOSYNC => bare .FNATTR_Nosync
  | .fixed .KW_NOUNWIND => bare .FNATTR_Nounwind
  | .fixed .KW_NOCREATEUNDEFORPOISON => bare .FNATTR_Nocreateundeforpoison
  | .fixed .KW_NOSANITIZE_BOUNDS => bare .FNATTR_Nosanitize_bounds
  | .fixed .KW_NOSANITIZE_COVERAGE => bare .FNATTR_Nosanitize_coverage
  | .fixed .KW_NULL_POINTER_IS_VALID => bare .FNATTR_Null_pointer_is_valid
  | .fixed .KW_OPTFORFUZZING => bare .FNATTR_Optforfuzzing
  | .fixed .KW_OPTNONE => bare .FNATTR_Optnone
  | .fixed .KW_OPTSIZE => bare .FNATTR_Optsize
  | .fixed .KW_READNONE => bare .FNATTR_Readnone
  | .fixed .KW_READONLY => bare .FNATTR_Readonly
  | .fixed .KW_WRITEONLY => bare .FNATTR_Writeonly
  | .fixed .KW_ARGMEMONLY => bare .FNATTR_Argmemonly
  | .fixed .KW_RETURNS_TWICE => bare .FNATTR_Returns_twice
  | .fixed .KW_SAFESTACK => bare .FNATTR_Safestack
  | .fixed .KW_SANITIZE_ADDRESS => bare .FNATTR_Sanitize_address
  | .fixed .KW_SANITIZE_MEMORY => bare .FNATTR_Sanitize_memory
  | .fixed .KW_SANITIZE_THREAD => bare .FNATTR_Sanitize_thread
  | .fixed .KW_SANITIZE_HWADDRESS => bare .FNATTR_Sanitize_hwaddress
  | .fixed .KW_SANITIZE_MEMTAG => bare .FNATTR_Sanitize_memtag
  | .fixed .KW_SPECULATIVE_LOAD_HARDENING => bare .FNATTR_Speculative_load_hardening
  | .fixed .KW_SPECULATABLE => bare .FNATTR_Speculatable
  | .fixed .KW_SSP => bare .FNATTR_Ssp
  | .fixed .KW_SSPSTRONG => bare .FNATTR_Sspstrong
  | .fixed .KW_SSPREQ => bare .FNATTR_Sspreq
  | .fixed .KW_STRICTFP => bare .FNATTR_Strictfp
  | .fixed .KW_UWTABLE => some do
    unless ← eat .LPAREN do return .FNATTR_Uwtable none
    let sync ← if ← eat .KW_SYNC then pure true else expect .KW_ASYNC *> pure false
    expect .RPAREN
    return .FNATTR_Uwtable (some sync)
  | .fixed .KW_NOCF_CHECK => bare .FNATTR_Nocf_check
  | .fixed .KW_SHADOWCALLSTACK => bare .FNATTR_Shadowcallstack
  | .fixed .KW_MUSTPROGRESS => bare .FNATTR_Mustprogress
  | .fixed .KW_VSCALE_RANGE => some (sizeAttr FNATTR_Vscale_range)
  | .STRING s => some do
    if ← eat .EQ then return .FNATTR_Key_value (s, ← parseString)
    return .FNATTR_String s
  | .ATTR_GRP_ID i => bare (.FNATTR_Attr_grp i)
  | .KW_UNKNOWN s => bare (.FNATTR_UNKNOWN s)
  | .fixed .KW_MEMORY => some (FNATTR_Memory <$> withParens (parseSep1 memAttr))
  | _ => none

def parseFnAttrs : P (List fn_attr) := attrList fnAttr?

private def convention? : Token → Option (P cconv)
  | .fixed .KW_CC => some (CC_Cc <$> parseInteger)
  | .fixed .KW_CCC => bare .CC_Ccc
  | .fixed .KW_FASTCC => bare .CC_Fastcc
  | .fixed .KW_COLDCC => bare .CC_Coldcc
  | .fixed .KW_WEBKIT_JSCC => bare .CC_Webkit_jscc
  | .fixed .KW_ANYREGCC => bare .CC_Anyregcc
  | .fixed .KW_PRESERVE_MOSTCC => bare .CC_Preserve_mostcc
  | .fixed .KW_PRESERVE_ALLCC => bare .CC_Preserve_allcc
  | .fixed .KW_CXX_FAST_TLSCC => bare .CC_Cxx_fast_tlscc
  | .fixed .KW_TAILCC => bare .CC_Tailcc
  | .fixed .KW_SWIFTCC => bare .CC_Swiftcc
  | .fixed .KW_SWIFTTAILCC => bare .CC_Swifttailcc
  | .fixed .KW_CFGUARD_CHECKCC => bare .CC_cfguard_checkcc
  | _ => none

def parseCconv? : P (Option (annotation typ)) := do
  let some p := convention? (← peek) | return none
  discard pop
  return some (.ANN_cconv (← p))

def parseAddrspace? : P (Option (annotation typ)) := do
  unless ← eat .KW_ADDRSPACE do return none
  return some (.ANN_addrspace (← withParens parseInteger))

end Vellvm.Frontend.Parser
