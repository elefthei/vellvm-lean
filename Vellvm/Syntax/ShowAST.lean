/- Translated from Vellvm's Syntax/ShowAST.v (see LICENSE.md). -/
module

public import Vellvm.Syntax.DynamicTypes
public import Vellvm.Utils.StringUtil

@[expose] public section
namespace Vellvm.Syntax.ShowAST
open LLVMAst
open Utils.StringUtil (Show «show»)
open Utils.DList

abbrev lit := String.toUTF8
abbrev sd := string_to_DString
abbrev ds (s : String) := sd (lit s)
local infixr:65 " <+> " => DList_append

def concatStr (xs : List IRString) : IRString := xs.foldl (· ++ ·) .empty

def concat_str_sep (sep : IRString) : List IRString → IRString
  | [] => .empty
  | x :: xs => xs.foldl (fun out y ↦ out ++ sep ++ y) x

instance Show_Pos : Show Positive := ⟨fun p ↦ Utils.StringUtil.show_Z (Int.ofNat p.val)⟩

class DShow (A : Type u) where
  Build_DShow ::
  dshow : A → DString
export DShow (Build_DShow dshow)

instance DShowList {A : Type u} [DShow A] : DShow (List A) := ⟨fun xs ↦ DList_join (xs.map dshow)⟩
instance DShowPair {A : Type u} {B : Type v} [DShow A] [DShow B] : DShow (A × B) :=
  ⟨fun (a, b) ↦ ds "(" <+> dshow a <+> ds "," <+> dshow b <+> ds ")"⟩
instance (priority := low) DShowShow {A : Type u} [DShow A] : Show A :=
  ⟨fun x ↦ DString_to_string (dshow x)⟩

def dintersperse (sep : DString) (xs : List DString) : DString :=
  xs.foldl (fun acc s ↦ if (acc []).isEmpty then s else acc <+> sep <+> s) DList_empty

def dconcat := concat_DString

def intersperse (sep : IRString) (xs : List IRString) : IRString :=
  xs.foldl (fun acc s ↦ if acc.size == 0 then s else acc ++ sep ++ s) .empty

def hexDigits : Hexadecimal.uint → ByteArray → ByteArray
  | .Nil, out => out
  | .D0 t, out => hexDigits t (out.push 48)
  | .D1 t, out => hexDigits t (out.push 49)
  | .D2 t, out => hexDigits t (out.push 50)
  | .D3 t, out => hexDigits t (out.push 51)
  | .D4 t, out => hexDigits t (out.push 52)
  | .D5 t, out => hexDigits t (out.push 53)
  | .D6 t, out => hexDigits t (out.push 54)
  | .D7 t, out => hexDigits t (out.push 55)
  | .D8 t, out => hexDigits t (out.push 56)
  | .D9 t, out => hexDigits t (out.push 57)
  | .Da t, out => hexDigits t (out.push 97)
  | .Db t, out => hexDigits t (out.push 98)
  | .Dc t, out => hexDigits t (out.push 99)
  | .Dd t, out => hexDigits t (out.push 100)
  | .De t, out => hexDigits t (out.push 101)
  | .Df t, out => hexDigits t (out.push 102)

def show_int_syntax : int_syntax → IRString
  | .IntDecimal i => Utils.StringUtil.show_int i
  | .IntHexadecimal (.Pos h) => hexDigits h (lit "u0x")
  | .IntHexadecimal (.Neg h) => hexDigits h (lit "s0x")
instance showIntSyntax : Show int_syntax := ⟨show_int_syntax⟩

def dshow_raw_id : raw_id → DString
  | .Name s => sd s
  | .Anon i | .Raw i => sd («show» i)
instance dshowRawId : DShow raw_id := ⟨dshow_raw_id⟩

def dshow_ident : «ident» → DString
  | .ID_Global r => ds "@" <+> dshow r
  | .ID_Local r => ds "%" <+> dshow r
instance dshowIdent : DShow «ident» := ⟨dshow_ident⟩

def show_floating_point_variant : floating_point_variant → IRString
  | .FP_half => lit "half"
  | .FP_bfloat => lit "bfloat"
  | .FP_float => lit "float"
  | .FP_double => lit "double"
  | .FP_fp128 => lit "fp128"
  | .FP_x86_fp80 => lit "x86_fp80"
  | .FP_ppc_fp128 => lit "ppc_fp128"

instance showFloatingPointVariant : Show floating_point_variant := ⟨show_floating_point_variant⟩

def dshow_floating_point_variant (fp : floating_point_variant) := sd (show_floating_point_variant fp)
instance dshowFLoatingPointVariant : DShow floating_point_variant := ⟨dshow_floating_point_variant⟩

def varargSuffix (empty varargs : Bool) : DString :=
  if varargs then if empty then ds "..." else ds ", ..." else DList_empty

def dshow_typ : typ → DString
  | .TYPE_I n => ds "i" <+> sd («show» n)
  | .TYPE_B n => ds "b" <+> sd («show» n)
  | .TYPE_Iptr => ds "iptr"
  | .TYPE_Pointer (some t) => dshow_typ t <+> ds "*"
  | .TYPE_Pointer none => ds "ptr"
  | .TYPE_Void => ds "void"
  | .TYPE_FP fp => dshow fp
  | .TYPE_Label => ds "label"
  | .TYPE_Token => ds "token"
  | .TYPE_Metadata => ds "metadata"
  | .TYPE_X86_mmx => ds "x86_mmx"
  | .TYPE_Array n t => ds "[" <+> sd («show» n) <+> ds " x " <+> dshow_typ t <+> ds "]"
  | .TYPE_Vector n t => ds "<" <+> sd («show» n) <+> ds " x " <+> dshow_typ t <+> ds ">"
  | .TYPE_Function ret args varargs => dshow_typ ret <+> ds " (" <+>
      dconcat (ds ", ") (args.map dshow_typ) <+> varargSuffix args.isEmpty varargs <+> ds ")"
  | .TYPE_Struct fields => ds "{" <+> dconcat (ds ", ") (fields.map dshow_typ) <+> ds "}"
  | .TYPE_Packed_struct fields => ds "<{" <+> dconcat (ds ", ") (fields.map dshow_typ) <+> ds "}>"
  | .TYPE_Opaque => ds "opaque"
  | .TYPE_Identified i => dshow i

instance dshowTyp : DShow typ := ⟨dshow_typ⟩

def show_linkage : linkage → IRString
  | .LINKAGE_Private => lit "private "
  | .LINKAGE_Internal => lit "internal "
  | .LINKAGE_Available_externally => lit "available_externally "
  | .LINKAGE_Linkonce => lit "linkonce "
  | .LINKAGE_Weak => lit "weak "
  | .LINKAGE_Common => lit "common "
  | .LINKAGE_Appending => lit "appending "
  | .LINKAGE_Linkonce_odr => lit "linkonce_odr "
  | .LINKAGE_Weak_odr => lit "weak_odr "
  | .LINKAGE_External => lit "external "
  | .LINKAGE_Extern_weak => lit "extern_weak "

instance showLinkage : Show linkage := ⟨show_linkage⟩

def show_dll_storage : dll_storage → IRString
  | .DLLSTORAGE_Dllimport => lit "dllimport"
  | .DLLSTORAGE_Dllexport => lit "dllexport"

instance showDllStorage : Show dll_storage := ⟨show_dll_storage⟩

def show_visibility : visibility → IRString
  | .VISIBILITY_Default => lit "default"
  | .VISIBILITY_Hidden => lit "hidden"
  | .VISIBILITY_Protected => lit "protected"

instance showVisibility : Show visibility := ⟨show_visibility⟩

def show_cconv : cconv → IRString
  | .CC_Ccc => lit "ccc"
  | .CC_Fastcc => lit "fastcc"
  | .CC_Coldcc => lit "coldcc"
  | .CC_Webkit_jscc => lit "webkit_jscc"
  | .CC_Anyregcc => lit "anyregcc"
  | .CC_Preserve_mostcc => lit "preserve_mostcc"
  | .CC_Preserve_allcc => lit "preserve_allcc"
  | .CC_Cxx_fast_tlscc => lit "cxx_fast_tlscc"
  | .CC_Tailcc => lit "tailcc"
  | .CC_Swiftcc => lit "swiftcc"
  | .CC_Swifttailcc => lit "swifttailcc"
  | .CC_cfguard_checkcc => lit "cfguard_checkcc"
  | .CC_Cc n => lit "cc" ++ «show» n

instance showCConv : Show cconv := ⟨show_cconv⟩

def show_sum {A : Type u} {B : Type v} [Show A] [Show B] : Sum A B → IRString
  | .inl a => «show» a
  | .inr b => «show» b
instance showSum {A : Type u} {B : Type v} [Show A] [Show B] : Show (Sum A B) := ⟨show_sum⟩

def dshow_pair_list {A : Type u} [Show A] (l : List (A × A)) : DString :=
  dconcat (ds ", ") (l.map fun x ↦ sd (Utils.StringUtil.showPair.«show» x))

def dshow_capture : List IRString × List IRString → DString
  | ([], []) => ds "none"
  | (l, []) => dconcat (ds ", ") (l.map sd)
  | ([], r) => ds "ret: " <+> dconcat (ds ", ") (r.map sd)
  | (l, r) => dconcat (ds ", ") (l.map sd) <+> ds ", ret: " <+> dconcat (ds ", ") (r.map sd)

def show_param_attr : param_attr → DString
  | .PARAMATTR_Zeroext => ds "zeroext"
  | .PARAMATTR_Signext => ds "signext"
  | .PARAMATTR_Inreg => ds "inreg"
  | .PARAMATTR_Noalias => ds "noalias"
  | .PARAMATTR_Nocapture => ds "nocapture"
  | .PARAMATTR_Nofree => ds "nofree"
  | .PARAMATTR_Nest => ds "nest"
  | .PARAMATTR_Returned => ds "returned"
  | .PARAMATTR_Nonnull => ds "nonnull"
  | .PARAMATTR_Swiftself => ds "swiftself"
  | .PARAMATTR_Swiftasync => ds "swiftasync"
  | .PARAMATTR_Swifterror => ds "swifterror"
  | .PARAMATTR_Immarg => ds "immarg"
  | .PARAMATTR_Noundef => ds "noundef"
  | .PARAMATTR_Nofreeobj => ds "nofreeobj"
  | .PARAMATTR_Allocalign => ds "allocalign"
  | .PARAMATTR_Allocptr => ds "allocptr"
  | .PARAMATTR_Readnone => ds "readnone"
  | .PARAMATTR_Readonly => ds "readonly"
  | .PARAMATTR_Writeonly => ds "writeonly"
  | .PARAMATTR_Writable => ds "writable"
  | .PARAMATTR_Dead_on_unwind => ds "dead_on_unwind"
  | .PARAMATTR_Byval t => ds "byval(" <+> dshow t <+> ds ")"
  | .PARAMATTR_Byref t => ds "byref(" <+> dshow t <+> ds ")"
  | .PARAMATTR_Preallocated t => ds "preallocated(" <+> dshow t <+> ds ")"
  | .PARAMATTR_Inalloca t => ds "inalloca(" <+> dshow t <+> ds ")"
  | .PARAMATTR_Sret t => ds "sret(" <+> dshow t <+> ds ")"
  | .PARAMATTR_Elementtype t => ds "elementtype(" <+> dshow t <+> ds ")"
  | .PARAMATTR_Align a => ds "align " <+> sd («show» a)
  | .PARAMATTR_Dereferenceable n => ds "dereferenceable(" <+> sd («show» n) <+> ds ")"
  | .PARAMATTR_Dereferenceable_or_null n => ds "dereferenceable_or_null(" <+> sd («show» n) <+> ds ")"
  | .PARAMATTR_Alignstack n => ds "alignstack(" <+> sd («show» n) <+> ds ")"
  | .PARAMATTR_Nofpclass mask => ds "nofpclass(" <+> dconcat (ds " ") ((nofpclass_words mask).map sd) <+> ds ")"
  | .PARAMATTR_Dead_on_return none => ds "dead_on_return"
  | .PARAMATTR_Dead_on_return (some n) => ds "dead_on_return(" <+> sd («show» n) <+> ds ")"
  | .PARAMATTR_Range t a b => ds "range(" <+> dshow t <+> ds " " <+> sd («show» a) <+>
      ds ", " <+> sd («show» b) <+> ds ")"
  | .PARAMATTR_Initializes xs => ds "initializes(" <+> dshow_pair_list xs <+> ds ")"
  | .PARAMATTR_Captures xs => ds "captures(" <+> dshow_capture xs <+> ds ")"
instance dshowParamAttr : DShow param_attr := ⟨show_param_attr⟩

def show_eff (eff : mem_loc × mem_access_kind) : IRString :=
  (match eff.1 with
   | .LOC_Default => ByteArray.empty
   | .LOC_Argmem => lit "argmem: "
   | .LOC_Inaccessiblemem => lit "inaccessiblemem: "
   | .LOC_Errnomem => lit "errnomem: ") ++
  (match eff.2 with
   | .ACC_None => lit "none"
   | .ACC_Read => lit "read"
   | .ACC_Write => lit "write"
   | .ACC_Readwrite => lit "readwrite")

def show_fn_attr : fn_attr → IRString
  | .FNATTR_Alwaysinline => lit "alwaysinline"
  | .FNATTR_Builtin => lit "builtin"
  | .FNATTR_Cold => lit "cold"
  | .FNATTR_Convergent => lit "convergent"
  | .FNATTR_Disable_sanitizer_instrumentation => lit "disable_sanitizer_instrumentation"
  | .FNATTR_Fn_ret_thunk_extern => lit "fun_ret_thunk_extern"
  | .FNATTR_Hot => lit "hot"
  | .FNATTR_Inaccessiblememonly => lit "inaccessiblememonly"
  | .FNATTR_Inaccessiblemem_or_argmemonly => lit "inaccessiblemem_or_argmemonly"
  | .FNATTR_Inlinehint => lit "inlinehint"
  | .FNATTR_Jumptable => lit "jumptable"
  | .FNATTR_Minsize => lit "minsize"
  | .FNATTR_Naked => lit "naked"
  | .FNATTR_No_jump_tables => lit "no-jump-tables"
  | .FNATTR_Nobuiltin => lit "nobuiltin"
  | .FNATTR_Noduplicate => lit "noduplicate"
  | .FNATTR_Nofree => lit "nofree"
  | .FNATTR_Noimplicitfloat => lit "noimplicitfloat"
  | .FNATTR_Noinline => lit "noinline"
  | .FNATTR_Nomerge => lit "nomerge"
  | .FNATTR_Nonlazybind => lit "nonlazybind"
  | .FNATTR_Noprofile => lit "noprofile"
  | .FNATTR_Noredzone => lit "noredzone"
  | .FNATTR_Indirect_tls_seg_refs => lit "indirect-tls-seg-refs"
  | .FNATTR_Noreturn => lit "noreturn"
  | .FNATTR_Norecurse => lit "norecurse"
  | .FNATTR_Willreturn => lit "willreturn"
  | .FNATTR_Nosync => lit "nosync"
  | .FNATTR_Nounwind => lit "nounwind"
  | .FNATTR_Nocreateundeforpoison => lit "nocreateundeforpoison"
  | .FNATTR_Nosanitize_bounds => lit "nosanitize_bounds"
  | .FNATTR_Nosanitize_coverage => lit "nosanitize_coverage"
  | .FNATTR_Null_pointer_is_valid => lit "null_pointer_is_valid"
  | .FNATTR_Optforfuzzing => lit "optforfuzzing"
  | .FNATTR_Optnone => lit "optnone"
  | .FNATTR_Optsize => lit "optsize"
  | .FNATTR_Readnone => lit "readnone"
  | .FNATTR_Readonly => lit "readonly"
  | .FNATTR_Writeonly => lit "writeonly"
  | .FNATTR_Argmemonly => lit "argmemonly"
  | .FNATTR_Returns_twice => lit "returns_twice"
  | .FNATTR_Safestack => lit "safestack"
  | .FNATTR_Sanitize_address => lit "sanitize_address"
  | .FNATTR_Sanitize_memory => lit "sanitize_memory"
  | .FNATTR_Sanitize_thread => lit "sanitize_thread"
  | .FNATTR_Sanitize_hwaddress => lit "sanitize_hwaddress"
  | .FNATTR_Sanitize_memtag => lit "sanitize_memtag"
  | .FNATTR_Speculative_load_hardening => lit "speculative_load_hardening"
  | .FNATTR_Speculatable => lit "speculatable"
  | .FNATTR_Ssp => lit "ssp"
  | .FNATTR_Sspstrong => lit "sspstrong"
  | .FNATTR_Sspreq => lit "sspreq"
  | .FNATTR_Strictfp => lit "strictfp"
  | .FNATTR_Tls_load_hoist => lit "\"tls-load-hoist\""
  | .FNATTR_Nocf_check => lit "nocf_check"
  | .FNATTR_Shadowcallstack => lit "shadowcallstack"
  | .FNATTR_Mustprogress => lit "mustprogress"
  | .FNATTR_Alignstack a => lit "alignstack(" ++ «show» a ++ lit ")"
  | .FNATTR_Allockind k => lit "allockind(" ++ «show» k ++ lit ")"
  | .FNATTR_Allocsize n m => lit "allocsize(" ++ «show» n ++ m.elim .empty (fun x ↦ lit "," ++ «show» x) ++ lit ")"
  | .FNATTR_Uwtable none => lit "uwtable"
  | .FNATTR_Uwtable (some sync) => if sync then lit "uwtable(sync)" else lit "uwtable(async)"
  | .FNATTR_Vscale_range n m => lit "vscale_range(" ++ «show» n ++ m.elim .empty (fun x ↦ lit "," ++ «show» x) ++ lit ")"
  | .FNATTR_String s => lit "\"" ++ s ++ lit "\""
  | .FNATTR_Key_value (k,v) => lit "\"" ++ k ++ lit "\"=\"" ++ v ++ lit "\""
  | .FNATTR_Attr_grp i => lit "#" ++ «show» i
  | .FNATTR_Memory xs => lit "memory(" ++ concat_str_sep (lit ", ") (xs.map show_eff) ++ lit ")"
  | .FNATTR_UNKNOWN s => s
instance showFnAttr : Show fn_attr := ⟨show_fn_attr⟩

def show_thread_local_storage : thread_local_storage → IRString
  | .TLS_NONE => lit "thread_local"
  | .TLS_Localdynamic => lit "thread_local(localdynamic)"
  | .TLS_Initialexec => lit "thread_local(initialexec)"
  | .TLS_Localexec => lit "thread_local(localexec)"

instance showTLS : Show thread_local_storage := ⟨show_thread_local_storage⟩

def show_icmp : icmp → IRString
  | .Eq => lit "eq"
  | .Ne => lit "ne"
  | .Ugt => lit "ugt"
  | .Uge => lit "uge"
  | .Ult => lit "ult"
  | .Ule => lit "ule"
  | .Sgt => lit "sgt"
  | .Sge => lit "sge"
  | .Slt => lit "slt"
  | .Sle => lit "sle"

instance showICmp : Show icmp := ⟨show_icmp⟩

def show_fcmp : fcmp → IRString
  | .FFalse => lit "false"
  | .FOeq => lit "oeq"
  | .FOgt => lit "ogt"
  | .FOge => lit "oge"
  | .FOlt => lit "olt"
  | .FOle => lit "ole"
  | .FOne => lit "one"
  | .FOrd => lit "ord"
  | .FUno => lit "uno"
  | .FUeq => lit "ueq"
  | .FUgt => lit "ugt"
  | .FUge => lit "uge"
  | .FUlt => lit "ult"
  | .FUle => lit "ule"
  | .FUne => lit "une"
  | .FTrue => lit "true"

instance showFCmp : Show fcmp := ⟨show_fcmp⟩



def show_op_nuw_nsw (op : IRString) (nuw nsw : Bool) : IRString :=
  op ++ (if nuw then lit " nuw" else .empty) ++ (if nsw then lit " nsw" else .empty)

def show_ibinop : ibinop → IRString
  | .Add a b => show_op_nuw_nsw (lit "add") a b
  | .Sub a b => show_op_nuw_nsw (lit "sub") a b
  | .Mul a b => show_op_nuw_nsw (lit "mul") a b
  | .Shl a b => show_op_nuw_nsw (lit "shl") a b
  | .UDiv e => if e then lit "udiv exact" else lit "udiv"
  | .SDiv e => if e then lit "sdiv exact" else lit "sdiv"
  | .LShr e => if e then lit "lshr exact" else lit "lshr"
  | .AShr e => if e then lit "ashr exact" else lit "ashr"
  | .URem => lit "urem"
  | .SRem => lit "srem"
  | .And => lit "and"
  | .Or b => if b then lit "or disjoint" else lit "or"
  | .Xor => lit "xor"
instance showIBinop : Show ibinop := ⟨show_ibinop⟩

def show_fbinop : fbinop → IRString
  | .FAdd => lit "fadd"
  | .FSub => lit "fsub"
  | .FMul => lit "fmul"
  | .FDiv => lit "fdiv"
  | .FRem => lit "frem"

instance showFBinop : Show fbinop := ⟨show_fbinop⟩

def show_gep_flags (f : gep_flags) : IRString :=
  (if f.gep_inbounds then lit "inbounds " else if f.gep_nusw then lit "nusw " else .empty) ++
  (if f.gep_nuw then lit "nuw " else .empty)

def show_fast_math : fast_math → IRString
  | .Nnan => lit "nnan"
  | .Ninf => lit "ninf"
  | .Nsz => lit "nsz"
  | .Arcp => lit "arcp"
  | .Contract => lit "contract"
  | .Afn => lit "afn"
  | .Reassoc => lit "reassoc"
  | .Fast => lit "fast"

instance showFastMath : Show fast_math := ⟨show_fast_math⟩

def show_pure_conversion : pure_conversion → IRString
  | .Trunc a b => show_op_nuw_nsw (lit "trunc") a b
  | .Zext n => if n then lit "zext nneg" else lit "zext"
  | .Sext => lit "sext"
  | .Fptrunc fs => fs.foldl (fun s f ↦ s ++ lit " " ++ show_fast_math f) (lit "fptrunc")
  | .Fpext fs => fs.foldl (fun s f ↦ s ++ lit " " ++ show_fast_math f) (lit "fpext")
  | .Uitofp n => if n then lit "uitofp nneg" else lit "uitofp"
  | .Sitofp => lit "sitofp"
  | .Fptoui => lit "fptoui"
  | .Fptosi => lit "fptosi"
instance ShowPureConversion : Show pure_conversion := ⟨show_pure_conversion⟩

def show_impure_conversion : impure_conversion → IRString
  | .Inttoptr => lit "inttoptr"
  | .Ptrtoint => lit "ptrtoint"
  | .Ptrtoaddr => lit "ptrtoaddr"
  | .Addrspacecast => lit "addrspacecast"

instance ShowImpureConversion : Show impure_conversion := ⟨show_impure_conversion⟩

def show_conversion_type : conversion_type → IRString
  | .CONV_Bitcast => lit "bitcast"
  | .CONV_Pure op => show_pure_conversion op
  | .CONV_Impure op => show_impure_conversion op
instance ShowConversionType : Show conversion_type := ⟨show_conversion_type⟩

variable {T : Type}

def ex_to_int : exp T → Int
  | .EXP_Integer i => i.toInt
  | _ => 0

def ex_to_nat (e : exp T) : Nat := (ex_to_int e).toNat

def hexNatBytes (n : Nat) : List UInt8 := go n []
where
  go (n : Nat) (tail : List UInt8) : List UInt8 :=
    let d := n % 16
    let rest := UInt8.ofNat (if d < 10 then d + 48 else d + 87) :: tail
    if n < 16 then rest else go (n / 16) rest
  termination_by n
  decreasing_by omega

def show_c_string (ex : exp T) : IRString :=
  let n := ex_to_nat ex
  if n < 32 || 126 < n then
    let digits := hexNatBytes n
    ⟨((if n < 16 then [92, 48] else [92]) ++ digits).toArray⟩
  else if n == 34 then lit "\\22"
  else if n == 92 then lit "\\\\"
  else ByteArray.empty.push (UInt8.ofNat n)

def dshow_c_string (ex : exp T) : DString := sd (show_c_string ex)

def add_parens (parens : Bool) (s : DString) : DString := if parens then ds "(" <+> s <+> ds ")" else s

def dshow_bool (flag : Bool) (s : IRString) : DString := if flag then sd s else DList_empty

def show_float_hex_type : float_hex_type → IRString
  | .FH_X => lit "0x"
  | .FH_K => lit "0xK"
  | .FH_L => lit "0xL"
  | .FH_M => lit "0xM"
  | .FH_H => lit "0xH"
  | .FH_R => lit "0xR"

def show_float_syntax : float_syntax → IRString
  | .FS_decimal (.Decimal i f) => Utils.StringUtil.show_int i ++ lit "." ++ Utils.StringUtil.show_uint f
  | .FS_decimal (.DecimalExp i f e) => Utils.StringUtil.show_int i ++ lit "." ++
      Utils.StringUtil.show_uint f ++ lit "e" ++ Utils.StringUtil.show_int e
  | .FS_hex ht u => hexDigits u (show_float_hex_type ht)
instance showFloatSyntax : Show float_syntax := ⟨show_float_syntax⟩

def fast_math_list_to_dstring : List fast_math → DString
  | [] => ds " "
  | fs@(_ :: _) => ds " " <+> dconcat (ds " ") (fs.map fun f ↦ sd (show_fast_math f)) <+> ds " "

variable [DShow T]

def typedWith (t : T) (s e : DString) : DString := dshow t <+> s <+> e

def binaryOperands (b : Bool) (t : T) (a z : DString) : DString :=
  add_parens b (typedWith t (ds " ") a <+> ds ", " <+> (if b then typedWith t (ds " ") z else z))

mutual
  def dshow_exp (b : Bool) : exp T → DString
    | .EXP_Ident i => dshow i
    | .EXP_Integer i => sd (show_int_syntax i)
    | .EXP_Float f => sd (show_float_syntax f)
    | .EXP_Bool v => sd («show» v)
    | .EXP_Null => ds "null"
    | .EXP_Zero_initializer => ds "zeroinitializer"
    | .EXP_Cstring es => ds "c\"" <+> DList_join (es.map fun x ↦ dshow_c_string x.2) <+> ds "\""
    | .EXP_Undef => ds "undef"
    | .EXP_Poison => ds "poison"
    | .EXP_Struct es => ds "{" <+> showExprArgs false es <+> ds "}"
    | .EXP_Packed_struct es => ds "<{" <+> showExprArgs false es <+> ds "}>"
    | .EXP_Array es => ds "[" <+> showExprArgs false es <+> ds "]"
    | .EXP_Vector es => ds "<" <+> showExprArgs false es <+> ds ">"
    | .OP_IBinop op t a z => sd (show_ibinop op) <+> ds " " <+>
        binaryOperands b t (dshow_exp true a) (dshow_exp true z)
    | .OP_ICmp ss cmp t a z => ds "icmp " <+> dshow_bool ss (lit "samesign ") <+>
        sd (show_icmp cmp) <+> ds " " <+> binaryOperands b t (dshow_exp true a) (dshow_exp true z)
    | .OP_FBinop op fm t a z => sd (show_fbinop op) <+> ds " " <+> add_parens b
        (fast_math_list_to_dstring fm <+> typedWith t (ds " ") (dshow_exp true a) <+> ds ", " <+> dshow_exp true z)
    | .OP_Fneg fm v => ds "fneg " <+> add_parens b (fast_math_list_to_dstring fm <+> showExprPair true v)
    | .OP_FCmp cmp fm t a z => ds "fcmp" <+> fast_math_list_to_dstring fm <+> add_parens b
        (sd (show_fcmp cmp) <+> ds " " <+> typedWith t (ds " ") (dshow_exp true a) <+> ds ", " <+> dshow_exp true z)
    | .OP_Conversion op t v t' => sd (show_conversion_type op) <+> ds " " <+>
        add_parens b (typedWith t (ds " ") (dshow_exp true v) <+> ds " to " <+> dshow t')
    | .OP_GetElementPtr flags t ptr ids => ds "getelementptr " <+> sd (show_gep_flags flags) <+>
        add_parens b (dshow t <+> ds ", " <+> showExprPair true ptr <+>
          (if ids.isEmpty then DList_empty else ds ", " <+> showExprArgs true ids))
    | .OP_ExtractElement v i => ds "extractelement " <+> add_parens b
        (showExprPair true v <+> ds ", " <+> showExprPair true i)
    | .OP_InsertElement v e i => ds "insertelement " <+> add_parens b
        (showExprPair true v <+> ds ", " <+> showExprPair true e <+> ds ", " <+> showExprPair true i)
    | .OP_ShuffleVector (ta,a) (tb,z) (tm,m) => ds "shufflevector " <+> add_parens b
        (dshow ta <+> dshow_exp true a <+> ds ", " <+> dshow tb <+> dshow_exp true z <+> ds ", " <+>
         dshow tm <+> dshow_exp true m)
    | .OP_ExtractValue v ids => ds "extractvalue " <+> add_parens b
        (showExprPair true v <+> ds ", " <+> dconcat (ds ", ") (ids.map fun i ↦ sd (show_int_syntax i)))
    | .OP_InsertValue v e ids => ds "insertvalue " <+> add_parens b (showExprPair false v <+>
        ds ", " <+> showExprPair false e <+> ds ", " <+> dconcat (ds ", ") (ids.map fun i ↦ sd (show_int_syntax i)))
    | .OP_Select fm c a z => ds "select" <+> fast_math_list_to_dstring fm <+> add_parens b
        (showExprPair true c <+> ds ", " <+> showExprPair true a <+> ds ", " <+> showExprPair true z)
    | .OP_Freeze v => ds "freeze " <+> add_parens b (showExprPair true v)
    | .EXP_Asm side align intel unwind template constraints => ds "asm " <+>
        dshow_bool side (lit "sideeffect ") <+> dshow_bool align (lit "alignstack ") <+>
        dshow_bool intel (lit "inteldialect ") <+> dshow_bool unwind (lit "unwind ") <+>
        ds "\"" <+> sd template <+> ds "\", \"" <+> sd constraints <+> ds "\""
    | .EXP_Metadata md => dshow_metadata md
    | .EXP_Splat v => ds "splat (" <+> showExprPair false v <+> ds ")"
    | .EXP_BlockAddress fn blk => ds "blockaddress(@" <+> dshow_raw_id fn <+> ds ", %" <+> dshow_raw_id blk <+> ds ")"
  termination_by v => sizeOf v

  def showExprPair (b : Bool) : texp T → DString
    | (t,e) => typedWith t (ds " ") (dshow_exp b e)
  termination_by p => sizeOf p

  def showExprArgs (b : Bool) : List (texp T) → DString
    | [] => DList_empty
    | x :: xs => showExprPair b x <+> (if xs.isEmpty then DList_empty else ds ", " <+> showExprArgs b xs)
  termination_by xs => sizeOf xs

  def dshow_metadata : metadata T → DString
    | .METADATA_Null => ds "null"
    | .METADATA_Const v => showExprPair false v
    | .METADATA_Id i => ds "!" <+> dshow_raw_id i
    | .METADATA_Node xs => ds "!{" <+> dconcat (ds " , ") (xs.map dshow_metadata) <+> ds "}"
    | .METADATA_Pair a b => dshow_metadata a <+> ds " " <+> dshow_metadata b
    | .METADATA_Debug name content => ds "!DI" <+> sd name <+> ds "(" <+> sd content <+> ds ")"
    | .METADATA_File_info _ => DList_empty
  termination_by m => sizeOf m
end

instance dshowExp : DShow (exp T) := ⟨dshow_exp false⟩
-- The source instance has an unused explicit argument that Lean cannot synthesize.
@[instance_reducible] def dshowMetadata (_md : metadata T) : DShow (metadata T) := ⟨dshow_metadata⟩
instance : DShow (metadata T) := dshowMetadata .METADATA_Null
instance dshowTExp : DShow (texp T) := ⟨showExprPair false⟩

def show_phi_block (p : block_id × exp T) : DString :=
  ds "[ " <+> dshow_exp true p.2 <+> ds ", %" <+> dshow p.1 <+> ds " ]"
instance dshowPhi : DShow (phi T) where
  dshow
    | .Phi fm t ps => ds "phi" <+> fast_math_list_to_dstring fm <+> dshow t <+>
        ds " " <+> dconcat (ds ", ") (ps.map show_phi_block)

def show_opt_prefix {A : Type u} [Show A] (pre : IRString) (x : Option A) : IRString :=
  x.elim .empty (fun a ↦ pre ++ «show» a)

def dshow_opt_prefix {A : Type u} [DShow A] (pre : DString) (x : Option A) : DString :=
  x.elim DList_empty (fun a ↦ pre <+> dshow a)

def show_opt_list {A : Type u} [Show A] (x : Option A) := (x.map «show»).toList
def dshow_opt_list {A : Type u} [DShow A] (x : Option A) := (x.map dshow).toList

def show_ordering : ordering → IRString
  | .Unordered => lit "unordered"
  | .Monotonic => lit "monotonic"
  | .Acquire => lit "acquire"
  | .Release => lit "release"
  | .Acq_rel => lit "acq_rel"
  | .Seq_cst => lit "seq_cst"
instance dshowOrdering : DShow ordering := ⟨fun o ↦ sd (show_ordering o)⟩

def scopeSpace (x : Option IRString) : DString :=
  x.elim DList_empty (fun s ↦ ds "syncscope(" <+> sd («show» s) <+> ds ") ")

def show_cmpxchg (c : cmpxchg T) : DString :=
  ds "cmpxchg " <+> dshow_bool c.c_weak.isSome (lit "weak ") <+>
  dshow_bool c.c_volatile.isSome (lit "volatile ") <+> dshow c.c_ptr <+> ds ", " <+>
  dshow c.c_cmp <+> ds ", " <+> dshow c.c_new <+> ds " " <+> scopeSpace c.c_syncscope <+>
  dshow c.c_success_ordering <+> ds " " <+> dshow c.c_failure_ordering <+>
  sd (show_opt_prefix (lit ", align ") c.c_align)
instance dshowCmpxchg : DShow (cmpxchg T) := ⟨show_cmpxchg⟩

def show_a_rmw_operation : atomic_rmw_operation → IRString
  | .Axchg => lit "xchg"
  | .Aadd => lit "add"
  | .Asub => lit "sub"
  | .Aand => lit "and"
  | .Anand => lit "nand"
  | .Aor => lit "or"
  | .Axor => lit "xor"
  | .Amax => lit "max"
  | .Amin => lit "min"
  | .Aumax => lit "umax"
  | .Aumin => lit "umin"
  | .Afadd => lit "fadd"
  | .Afsub => lit "fsub"
  | .Afmax => lit "fmax"
  | .Afmin => lit "fmin"
  | .Afmaximum => lit "fmaximum"
  | .Afminimum => lit "fminimum"
  | .Auinc_wrap => lit "uinc_wrap"
  | .Audec_wrap => lit "udec_wrap"
  | .Ausub_cond => lit "usub_cond"
  | .Ausub_sat => lit "usub_sat"

instance showARmwOperation : Show atomic_rmw_operation := ⟨show_a_rmw_operation⟩

def show_atomic_rmw (a : atomicrmw T) : DString :=
  ds "atomicrmw " <+> dshow_bool a.a_volatile.isSome (lit "volatile ") <+>
  sd (show_a_rmw_operation a.a_operation) <+> ds " " <+> dshow a.a_ptr <+> ds ", " <+>
  dshow a.a_val <+> ds " " <+> scopeSpace a.a_syncscope <+> dshow a.a_ordering <+>
  sd (show_opt_prefix (lit ", align ") a.a_align)
instance showAtomicrmw : DShow (atomicrmw T) := ⟨show_atomic_rmw⟩

def show_unnamed_addr : unnamed_addr → IRString
  | .Unnamed_addr => lit "unnamed_addr"
  | .Local_Unnamed_addr => lit "local_unnamed_addr"

instance showUnnamedAddr : Show unnamed_addr := ⟨show_unnamed_addr⟩

def show_tailcall : tailcall → IRString
  | .Tail => lit "tail"
  | .Musttail => lit "musttail"
  | .Notail => lit "notail"

instance showTailcall : Show tailcall := ⟨show_tailcall⟩

def dshow_texp (x : texp T) : DString := showExprPair true x

def show_opt_space {A : Type u} (x : Option A) : IRString := if x.isSome then lit " " else .empty

def show_call_arg : texp T × List param_attr → DString
  | ((t,e), attrs) => dshow t <+> ds " " <+> dconcat (ds " ") (attrs.map dshow) <+> ds " " <+> dshow_exp true e
instance dshowCallArg : DShow (texp T × List param_attr) := ⟨show_call_arg⟩

def dshow_metadata_list (ml : List (metadata T)) := dconcat (ds " ") (ml.map dshow_metadata)
def dnewline := sd Utils.StringUtil.newline

def dshow_clause : @landingpad_clause T → DString
  | .CATCH x => ds "catch " <+> dshow_texp x <+> dnewline
  | .FILTER x => ds "filter " <+> dshow_texp x <+> dnewline

def show_syncscope (s : IRString) := lit "syncscope(\"" ++ s ++ lit "\")"

def ann_str {A : Type u} {B : Type v} (l : List A) (k : A → Option B) (render : B → IRString) :=
  (l.findSome? k).elim ByteArray.empty render

def show_operand : @operand T → DString
  | .SSA_value t => dshow_texp t
  | .Metadata_string md => dshow_metadata md

def show_operand_bundle (ob : @operand_bundle T) : DString := ds "\"" <+> sd ob.ob_tag <+>
  ds "\"(" <+> dconcat (ds ", ") (ob.ob_ops.map show_operand) <+> ds ")"

def dshow_operand_bundles : List (@operand_bundle T) → DString
  | [] => DList_empty
  | obs@(_ :: _) => ds "[" <+> dconcat (ds ", ") (obs.map show_operand_bundle) <+> ds "]"

def dshow_callee {C : Type u} {A : Type v} [Show C] [Show A] (flags : List fast_math)
    (cc : Option C) (attrs : List param_attr) (space : Option A) (fn : texp T) : DString :=
  dconcat (ds " ") ((flags.map fun f ↦ sd (show_fast_math f)) ++ (show_opt_list cc).map sd ++
    attrs.map show_param_attr ++ (show_opt_list space).map sd ++ [dshow_texp fn])

def dshow_call_suffix (attrs : List fn_attr) (obs : List (@operand_bundle T)) : DString :=
  DList_join (attrs.map fun f ↦ ds " " <+> sd (show_fn_attr f)) <+>
  (if obs.isEmpty then DList_empty else ds " " <+> dshow_operand_bundles obs)

def showCallBody (fn : texp T) (args : List (texp T × List param_attr))
    (anns : List (annotation T)) (obs : List (@operand_bundle T)) : DString :=
  dshow_callee (anns.filterMap ann_fast_math_flag) (anns.findSome? ann_cconv)
    (ann_ret_attributes anns) (anns.findSome? ann_addrspace) fn <+>
  ds "(" <+> dconcat (ds ", ") (args.map show_call_arg) <+> ds ")" <+>
  dshow_call_suffix (ann_fun_attributes anns) obs

def showMemInstr (op payload : DString) (ptr : texp T) (anns : List (annotation T)) : DString :=
  let atom := ann_str anns ann_atomic (fun _ ↦ lit "atomic")
  let vol := ann_str anns ann_volatile (fun _ ↦ lit "volatile")
  let ss := ann_str anns ann_syncscope show_syncscope
  let ord := ann_str anns ann_ordering show_ordering
  op <+> ds " " <+> sd atom <+> ds " " <+> sd vol <+> ds " " <+> payload <+> ds ", " <+>
  dshow_texp ptr <+> sd ss <+> ds " " <+> sd ord <+>
  sd (show_opt_prefix (lit ", align ") (anns.findSome? ann_align)) <+>
  DList_join ((anns.filterMap ann_metadata).map fun ml ↦ ds ", " <+> dshow_metadata_list ml)

def dshow_instr : instr T → DString
  | .INSTR_Comment s => ds "; " <+> sd s <+> ds "\\n"
  | .INSTR_Op e => dshow_exp false e
  | .INSTR_Call fn args anns obs =>
      let tail := anns.findSome? ann_tail
      sd (show_opt_prefix .empty tail) <+> sd (show_opt_space tail) <+> ds "call " <+>
      showCallBody fn args anns obs
  | .INSTR_Alloca t anns => ds "alloca " <+> sd (ann_str anns ann_inalloca (fun _ ↦ lit "inalloca")) <+>
      dshow t <+> dshow_opt_prefix (ds ", ") (anns.findSome? ann_num_elements) <+>
      sd (show_opt_prefix (lit ", align ") (anns.findSome? ann_align))
  | .INSTR_Load t ptr anns => showMemInstr (ds "load") (dshow t) ptr anns
  | .INSTR_Store x ptr anns => showMemInstr (ds "store") (dshow_texp x) ptr anns
  | .INSTR_Fence scope ord => ds "fence " <+>
      scope.elim DList_empty (fun x ↦ ds "[syncscope(\"" <+> sd («show» x) <+> ds "\")]" ) <+>
      dshow ord <+> ds " ; yields void"
  | .INSTR_AtomicCmpXchg c => show_cmpxchg c
  | .INSTR_AtomicRMW a => show_atomic_rmw a
  | .INSTR_VAArg x t => ds "va_arg " <+> dshow x <+> ds ", " <+> dshow t
  | .INSTR_LandingPad t cleanup cs => ds "landingpad " <+> dshow t <+> dnewline <+>
      dshow_bool cleanup (lit "cleanup ") <+> DList_join (cs.map dshow_clause)
instance dshowInstr : DShow (instr T) := ⟨dshow_instr⟩

def dshow_instr_id : instr_id → DString
  | .IId i => ds "%" <+> dshow_raw_id i <+> ds " = "
  | .IVoid _ => DList_empty
instance dshowInstrId : DShow instr_id := ⟨dshow_instr_id⟩

def remove_file_info (md : List (metadata T)) : List (metadata T) :=
  md.filter fun | .METADATA_File_info _ => false | _ => true

def dshow_metadata_suffix (md : List (metadata T)) :=
  DList_join ((remove_file_info md).map fun m ↦ ds ", " <+> dshow_metadata m)

def dshow_id_instr_metadata : (instr_id × instr T) × List (metadata T) → DString
  | ((iid,i),md) => dshow_instr_id iid <+> dshow_instr i <+> dshow_metadata_suffix md

def dshow_id_phi_metadata : (local_id × phi T) × List (metadata T) → DString
  | ((i,p),md) => ds "%" <+> dshow i <+> ds " = " <+> dshow p <+> dshow_metadata_suffix md

def show_tint_literal : tint_literal → IRString
  | .TInt_Literal sz x => lit "i" ++ «show» sz ++ lit " " ++ show_int_syntax x
instance showTintLiteral : Show tint_literal := ⟨show_tint_literal⟩

def dshow_terminator : terminator T → DString
  | .TERM_Ret x => ds "ret " <+> dshow_texp x
  | .TERM_Ret_void => ds "ret void"
  | .TERM_Br c a b => ds "br " <+> dshow_texp c <+> ds ", label %" <+> dshow a <+> ds ", label %" <+> dshow b
  | .TERM_Br_1 b => ds "br label %" <+> dshow b
  | .TERM_Switch x deflt brs => ds "switch " <+> dshow_texp x <+> ds ", label %" <+> dshow deflt <+> ds " [" <+>
      DList_join (brs.map fun (n, y) ↦ sd (show_tint_literal n) <+> ds ", label %" <+> dshow y <+> ds " ") <+> ds "]"
  | .TERM_IndirectBr x brs _ => ds "indirectbr " <+> dshow_texp x <+> ds ", [" <+>
      dconcat (ds ", ") (brs.map fun b ↦ ds "label %" <+> dshow b) <+> ds "]"
  | .TERM_Resume x => ds "resume " <+> dshow_texp x
  | .TERM_Invoke fn args dest unwind anns obs => ds "invoke " <+> showCallBody fn args anns obs <+>
      ds " to label %" <+> dshow dest <+> ds " unwind label %" <+> dshow unwind
  | .TERM_Unreachable => ds "unreachable"
instance dshowTerminator : DShow (terminator T) := ⟨dshow_terminator⟩

def dshow_id_terminator_metadata : (instr_id × terminator T) × List (metadata T) → DString
  | ((i,t),md) => dshow_instr_id i <+> dshow_terminator t <+> dshow_metadata_suffix md

def dshow_lines {A : Type u} (indent : DString) (render : A → DString) (xs : List A) :=
  DList_join (xs.map fun x ↦ indent <+> render x <+> dnewline)

def dshow_block (indent : IRString) (b : block T) : DString :=
  let ind := sd indent
  dshow b.blk_id <+> ds ":" <+> dnewline <+> dshow_lines ind dshow_id_phi_metadata b.blk_phis <+>
  dshow_lines ind dshow_id_instr_metadata b.blk_code <+> ind <+> dshow_id_terminator_metadata b.blk_term <+> dnewline
instance dshowBlock : DShow (block T) := ⟨dshow_block (lit "    ")⟩

def dshow_typ_instr : T × instr T → DString
  | (t,i) => ds "(" <+> dshow t <+> ds ", " <+> dshow_instr i <+> ds ")"
instance dshowTypInstr : DShow (T × instr T) := ⟨dshow_typ_instr⟩

def dshow_arg : (local_id × T) × List param_attr → DString
  | ((i,t),attrs) => dshow t <+>
      (if attrs.isEmpty then DList_empty else ds " " <+> dconcat (ds " ") (attrs.map dshow)) <+>
      ds " %" <+> dshow i
instance dshowArg : DShow ((local_id × T) × List param_attr) := ⟨dshow_arg⟩

def dshow_arg_list (args : List ((local_id × T) × List param_attr)) (varargs : Bool) :=
  ds "(" <+> dconcat (ds ", ") (args.map dshow_arg) <+> varargSuffix args.isEmpty varargs <+> ds ")"

def maybe_to_string {X : Type u} (render : X → IRString) (x : Option X) : IRString :=
  x.elim .empty (fun x ↦ render x ++ lit " ")

def maybe_to_dstring {X : Type u} (render : X → DString) (x : Option X) : DString :=
  x.elim DList_empty (fun x ↦ render x <+> ds " ")

def maybe_show {X : Type u} [Show X] := @maybe_to_string X «show»
def maybe_dshow {X : Type u} [DShow X] := @maybe_to_dstring X dshow

abbrev ASTBody := block typ × List (block typ)

def declarationFlags (p : declaration typ) : DString :=
  list_to_DString [maybe_show (dc_linkage p), maybe_show (dc_visibility p),
    maybe_show (dc_dll_storage p), maybe_show (dc_cconv p)]

def dshow_definition (f : definition typ ASTBody) : DString :=
  let p := f.df_prototype
  let name := dshow_raw_id p.dc_name
  match p.dc_type with
  | .TYPE_Function ret ts variadic =>
    let (rets, ats) := p.dc_param_attrs
    if f.df_args.length != ts.length || f.df_args.length != ats.length then
      ds "Function \"" <+> name <+> ds "\" has mismatched arguments and argument attributes length"
    else
      let args := Utils.ListUtil.zip3 f.df_args ts ats
      let sect := maybe_to_string (fun s ↦ lit "section \"" ++ s ++ lit "\" ") (dc_section p)
      let align := maybe_to_string (fun a ↦ lit "align " ++ show_int_syntax a ++ lit " ") (dc_align p)
      let pers := maybe_to_string (fun x ↦ lit " personality " ++ DString_to_string (showExprPair false x) ++ lit " ") (dc_personality p)
      ds "define " <+> declarationFlags p <+> dconcat (ds " ") (rets.map dshow) <+> ds " " <+>
      dshow ret <+> ds " @" <+> name <+> dshow_arg_list args variadic <+>
      sd sect <+> sd align <+> sd (maybe_show (dc_gc p)) <+> sd pers <+> ds " {" <+> dnewline <+>
      dconcat dnewline ((f.df_instrs.1 :: f.df_instrs.2).map dshow) <+> ds "}" <+> dnewline
  | _ => ds "Invalid type on function: " <+> name
instance dshowDefinition : DShow (definition typ ASTBody) := ⟨dshow_definition⟩

def dshow_declaration (p : declaration typ) : DString :=
  let name := dshow_raw_id p.dc_name
  match p.dc_type with
  | .TYPE_Function ret ts variadic =>
    let (rets, ats) := p.dc_param_attrs
    let sect := maybe_to_string (fun s ↦ lit "section \\" ++ s ++ lit "\\ ") (dc_section p)
    let align := maybe_to_string (fun a ↦ lit ", align " ++ show_int_syntax a ++ lit " ") (dc_align p)
    ds "declare " <+> declarationFlags p <+> dintersperse (ds " ") (rets.map dshow) <+> ds " " <+>
    dshow ret <+> ds " @" <+> name <+> ds "(" <+>
    dconcat (ds ", ") ((ts.zip ats).map fun (t,attrs) ↦
      dshow t <+> ds " " <+> attrs.head?.elim DList_empty dshow) <+>
    varargSuffix ts.isEmpty variadic <+> ds ")" <+> sd sect <+> sd align <+> sd (maybe_show (dc_gc p))
  | _ => ds "Invalid type on function: " <+> name
instance dshowDeclaration : DShow (declaration typ) := ⟨dshow_declaration⟩

def dshow_global (g : «global» typ) : DString :=
  let init := g.g_exp.elim DList_empty (dshow_exp true)
  let ty := dshow g.g_typ
  ds "@" <+> dshow g.g_ident <+> ds " = " <+>
  list_to_DString [maybe_show (g_linkage g), maybe_show (g_visibility g),
    maybe_show (g_dll_storage g), maybe_show (g_thread_local_storage g), maybe_show (g_unnamed_addr g),
    maybe_show (g_addrspace g)] <+> dshow_bool g.g_externally_initialized (lit "external ") <+>
  (if g.g_alias then
    let part := maybe_to_string (fun a ↦ lit ", partition " ++ «show» a ++ lit " ") (g_partition g)
    ds "alias " <+> ty <+> ds ", " <+> ty <+> ds "* " <+> init <+> sd part
   else
    let sect := maybe_to_string (fun s ↦ lit ", section \"" ++ s ++ lit "\"") (g_section g)
    let align := maybe_to_string (fun a ↦ lit ", align " ++ show_int_syntax a ++ lit " ") (g_align g)
    (if g.g_constant then ds "constant " else ds "global ") <+> ty <+> ds " " <+> init <+>
      sd sect <+> sd align)
instance dshowGlobal : DShow («global» typ) := ⟨dshow_global⟩

def quoted_dstring (s : IRString) : DString := sd («show» s)

def dshow_tle : toplevel_entity typ ASTBody → DString
  | .TLE_Definition f => dshow_definition f
  | .TLE_Comment s => ds ";" <+> quoted_dstring s
  | .TLE_Target s => ds "target triple = " <+> quoted_dstring s
  | .TLE_Datalayout s => ds "target datalayout = " <+> quoted_dstring s
  | .TLE_Source_filename s => ds "source_filename = " <+> quoted_dstring s
  | .TLE_Declaration p => dshow_declaration p
  | .TLE_Global g => dshow_global g
  | .TLE_Metadata i distinct md => dshow_metadata i <+> ds " = " <+>
      dshow_bool distinct (lit "distinct ") <+> dshow_metadata md
  | .TLE_Type_decl i t => dshow_ident i <+> ds " = type " <+> dshow_typ t
  | .TLE_Attribute_group n attrs => ds "attributes #" <+> sd («show» n) <+> ds " = { " <+>
      dconcat (ds " ") (attrs.map fun a ↦ sd (show_fn_attr a)) <+> ds " }"
instance dshowTLE : DShow (toplevel_entity typ ASTBody) := ⟨dshow_tle⟩
instance dshowProg : DShow (List (toplevel_entity typ ASTBody)) :=
  ⟨fun p ↦ dconcat (dnewline <+> dnewline) (p.map dshow_tle)⟩

/-- As in the extracted API, the public non-difference-list printer ignores this flag. -/
def show_exp (_b : Bool) (e : exp T) : IRString := DString_to_string (dshow_exp false e)
def showProg (p : List (toplevel_entity typ ASTBody)) : IRString := DString_to_string (dshowProg.dshow p)
def show_tle (x : toplevel_entity typ ASTBody) : IRString := DString_to_string (dshow_tle x)
def show_typ (t : typ) : IRString := DString_to_string (dshow_typ t)
def show_raw_id (i : raw_id) : IRString := DString_to_string (dshow_raw_id i)
instance showTyp : Show typ := ⟨show_typ⟩
instance DShow_Z : DShow Int := ⟨fun x ↦ sd (Utils.StringUtil.show_Z x)⟩
instance DShow_N : DShow Nat := ⟨fun n ↦ sd (Utils.StringUtil.show_N n)⟩

def show_dtyp_base : DynamicTypes.dtyp_base → IRString
  | .DTYPE_Iptr => lit "iptr"
  | .DTYPE_Pointer => lit "ptr"
  | .DTYPE_Void => lit "void"
  | .DTYPE_Label => lit "label"
  | .DTYPE_Token => lit "token"
  | .DTYPE_Metadata => lit "metadata"
  | .DTYPE_X86_mmx => lit "X86_mmx"
  | .DTYPE_Opaque => lit "Opaque"
  | .DTYPE_I n => lit "i" ++ «show» n
  | .DTYPE_B n => lit "b" ++ «show» n
  | .DTYPE_FP fp => show_floating_point_variant fp

def show_dtyp : DynamicTypes.dtyp → IRString
  | .DTYPE_Base t => show_dtyp_base t
  | .DTYPE_Struct p ts =>
    (if p then lit "<{" else lit "{") ++ concat_str_sep (lit ", ") (ts.map show_dtyp) ++
      (if p then lit "}>" else lit "}")
  | .DTYPE_Array v n t =>
    (if v then lit "<" else lit "[") ++ «show» n ++ lit " x " ++ show_dtyp t ++
      (if v then lit ">" else lit "]")
instance dshowDTyp : Show DynamicTypes.dtyp := ⟨show_dtyp⟩
instance DShow_dtyp : DShow DynamicTypes.dtyp := ⟨fun t ↦ sd (show_dtyp t)⟩

example : show_c_string (.EXP_Integer (.IntHexadecimal (.Pos (.Df (.Df .Nil)))) : exp typ) =
    lit "\\ff" := by decide +kernel
example : show_gep_flags ⟨true, true, true⟩ = lit "inbounds nuw " := rfl

end Vellvm.Syntax.ShowAST
