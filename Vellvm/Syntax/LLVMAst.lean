module

public import Vellvm.Syntax.Number
public import Vellvm.Types

@[expose] public section
namespace Vellvm.Syntax.LLVMAst

abbrev int_ast := Int

abbrev int_syntax := Number.signed_int

structure file_info where
  mk_file_info ::
  filename : IRString
  start_line : int_ast
  start_col : int_ast
  end_line : int_ast
  end_col : int_ast

export file_info (mk_file_info filename start_line start_col end_line end_col)

inductive raw_id where
  | Name (s : IRString)
  | Anon (n : int_ast)
  | Raw (n : int_ast)

export raw_id (Name Anon Raw)

inductive «ident» where
  | ID_Global (id : raw_id)
  | ID_Local (id : raw_id)

export «ident» (ID_Global ID_Local)

inductive floating_point_variant where
  | FP_half
  | FP_bfloat
  | FP_float
  | FP_double
  | FP_fp128
  | FP_x86_fp80
  | FP_ppc_fp128
  deriving DecidableEq

export floating_point_variant (FP_half FP_bfloat FP_float FP_double FP_fp128 FP_x86_fp80 FP_ppc_fp128)

def floating_point_variant_beq (x y : floating_point_variant) : Bool := decide (x = y)

def floating_point_variant_eq_dec (x y : floating_point_variant) : Decidable (x = y) := inferInstance

theorem internal_floating_point_variant_dec_bl (x y : floating_point_variant) :
    floating_point_variant_beq x y = true → x = y := of_decide_eq_true

theorem internal_floating_point_variant_dec_lb {x y : floating_point_variant} :
    x = y → floating_point_variant_beq x y = true := fun h ↦ by simp [floating_point_variant_beq, h]

inductive typ where
  | TYPE_I (sz : Positive)
  | TYPE_B (sz : Positive)
  | TYPE_Iptr
  | TYPE_Pointer (t : Option typ)
  | TYPE_Void
  | TYPE_FP (fp : floating_point_variant)
  | TYPE_Label
  | TYPE_Token
  | TYPE_Metadata
  | TYPE_X86_mmx
  | TYPE_Array (sz : Nat) (t : typ)
  | TYPE_Function (ret : typ) (args : List typ) (vararg : Bool)
  | TYPE_Struct (fields : List typ)
  | TYPE_Packed_struct (fields : List typ)
  | TYPE_Opaque
  | TYPE_Vector (sz : Nat) (t : typ)
  | TYPE_Identified (id : «ident»)

export typ (TYPE_I TYPE_B TYPE_Iptr TYPE_Pointer TYPE_Void TYPE_FP TYPE_Label TYPE_Token
  TYPE_Metadata TYPE_X86_mmx TYPE_Array TYPE_Function TYPE_Struct TYPE_Packed_struct
  TYPE_Opaque TYPE_Vector TYPE_Identified)

inductive linkage where
  | LINKAGE_Private
  | LINKAGE_Internal
  | LINKAGE_Available_externally
  | LINKAGE_Linkonce
  | LINKAGE_Weak
  | LINKAGE_Common
  | LINKAGE_Appending
  | LINKAGE_Extern_weak
  | LINKAGE_Linkonce_odr
  | LINKAGE_Weak_odr
  | LINKAGE_External

export linkage (LINKAGE_Private LINKAGE_Internal LINKAGE_Available_externally LINKAGE_Linkonce
  LINKAGE_Weak LINKAGE_Common LINKAGE_Appending LINKAGE_Extern_weak
  LINKAGE_Linkonce_odr LINKAGE_Weak_odr LINKAGE_External)

inductive preemption_specifier where
  | PREEMPTION_Dso_preemptable
  | PREEMPTION_Dso_local

export preemption_specifier (PREEMPTION_Dso_preemptable PREEMPTION_Dso_local)

inductive dll_storage where
  | DLLSTORAGE_Dllimport
  | DLLSTORAGE_Dllexport

export dll_storage (DLLSTORAGE_Dllimport DLLSTORAGE_Dllexport)

inductive visibility where
  | VISIBILITY_Default
  | VISIBILITY_Hidden
  | VISIBILITY_Protected

export visibility (VISIBILITY_Default VISIBILITY_Hidden VISIBILITY_Protected)

inductive cconv where
  | CC_Ccc
  | CC_Fastcc
  | CC_Coldcc
  | CC_Cc (cc : int_syntax)
  | CC_Webkit_jscc
  | CC_Anyregcc
  | CC_Preserve_mostcc
  | CC_Preserve_allcc
  | CC_Cxx_fast_tlscc
  | CC_Tailcc
  | CC_Swiftcc
  | CC_Swifttailcc
  | CC_cfguard_checkcc

export cconv (CC_Ccc CC_Fastcc CC_Coldcc CC_Cc CC_Webkit_jscc CC_Anyregcc CC_Preserve_mostcc
  CC_Preserve_allcc CC_Cxx_fast_tlscc CC_Tailcc CC_Swiftcc CC_Swifttailcc
  CC_cfguard_checkcc)

def cconv_number : cconv → Int
  | .CC_Ccc => 0
  | .CC_Fastcc => 8
  | .CC_Coldcc => 9
  | .CC_Cc n => n.toInt
  | .CC_Webkit_jscc => 12
  | .CC_Anyregcc => 13
  | .CC_Preserve_mostcc => 14
  | .CC_Preserve_allcc => 15
  | .CC_Swiftcc => 16
  | .CC_Cxx_fast_tlscc => 17
  | .CC_Tailcc => 18
  | .CC_cfguard_checkcc => 19
  | .CC_Swifttailcc => 20

def cconv_eqb (c₁ c₂ : cconv) : Bool := cconv_number c₁ == cconv_number c₂

inductive param_attr where
  | PARAMATTR_Zeroext
  | PARAMATTR_Signext
  | PARAMATTR_Inreg
  | PARAMATTR_Byval (t : typ)
  | PARAMATTR_Byref (t : typ)
  | PARAMATTR_Preallocated (t : typ)
  | PARAMATTR_Inalloca (t : typ)
  | PARAMATTR_Sret (t : typ)
  | PARAMATTR_Elementtype (t : typ)
  | PARAMATTR_Align (a : int_syntax)
  | PARAMATTR_Noalias
  | PARAMATTR_Nocapture
  | PARAMATTR_Nofree
  | PARAMATTR_Nest
  | PARAMATTR_Returned
  | PARAMATTR_Nonnull
  | PARAMATTR_Dereferenceable (a : int_syntax)
  | PARAMATTR_Dereferenceable_or_null (a : int_syntax)
  | PARAMATTR_Swiftself
  | PARAMATTR_Swiftasync
  | PARAMATTR_Swifterror
  | PARAMATTR_Immarg
  | PARAMATTR_Noundef
  | PARAMATTR_Nofpclass (mask : int_ast)
  | PARAMATTR_Nofreeobj
  | PARAMATTR_Alignstack (a : int_syntax)
  | PARAMATTR_Allocalign
  | PARAMATTR_Allocptr
  | PARAMATTR_Readnone
  | PARAMATTR_Readonly
  | PARAMATTR_Writeonly
  | PARAMATTR_Writable
  | PARAMATTR_Dead_on_unwind
  | PARAMATTR_Dead_on_return (size : Option int_syntax)
  | PARAMATTR_Range (t : typ) (a b : int_syntax)
  | PARAMATTR_Initializes (l : List (int_syntax × int_syntax))
  | PARAMATTR_Captures (p : (List IRString) × (List IRString))

export param_attr (PARAMATTR_Zeroext PARAMATTR_Signext PARAMATTR_Inreg PARAMATTR_Byval
  PARAMATTR_Byref PARAMATTR_Preallocated PARAMATTR_Inalloca PARAMATTR_Sret
  PARAMATTR_Elementtype PARAMATTR_Align PARAMATTR_Noalias PARAMATTR_Nocapture
  PARAMATTR_Nofree PARAMATTR_Nest PARAMATTR_Returned PARAMATTR_Nonnull
  PARAMATTR_Dereferenceable PARAMATTR_Dereferenceable_or_null PARAMATTR_Swiftself
  PARAMATTR_Swiftasync PARAMATTR_Swifterror PARAMATTR_Immarg PARAMATTR_Noundef
  PARAMATTR_Nofpclass PARAMATTR_Nofreeobj PARAMATTR_Alignstack PARAMATTR_Allocalign
  PARAMATTR_Allocptr PARAMATTR_Readnone PARAMATTR_Readonly PARAMATTR_Writeonly
  PARAMATTR_Writable PARAMATTR_Dead_on_unwind PARAMATTR_Dead_on_return
  PARAMATTR_Range PARAMATTR_Initializes PARAMATTR_Captures)

def nofpclass_names : List (IRString × int_ast) :=
  [("all".toUTF8, 1023), ("nan".toUTF8, 3), ("snan".toUTF8, 1),
   ("qnan".toUTF8, 2), ("inf".toUTF8, 516), ("ninf".toUTF8, 4),
   ("pinf".toUTF8, 512), ("zero".toUTF8, 96), ("nzero".toUTF8, 32),
   ("pzero".toUTF8, 64), ("sub".toUTF8, 144), ("nsub".toUTF8, 16),
   ("psub".toUTF8, 128), ("norm".toUTF8, 264), ("nnorm".toUTF8, 8),
   ("pnorm".toUTF8, 256)]

def nofpclass_mask (words : List IRString) : Option int_ast := do
  let mask ← words.foldlM (m := Option) (init := 0) fun acc w ↦ do
    let bits ← nofpclass_names.lookup w
    pure (Nat.lor acc bits.toNat)
  return Int.ofNat mask

def nofpclass_mask_valid (mask : int_ast) : Bool := decide (0 < mask ∧ mask ≤ 1023)

def nofpclass_words (mask : int_ast) : List IRString :=
  -- Every class occupies the low ten bits, including for negative input masks.
  let (_, names) := nofpclass_names.foldl (init := ((mask % 1024).toNat, []))
    fun (remaining, names) (name, bits) ↦
      let b := bits.toNat
      if Nat.land remaining b == b then (remaining - b, name :: names) else (remaining, names)
  names.reverse

inductive frame_pointer_val where
  | FRAMEPTR_None
  | FRAMEPTR_Non_leaf
  | FRAMEPTR_All

export frame_pointer_val (FRAMEPTR_None FRAMEPTR_Non_leaf FRAMEPTR_All)

inductive mem_loc where
  | LOC_Default
  | LOC_Argmem
  | LOC_Inaccessiblemem
  | LOC_Errnomem

export mem_loc (LOC_Default LOC_Argmem LOC_Inaccessiblemem LOC_Errnomem)

inductive mem_access_kind where
  | ACC_None
  | ACC_Read
  | ACC_Write
  | ACC_Readwrite

export mem_access_kind (ACC_None ACC_Read ACC_Write ACC_Readwrite)

inductive fn_attr where
  | FNATTR_Alignstack (a : int_syntax)
  | FNATTR_Allockind (kind : IRString)
  | FNATTR_Allocsize (a1 : int_syntax) (a2 : Option int_syntax)
  | FNATTR_Alwaysinline
  | FNATTR_Builtin
  | FNATTR_Cold
  | FNATTR_Convergent
  | FNATTR_Disable_sanitizer_instrumentation
  | FNATTR_Fn_ret_thunk_extern
  | FNATTR_Hot
  | FNATTR_Inaccessiblememonly
  | FNATTR_Inaccessiblemem_or_argmemonly
  | FNATTR_Inlinehint
  | FNATTR_Jumptable
  | FNATTR_Minsize
  | FNATTR_Naked
  | FNATTR_No_jump_tables
  | FNATTR_Nobuiltin
  | FNATTR_Noduplicate
  | FNATTR_Nofree
  | FNATTR_Noimplicitfloat
  | FNATTR_Noinline
  | FNATTR_Nomerge
  | FNATTR_Nonlazybind
  | FNATTR_Noprofile
  | FNATTR_Noredzone
  | FNATTR_Indirect_tls_seg_refs
  | FNATTR_Noreturn
  | FNATTR_Norecurse
  | FNATTR_Willreturn
  | FNATTR_Nosync
  | FNATTR_Nounwind
  | FNATTR_Nocreateundeforpoison
  | FNATTR_Nosanitize_bounds
  | FNATTR_Nosanitize_coverage
  | FNATTR_Null_pointer_is_valid
  | FNATTR_Optforfuzzing
  | FNATTR_Optnone
  | FNATTR_Optsize
  | FNATTR_Readnone
  | FNATTR_Readonly
  | FNATTR_Writeonly
  | FNATTR_Argmemonly
  | FNATTR_Returns_twice
  | FNATTR_Safestack
  | FNATTR_Sanitize_address
  | FNATTR_Sanitize_memory
  | FNATTR_Sanitize_thread
  | FNATTR_Sanitize_hwaddress
  | FNATTR_Sanitize_memtag
  | FNATTR_Speculative_load_hardening
  | FNATTR_Speculatable
  | FNATTR_Ssp
  | FNATTR_Sspstrong
  | FNATTR_Sspreq
  | FNATTR_Strictfp
  | FNATTR_Tls_load_hoist
  | FNATTR_Uwtable (sync : Option Bool)
  | FNATTR_Nocf_check
  | FNATTR_Shadowcallstack
  | FNATTR_Mustprogress
  | FNATTR_Vscale_range (min : int_syntax) («max» : Option int_syntax)
  | FNATTR_String (s : IRString)
  | FNATTR_Key_value (kv : IRString × IRString)
  | FNATTR_Attr_grp (g : int_ast)
  | FNATTR_Memory (effs : List (mem_loc × mem_access_kind))
  | FNATTR_UNKNOWN (s : IRString)

export fn_attr (FNATTR_Alignstack FNATTR_Allockind FNATTR_Allocsize FNATTR_Alwaysinline
  FNATTR_Builtin FNATTR_Cold FNATTR_Convergent FNATTR_Disable_sanitizer_instrumentation
  FNATTR_Fn_ret_thunk_extern FNATTR_Hot FNATTR_Inaccessiblememonly
  FNATTR_Inaccessiblemem_or_argmemonly FNATTR_Inlinehint FNATTR_Jumptable
  FNATTR_Minsize FNATTR_Naked FNATTR_No_jump_tables FNATTR_Nobuiltin FNATTR_Noduplicate
  FNATTR_Nofree FNATTR_Noimplicitfloat FNATTR_Noinline FNATTR_Nomerge
  FNATTR_Nonlazybind FNATTR_Noprofile FNATTR_Noredzone FNATTR_Indirect_tls_seg_refs
  FNATTR_Noreturn FNATTR_Norecurse FNATTR_Willreturn FNATTR_Nosync FNATTR_Nounwind
  FNATTR_Nocreateundeforpoison FNATTR_Nosanitize_bounds FNATTR_Nosanitize_coverage
  FNATTR_Null_pointer_is_valid FNATTR_Optforfuzzing FNATTR_Optnone FNATTR_Optsize
  FNATTR_Readnone FNATTR_Readonly FNATTR_Writeonly FNATTR_Argmemonly
  FNATTR_Returns_twice FNATTR_Safestack FNATTR_Sanitize_address FNATTR_Sanitize_memory
  FNATTR_Sanitize_thread FNATTR_Sanitize_hwaddress FNATTR_Sanitize_memtag
  FNATTR_Speculative_load_hardening FNATTR_Speculatable FNATTR_Ssp FNATTR_Sspstrong
  FNATTR_Sspreq FNATTR_Strictfp FNATTR_Tls_load_hoist FNATTR_Uwtable FNATTR_Nocf_check
  FNATTR_Shadowcallstack FNATTR_Mustprogress FNATTR_Vscale_range FNATTR_String
  FNATTR_Key_value FNATTR_Attr_grp FNATTR_Memory FNATTR_UNKNOWN)

inductive thread_local_storage where
  | TLS_NONE
  | TLS_Localdynamic
  | TLS_Initialexec
  | TLS_Localexec

export thread_local_storage (TLS_NONE TLS_Localdynamic TLS_Initialexec TLS_Localexec)

abbrev local_id := raw_id

abbrev global_id := raw_id

abbrev block_id := raw_id

abbrev function_id := global_id

inductive icmp where
  | Eq
  | Ne
  | Ugt
  | Uge
  | Ult
  | Ule
  | Sgt
  | Sge
  | Slt
  | Sle

export icmp (Eq Ne Ugt Uge Ult Ule Sgt Sge Slt Sle)

inductive fcmp where
  | FFalse
  | FOeq
  | FOgt
  | FOge
  | FOlt
  | FOle
  | FOne
  | FOrd
  | FUno
  | FUeq
  | FUgt
  | FUge
  | FUlt
  | FUle
  | FUne
  | FTrue

export fcmp (FFalse FOeq FOgt FOge FOlt FOle FOne FOrd FUno FUeq FUgt FUge FUlt FUle FUne FTrue)

inductive ibinop where
  | Add (nuw : Bool) (nsw : Bool)
  | Sub (nuw : Bool) (nsw : Bool)
  | Mul (nuw : Bool) (nsw : Bool)
  | Shl (nuw : Bool) (nsw : Bool)
  | UDiv («exact» : Bool)
  | SDiv («exact» : Bool)
  | LShr («exact» : Bool)
  | AShr («exact» : Bool)
  | URem
  | SRem
  | And
  | Or (disjoint : Bool)
  | Xor

export ibinop (Add Sub Mul Shl UDiv SDiv LShr AShr URem SRem And Or Xor)

inductive fbinop where
  | FAdd
  | FSub
  | FMul
  | FDiv
  | FRem

export fbinop (FAdd FSub FMul FDiv FRem)

inductive fast_math where
  | Nnan
  | Ninf
  | Nsz
  | Arcp
  | Contract
  | Afn
  | Reassoc
  | Fast

export fast_math (Nnan Ninf Nsz Arcp Contract Afn Reassoc Fast)

inductive pure_conversion where
  | Trunc (nuw : Bool) (nsw : Bool)
  | Zext (nneg : Bool)
  | Sext
  | Fptrunc (flags : List fast_math)
  | Fpext (flags : List fast_math)
  | Uitofp (nneg : Bool)
  | Sitofp
  | Fptoui
  | Fptosi

export pure_conversion (Trunc Zext Sext Fptrunc Fpext Uitofp Sitofp Fptoui Fptosi)

inductive impure_conversion where
  | Inttoptr
  | Ptrtoint
  | Ptrtoaddr
  | Addrspacecast

export impure_conversion (Inttoptr Ptrtoint Ptrtoaddr Addrspacecast)

inductive conversion_type where
  | CONV_Bitcast
  | CONV_Pure (c : pure_conversion)
  | CONV_Impure (c : impure_conversion)

export conversion_type (CONV_Bitcast CONV_Pure CONV_Impure)

structure gep_flags where
  mk_gep_flags ::
  gep_inbounds : Bool
  gep_nusw : Bool
  gep_nuw : Bool

export gep_flags (mk_gep_flags gep_inbounds gep_nusw gep_nuw)

def gep_no_flags : gep_flags := ⟨false, false, false⟩

variable {T : Type}

abbrev tident {T : Type} := T × «ident»

inductive float_hex_type where
  | FH_X
  | FH_K
  | FH_L
  | FH_M
  | FH_H
  | FH_R

export float_hex_type (FH_X FH_K FH_L FH_M FH_H FH_R)

inductive float_syntax where
  | FS_decimal (d : Decimal.decimal)
  | FS_hex (t : float_hex_type) (u : Hexadecimal.uint)

export float_syntax (FS_decimal FS_hex)

mutual
  inductive exp (T : Type) where
    | EXP_Ident (id : «ident»)
    | EXP_Integer (x : int_syntax)
    | EXP_Float (f : float_syntax)
    | EXP_Bool (b : Bool)
    | EXP_Null
    | EXP_Zero_initializer
    | EXP_Cstring (elts : List (T × (exp T)))
    | EXP_Undef
    | EXP_Poison
    | EXP_Struct (fields : List (T × (exp T)))
    | EXP_Packed_struct (fields : List (T × (exp T)))
    | EXP_Array (elts : List (T × (exp T)))
    | EXP_Vector (elts : List (T × (exp T)))
    | OP_IBinop (iop : ibinop) (t : T) (v1 : exp T) (v2 : exp T)
    | OP_ICmp (samesign : Bool) (cmp : icmp) (t : T) (v1 : exp T) (v2 : exp T)
    | OP_FBinop (fop : fbinop) (fm : List fast_math) (t : T) (v1 : exp T) (v2 : exp T)
    | OP_Fneg (flags : List fast_math) (v : T × (exp T))
    | OP_FCmp (cmp : fcmp) (fm : List fast_math) (t : T) (v1 : exp T) (v2 : exp T)
    | OP_Conversion (conv : conversion_type) (t_from : T) (v : exp T) (t_to : T)
    | OP_GetElementPtr (flags : gep_flags) (t : T) (ptrval : T × (exp T)) (idxs : List (T × (exp T)))
    | OP_ExtractElement (vec : T × (exp T)) (idx : T × (exp T))
    | OP_InsertElement (vec : T × (exp T)) (elt : T × (exp T)) (idx : T × (exp T))
    | OP_ShuffleVector (vec1 : T × (exp T)) (vec2 : T × (exp T)) (idxmask : T × (exp T))
    | OP_ExtractValue (vec : T × (exp T)) (idxs : List int_syntax)
    | OP_InsertValue (vec : T × (exp T)) (elt : T × (exp T)) (idxs : List int_syntax)
    | OP_Select (fm : List fast_math) (cnd : T × (exp T)) (v1 : T × (exp T)) (v2 : T × (exp T))
    | OP_Freeze (v : T × (exp T))
    | EXP_Asm (sideffect : Bool) (alignstack : Bool) (inteldialect : Bool) (unwind : Bool)
        (template : IRString) (operand_constraints : IRString)
    | EXP_Metadata (m : metadata T)
    | EXP_Splat (elt : T × (exp T))
    | EXP_BlockAddress (fn : function_id) (blk : block_id)

  inductive metadata (T : Type) where
    | METADATA_Null
    | METADATA_Id (id : raw_id)
    | METADATA_Const (tv : T × (exp T))
    | METADATA_Node (mds : List (metadata T))
    | METADATA_Pair (md1 md2 : metadata T)
    | METADATA_Debug (DIstr : IRString) (contents : IRString)
    | METADATA_File_info (finfo : file_info)
end

export exp (EXP_Ident EXP_Integer EXP_Float EXP_Bool EXP_Null EXP_Zero_initializer EXP_Cstring
  EXP_Undef EXP_Poison EXP_Struct EXP_Packed_struct EXP_Array EXP_Vector OP_IBinop OP_ICmp
  OP_FBinop OP_Fneg OP_FCmp OP_Conversion OP_GetElementPtr OP_ExtractElement
  OP_InsertElement OP_ShuffleVector OP_ExtractValue OP_InsertValue OP_Select OP_Freeze
  EXP_Asm EXP_Metadata EXP_Splat EXP_BlockAddress)
export metadata (METADATA_Null METADATA_Id METADATA_Const METADATA_Node METADATA_Pair METADATA_Debug
  METADATA_File_info)

abbrev texp (T : Type) := T × exp T

inductive tint_literal where
  | TInt_Literal (sz : Positive) (x : int_syntax)

export tint_literal (TInt_Literal)

inductive instr_id where
  | IId (id : raw_id)
  | IVoid (n : int_ast)

export instr_id (IId IVoid)

inductive phi (T : Type) where
  | Phi (fm : List fast_math) (t : T) (args : List (block_id × (exp T)))

export phi (Phi)

inductive ordering where
  | Unordered
  | Monotonic
  | Acquire
  | Release
  | Acq_rel
  | Seq_cst

export ordering (Unordered Monotonic Acquire Release Acq_rel Seq_cst)

structure cmpxchg (T : Type) where
  mk_cmpxchg ::
  c_weak : Option Unit
  c_volatile : Option Unit
  c_ptr : texp T
  c_cmp : texp T
  c_new : texp T
  c_syncscope : Option IRString
  c_success_ordering : ordering
  c_failure_ordering : ordering
  c_align : Option int_syntax

export cmpxchg (mk_cmpxchg c_weak c_volatile c_ptr c_cmp c_new c_syncscope c_success_ordering
  c_failure_ordering c_align)

inductive atomic_rmw_operation where
  | Axchg
  | Aadd
  | Asub
  | Aand
  | Anand
  | Aor
  | Axor
  | Amax
  | Amin
  | Aumax
  | Aumin
  | Afadd
  | Afsub
  | Afmax
  | Afmin
  | Afmaximum
  | Afminimum
  | Auinc_wrap
  | Audec_wrap
  | Ausub_cond
  | Ausub_sat

export atomic_rmw_operation (Axchg Aadd Asub Aand Anand Aor Axor Amax Amin Aumax Aumin Afadd Afsub
  Afmax Afmin Afmaximum Afminimum Auinc_wrap Audec_wrap Ausub_cond
  Ausub_sat)

structure atomicrmw (T : Type) where
  mk_atomicrmw ::
  a_volatile : Option Unit
  a_operation : atomic_rmw_operation
  a_ptr : texp T
  a_val : texp T
  a_syncscope : Option IRString
  a_ordering : ordering
  a_align : Option int_syntax

export atomicrmw (mk_atomicrmw a_volatile a_operation a_ptr a_val a_syncscope a_ordering a_align)

inductive unnamed_addr where
  | Unnamed_addr
  | Local_Unnamed_addr

export unnamed_addr (Unnamed_addr Local_Unnamed_addr)

inductive tailcall where
  | Tail
  | Musttail
  | Notail

export tailcall (Tail Musttail Notail)

inductive annotation (T : Type) where
  | ANN_linkage (l : linkage)
  | ANN_preemption_specifier (p : preemption_specifier)
  | ANN_visibility (v : visibility)
  | ANN_dll_storage (d : dll_storage)
  | ANN_thread_local_storage (t : thread_local_storage)
  | ANN_unnamed_addr (u : unnamed_addr)
  | ANN_addrspace (n : int_syntax)
  | ANN_section (s : IRString)
  | ANN_partition (s : IRString)
  | ANN_comdat (l : local_id)
  | ANN_align (n : int_syntax)
  | ANN_no_sanitize
  | ANN_no_sanitize_address
  | ANN_no_sanitize_hwaddress
  | ANN_sanitize_address_dyninit
  | ANN_metadata (l : List (metadata T))
  | ANN_cconv (c : cconv)
  | ANN_gc (s : IRString)
  | ANN_prefix (t : texp T)
  | ANN_prologue (t : texp T)
  | ANN_personality (t : texp T)
  | ANN_inalloca
  | ANN_num_elements (t : texp T)
  | ANN_volatile
  | ANN_tail (t : tailcall)
  | ANN_fast_math_flag (f : fast_math)
  | ANN_ret_attribute (p : param_attr)
  | ANN_fun_attribute (f : fn_attr)
  | ANN_atomic
  | ANN_syncscope (s : IRString)
  | ANN_ordering (o : ordering)

export annotation (ANN_linkage ANN_preemption_specifier ANN_visibility ANN_dll_storage
  ANN_thread_local_storage ANN_unnamed_addr ANN_addrspace ANN_section ANN_partition
  ANN_comdat ANN_align ANN_no_sanitize ANN_no_sanitize_address
  ANN_no_sanitize_hwaddress ANN_sanitize_address_dyninit ANN_metadata ANN_cconv
  ANN_gc ANN_prefix ANN_prologue ANN_personality ANN_inalloca ANN_num_elements
  ANN_volatile ANN_tail ANN_fast_math_flag ANN_ret_attribute ANN_fun_attribute
  ANN_atomic ANN_syncscope ANN_ordering)

def ann_linkage : annotation T → Option linkage
  | .ANN_linkage l => some l
  | _ => none

def ann_preemption_specifier : annotation T → Option preemption_specifier
  | .ANN_preemption_specifier p => some p
  | _ => none

def ann_visibility : annotation T → Option visibility
  | .ANN_visibility v => some v
  | _ => none

def ann_dll_storage : annotation T → Option dll_storage
  | .ANN_dll_storage d => some d
  | _ => none

def ann_thread_local_storage : annotation T → Option thread_local_storage
  | .ANN_thread_local_storage t => some t
  | _ => none

def ann_unnamed_addr : annotation T → Option unnamed_addr
  | .ANN_unnamed_addr a => some a
  | _ => none

def ann_addrspace : annotation T → Option int_syntax
  | .ANN_addrspace a => some a
  | _ => none

def ann_section : annotation T → Option IRString
  | .ANN_section s => some s
  | _ => none

def ann_partition : annotation T → Option IRString
  | .ANN_partition p => some p
  | _ => none

def ann_comdat : annotation T → Option local_id
  | .ANN_comdat s => some s
  | _ => none

def ann_align : annotation T → Option int_syntax
  | .ANN_align n => some n
  | _ => none

def ann_no_sanitize : annotation T → Option Unit
  | .ANN_no_sanitize => some ()
  | _ => none

def ann_no_sanitize_address : annotation T → Option Unit
  | .ANN_no_sanitize_address => some ()
  | _ => none

def ann_no_sanitize_hwaddress : annotation T → Option Unit
  | .ANN_no_sanitize_hwaddress => some ()
  | _ => none

def ann_sanitize_address_dynint : annotation T → Option Unit
  | .ANN_sanitize_address_dyninit => some ()
  | _ => none

def ann_metadata : annotation T → Option (List (metadata T))
  | .ANN_metadata l => some l
  | _ => none

def ann_cconv : annotation T → Option cconv
  | .ANN_cconv c => some c
  | _ => none

def ann_gc : annotation T → Option IRString
  | .ANN_gc s => some s
  | _ => none

def ann_prefix : annotation T → Option (texp T)
  | .ANN_prefix t => some t
  | _ => none

def ann_prologue : annotation T → Option (texp T)
  | .ANN_prologue t => some t
  | _ => none

def ann_personality : annotation T → Option (texp T)
  | .ANN_personality t => some t
  | _ => none

def ann_inalloca : annotation T → Option Unit
  | .ANN_inalloca => some ()
  | _ => none

def ann_num_elements : annotation T → Option (texp T)
  | .ANN_num_elements t => some t
  | _ => none

def ann_volatile : annotation T → Option Unit
  | .ANN_volatile => some ()
  | _ => none

def ann_tail : annotation T → Option tailcall
  | .ANN_tail t => some t
  | _ => none

def ann_fast_math_flag : annotation T → Option fast_math
  | .ANN_fast_math_flag f => some f
  | _ => none

def ann_ret_attribute : annotation T → Option param_attr
  | .ANN_ret_attribute p => some p
  | _ => none

def ann_ret_attributes (anns : List (annotation T)) : List param_attr :=
  anns.filterMap ann_ret_attribute

def ann_fun_attribute : annotation T → Option fn_attr
  | .ANN_fun_attribute f => some f
  | _ => none

def ann_fun_attributes (anns : List (annotation T)) : List fn_attr :=
  anns.filterMap ann_fun_attribute

def fn_attr_is_noreturn : fn_attr → Bool
  | .FNATTR_Noreturn => true
  | _ => false

def fn_attr_is_nounwind : fn_attr → Bool
  | .FNATTR_Nounwind => true
  | _ => false

def fn_attr_is_nocreateundeforpoison : fn_attr → Bool
  | .FNATTR_Nocreateundeforpoison => true
  | _ => false

def ann_atomic : annotation T → Option Unit
  | .ANN_atomic => some ()
  | _ => none

def ann_syncscope : annotation T → Option IRString
  | .ANN_syncscope s => some s
  | _ => none

def ann_ordering : annotation T → Option ordering
  | .ANN_ordering o => some o
  | _ => none

def attr_align : param_attr → Option int_syntax
  | .PARAMATTR_Align n => some n
  | _ => none

def attr_dereferenceable : param_attr → Option (Bool × int_syntax)
  | .PARAMATTR_Dereferenceable n => some (false, n)
  | .PARAMATTR_Dereferenceable_or_null n => some (true, n)
  | _ => none

def attr_nofpclass : param_attr → Option int_ast
  | .PARAMATTR_Nofpclass mask => some mask
  | _ => none

def attr_range : param_attr → Option (int_syntax × int_syntax)
  | .PARAMATTR_Range _ lo hi => some (lo, hi)
  | _ => none

def load_metadata_attr : metadata T → List param_attr
  | .METADATA_Pair (.METADATA_Id (.Name name)) node =>
    if name == "nonnull".toUTF8 then [.PARAMATTR_Nonnull]
    else if name == "noundef".toUTF8 then [.PARAMATTR_Noundef]
    else match node with
      | .METADATA_Node [.METADATA_Const (_, .EXP_Integer n)] =>
        if name == "align".toUTF8 then [.PARAMATTR_Align n]
        else if name == "nofpclass".toUTF8 then [.PARAMATTR_Nofpclass n.toInt]
        else []
      | _ => []
  | _ => []

def load_metadata_attrs (mds : List (metadata T)) : List param_attr :=
  mds.flatMap load_metadata_attr

def metadata_range_pairs : List (metadata T) → List (int_syntax × int_syntax)
  | .METADATA_Const (_, .EXP_Integer lo) :: .METADATA_Const (_, .EXP_Integer hi) :: rest =>
    (lo, hi) :: metadata_range_pairs rest
  | _ => []

def metadata_range (mds : List (metadata T)) : Option (List (int_syntax × int_syntax)) :=
  mds.findSome? fun
    | .METADATA_Pair (.METADATA_Id (.Name name)) (.METADATA_Node ns) =>
      if name == "range".toUTF8 then some (metadata_range_pairs ns) else none
    | _ => none

def load_metadata_dereferenceable (mds : List (metadata T)) : Option (Bool × int_syntax) :=
  mds.findSome? fun
    | .METADATA_Pair (.METADATA_Id (.Name name)) (.METADATA_Node [.METADATA_Const (_, .EXP_Integer n)]) =>
      if name == "dereferenceable".toUTF8 then some (false, n)
      else if name == "dereferenceable_or_null".toUTF8 then some (true, n)
      else none
    | _ => none

inductive operand {T : Type} where
  | SSA_value (t : texp T)
  | Metadata_string (m : metadata T)

export operand (SSA_value Metadata_string)

structure operand_bundle {T : Type} where
  mk_operand_bundle ::
  ob_tag : IRString
  ob_ops : List (@operand T)

export operand_bundle (mk_operand_bundle ob_tag ob_ops)

inductive landingpad_clause {T : Type} where
  | CATCH (t : texp T)
  | FILTER (t : texp T)

export landingpad_clause (CATCH FILTER)

inductive instr (T : Type) where
  | INSTR_Comment (msg : IRString)
  | INSTR_Op (op : exp T)
  | INSTR_Call (fn : texp T) (args : List ((texp T) × (List param_attr)))
      (anns : List (annotation T)) (obs : List (@operand_bundle T))
  | INSTR_Alloca (t : T) (anns : List (annotation T))
  | INSTR_Load (t : T) (ptr : texp T) (anns : List (annotation T))
  | INSTR_Store (val : texp T) (ptr : texp T) (anns : List (annotation T))
  | INSTR_Fence (syncscope : Option IRString) (o : ordering)
  | INSTR_AtomicCmpXchg (c : cmpxchg T)
  | INSTR_AtomicRMW (a : atomicrmw T)
  | INSTR_VAArg (va_list_and_arg_list : texp T) (t : T)
  | INSTR_LandingPad (resultty : T) (cleanup : Bool) (cs : List (@landingpad_clause T))

export instr (INSTR_Comment INSTR_Op INSTR_Call INSTR_Alloca INSTR_Load INSTR_Store INSTR_Fence
  INSTR_AtomicCmpXchg INSTR_AtomicRMW INSTR_VAArg INSTR_LandingPad)

inductive terminator (T : Type) where
  | TERM_Ret (v : texp T)
  | TERM_Ret_void
  | TERM_Br (v : texp T) (br1 : block_id) (br2 : block_id)
  | TERM_Br_1 (br : block_id)
  | TERM_Switch (v : texp T) (default_dest : block_id) (brs : List (tint_literal × block_id))
  | TERM_IndirectBr (v : texp T) (brs : List block_id) (fn : Option function_id)
  | TERM_Resume (v : texp T)
  | TERM_Invoke (fnptrval : texp T) (args : List ((texp T) × (List param_attr)))
      (to_label : block_id) (unwind_label : block_id) (anns : List (annotation T))
      (obs : List (@operand_bundle T))
  | TERM_Unreachable

export terminator (TERM_Ret TERM_Ret_void TERM_Br TERM_Br_1 TERM_Switch TERM_IndirectBr TERM_Resume
  TERM_Invoke TERM_Unreachable)

structure «global» (T : Type) where
  mk_global ::
  g_ident : global_id
  g_typ : T
  g_constant : Bool
  g_exp : Option (exp T)
  g_externally_initialized : Bool
  g_alias : Bool
  g_annotations : List (annotation T)

export «global» (mk_global g_ident g_typ g_constant g_exp g_externally_initialized g_alias
  g_annotations)

def g_linkage (g : «global» T) : Option linkage :=
  g.g_annotations.findSome? ann_linkage

def g_visibility (g : «global» T) : Option visibility :=
  g.g_annotations.findSome? ann_visibility

def g_dll_storage (g : «global» T) : Option dll_storage :=
  g.g_annotations.findSome? ann_dll_storage

def g_thread_local_storage (g : «global» T) : Option thread_local_storage :=
  g.g_annotations.findSome? ann_thread_local_storage

def g_unnamed_addr (g : «global» T) : Option unnamed_addr :=
  g.g_annotations.findSome? ann_unnamed_addr

def g_addrspace (g : «global» T) : Option int_syntax :=
  g.g_annotations.findSome? ann_addrspace

def g_section (g : «global» T) : Option IRString :=
  g.g_annotations.findSome? ann_section

def g_partition (g : «global» T) : Option IRString :=
  g.g_annotations.findSome? ann_partition

def g_comdat (g : «global» T) : Option local_id :=
  g.g_annotations.findSome? ann_comdat

def g_align (g : «global» T) : Option int_syntax :=
  g.g_annotations.findSome? ann_align

def g_no_sanitize (g : «global» T) : Option Unit :=
  g.g_annotations.findSome? ann_no_sanitize

def g_no_sanitize_address (g : «global» T) : Option Unit :=
  g.g_annotations.findSome? ann_no_sanitize_address

def g_no_sanitize_hwaddress (g : «global» T) : Option Unit :=
  g.g_annotations.findSome? ann_no_sanitize_hwaddress

def g_sanitize_address_dyninit (g : «global» T) : Option Unit :=
  g.g_annotations.findSome? ann_sanitize_address_dynint

def g_metadata (g : «global» T) : List (List (metadata T)) :=
  g.g_annotations.filterMap ann_metadata

structure declaration (T : Type) where
  mk_declaration ::
  dc_name : function_id
  dc_type : T
  dc_param_attrs : List param_attr × List (List param_attr)
  dc_attrs : List fn_attr
  dc_annotations : List (annotation T)

export declaration (mk_declaration dc_name dc_type dc_param_attrs dc_attrs dc_annotations)

def dc_linkage (d : declaration T) : Option linkage :=
  d.dc_annotations.findSome? ann_linkage

def dc_visibility (d : declaration T) : Option visibility :=
  d.dc_annotations.findSome? ann_visibility

def dc_dll_storage (d : declaration T) : Option dll_storage :=
  d.dc_annotations.findSome? ann_dll_storage

def dc_thread_local_storage (d : declaration T) : Option thread_local_storage :=
  d.dc_annotations.findSome? ann_thread_local_storage

def dc_unnamed_addr (d : declaration T) : Option unnamed_addr :=
  d.dc_annotations.findSome? ann_unnamed_addr

def dc_addrspace (d : declaration T) : Option int_syntax :=
  d.dc_annotations.findSome? ann_addrspace

def dc_section (d : declaration T) : Option IRString :=
  d.dc_annotations.findSome? ann_section

def dc_partition (d : declaration T) : Option IRString :=
  d.dc_annotations.findSome? ann_partition

def dc_comdat (d : declaration T) : Option local_id :=
  d.dc_annotations.findSome? ann_comdat

def dc_align (d : declaration T) : Option int_syntax :=
  d.dc_annotations.findSome? ann_align

def dc_cconv (d : declaration T) : Option cconv :=
  d.dc_annotations.findSome? ann_cconv

def anns_cconv (anns : List (annotation T)) : cconv := (anns.findSome? ann_cconv).getD .CC_Ccc

def dc_gc (d : declaration T) : Option IRString :=
  d.dc_annotations.findSome? ann_gc

def dc_prefix (d : declaration T) : Option (texp T) :=
  d.dc_annotations.findSome? ann_prefix

def dc_prologue (d : declaration T) : Option (texp T) :=
  d.dc_annotations.findSome? ann_prologue

def dc_personality (d : declaration T) : Option (texp T) :=
  d.dc_annotations.findSome? ann_personality

def dc_metadata (d : declaration T) : List (List (metadata T)) :=
  d.dc_annotations.filterMap ann_metadata

abbrev code (T : Type) := List ((instr_id × instr T) × List (metadata T))

structure block (T : Type) where
  mk_block ::
  blk_id : block_id
  blk_phis : List ((local_id × (phi T)) × (List (metadata T)))
  blk_code : code T
  blk_term : (instr_id × (terminator T)) × (List (metadata T))
  blk_comments : Option (List IRString)

export block (mk_block blk_id blk_phis blk_code blk_term blk_comments)

structure definition (T FnBody : Type) where
  mk_definition ::
  df_prototype : declaration T
  df_args : List local_id
  df_instrs : FnBody

export definition (mk_definition df_prototype df_args df_instrs)

inductive toplevel_entity (T FnBody : Type) where
  | TLE_Comment (msg : IRString)
  | TLE_Target (tgt : IRString)
  | TLE_Datalayout (layout : IRString)
  | TLE_Declaration (decl : declaration T)
  | TLE_Definition (defn : definition T FnBody)
  | TLE_Type_decl (id : «ident») (t : T)
  | TLE_Source_filename (s : IRString)
  | TLE_Global (g : «global» T)
  | TLE_Metadata (id : metadata T) (distinct : Bool) (md : metadata T)
  | TLE_Attribute_group (i : int_ast) (attrs : List fn_attr)

export toplevel_entity (TLE_Comment TLE_Target TLE_Datalayout TLE_Declaration TLE_Definition
  TLE_Type_decl TLE_Source_filename TLE_Global TLE_Metadata TLE_Attribute_group)

abbrev toplevel_entities (T FnBody : Type) := List (toplevel_entity T FnBody)

end Vellvm.Syntax.LLVMAst
