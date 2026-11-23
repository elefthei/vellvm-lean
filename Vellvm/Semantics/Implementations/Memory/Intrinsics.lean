import Vellvm.Semantics.Implementations.Memory.Bytes
import Vellvm.Semantics.IntrinsicsDefinitions.Families
import Vellvm.Semantics.DynamicValues.Core
import Vellvm.Semantics.LLVMEvents

namespace Vellvm.Semantics.Implementations.Memory

open Interfaces.Params Interfaces.Memory DynamicValues MemoryBytes Numeric.Integers

universe u v w z r
variable [Pa : Params] [MMP : MemoryModelPrimitives.{u,v,w,z,r}]

def malloc_bytes (init_bytes : List memory_byte) (align : Nat) :
    memM (MMS := MMP.mm_state) Pa.PTR.ptr := do
  let pr ← fresh_prov ()
  MMP.malloc_bytes_with_pr init_bytes align pr

def memcpy (src dst : Pa.PTR.ptr) (size : Nat) (_volatile : Bool) :
    memM (MMS := MMP.mm_state) Unit := do
  if Interfaces.Pointer.no_overlap dst size src size ||
      Pa.P2I.ptr_to_int src == Pa.P2I.ptr_to_int dst then
    let bytes ← read_bytes src size
    write_bytes dst bytes
  else
    mub "memcpy with overlapping or non-equal src and dst memory locations.".toUTF8

def memmove (src dst : Pa.PTR.ptr) (size : Nat) (_volatile : Bool) :
    memM (MMS := MMP.mm_state) Unit := do
  let bytes ← read_bytes src size
  write_bytes dst bytes

def memset (dst : Pa.PTR.ptr) (byte : memory_byte) (len : Nat) (_volatile : Bool) :
    memM (MMS := MMP.mm_state) Unit :=
  write_bytes dst (List.replicate len byte)

def handle_memtransfer (overlap_ok : Bool) (args : List dvalue_base) :
    memM (MMS := MMP.mm_state) Unit := do
  let name := if overlap_ok then "memmove" else "memcpy"
  let unsupported := if overlap_ok then "Unsupported arguments to memmove.".toUTF8
    else "Unsupported arguments to memcpy.".toUTF8
  match args with
  | [dst, src, len, .DVALUE_I _ volatile] =>
    let size : Nat ← match len with
      | .DVALUE_I _ n => pure (unsigned n).toNat
      | .DVALUE_Iptr n => pure (Pa.IPTR.to_Z n).toNat
      | .DVALUE_Poison => mub (name ++ " with poison length.").toUTF8
      | _ => merr unsupported
    match dst, src with
    | .DVALUE_Pointer dst, .DVALUE_Pointer src =>
      (if overlap_ok then memmove else memcpy) src dst size
        (VellvmIntegers.equ volatile VellvmIntegers.one)
    | .DVALUE_Poison, .DVALUE_Pointer _ | .DVALUE_Poison, .DVALUE_Poison
    | .DVALUE_Pointer _, .DVALUE_Poison =>
      if size == 0 then pure ()
      else mub (name ++ " with a poison source or destination and nonzero length.").toUTF8
    | _, _ => merr unsupported
  | _ => merr unsupported

def handle_memcpy (args : List dvalue_base) : memM (MMS := MMP.mm_state) Unit :=
  handle_memtransfer false args

def handle_memmove (args : List dvalue_base) : memM (MMS := MMP.mm_state) Unit :=
  handle_memtransfer true args

def handle_memset (args : List dvalue_base) : memM (MMS := MMP.mm_state) Unit := do
  let unsupported := "Unsupported arguments to memset.".toUTF8
  match args with
  | [dst, val, len, .DVALUE_I _ volatile] =>
    let byte : memory_byte ← match val with
      | .DVALUE_I sz v =>
        if sz.val == 8 then pure (BYTE_I (Numeric.Integers.repr (unsigned v))) else merr unsupported
      | .DVALUE_Poison => pure poison_memory_byte
      | _ => merr unsupported
    let size : Nat ← match len with
      | .DVALUE_I _ n => pure (unsigned n).toNat
      | .DVALUE_Poison => mub "memset with poison length.".toUTF8
      | _ => merr unsupported
    match dst with
    | .DVALUE_Pointer p => memset p byte size (VellvmIntegers.equ volatile VellvmIntegers.one)
    | .DVALUE_Poison =>
      if size == 0 then pure () else mub "memset with a poison destination and nonzero length.".toUTF8
    | _ => merr unsupported
  | _ => merr unsupported

def handle_malloc (args : List dvalue_base) (align : Nat) : memM (MMS := MMP.mm_state) Pa.PTR.ptr :=
  match args with
  | [.DVALUE_I _ sz] => malloc_bytes (generate_num_poison_bytes (unsigned sz).toNat) align
  | [.DVALUE_Iptr sz] => malloc_bytes (generate_num_poison_bytes (Pa.IPTR.to_unsigned sz).toNat) align
  | _ => merr "Malloc: invalid arguments.".toUTF8

def handle_free (args : List dvalue_base) : memM (MMS := MMP.mm_state) Unit :=
  match args with
  | [.DVALUE_Pointer p] =>
    if Pa.P2I.ptr_to_int p == Pa.P2I.ptr_to_int Pa.PTR.null then pure () else MMP.free p
  | [.DVALUE_Poison] => mub "Free of a poison pointer.".toUTF8
  | _ => merr "Free: invalid arguments.".toUTF8

def NONE : dvalue := DVALUE_Base DVALUE_None

def handle_intrinsicM (e : LLVMEvents.IntrinsicRequest) :
    memM (MMS := MMP.mm_state) (LLVMEvents.IntrinsicE.O e) :=
  match e with
  | .Intrinsic _ name args _ => do
    let args' ← lift (args.mapM fun a ↦ dvalue_to_dvalue_base a.2)
    match IntrinsicsDefinitions.lookup_intrinsic name with
    | some .Intr_memcpy => handle_memcpy args' *> pure (.inr NONE)
    | some .Intr_memmove => handle_memmove args' *> pure (.inr NONE)
    | some .Intr_memset => handle_memset args' *> pure (.inr NONE)
    | some .Intr_malloc =>
      let p ← handle_malloc args' 8
      pure (.inr (DVALUE_Base (DVALUE_Pointer p)))
    | some .Intr_free => handle_free args' *> pure (.inr NONE)
    | _ => merr ("Unknown intrinsic: ".toUTF8 ++ name)

end Vellvm.Semantics.Implementations.Memory
