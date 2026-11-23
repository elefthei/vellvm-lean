import Vellvm.Semantics.MemoryBytes.Basic
import Vellvm.Semantics.MemoryBytes.Digits
import Vellvm.Semantics.DynamicValues.Core
import Vellvm.Numeric.Floats.Raw

namespace Vellvm.Semantics.MemoryBytes
open Interfaces.Params Interfaces.Sizeof DynamicValues EOU Numeric Syntax.DynamicTypes Syntax.LLVMAst
open Utils.ListUtil

variable [Pa : Params]

def memory_byte_of_dvalue_bv {bit_sz : Positive} (bv : dvalue_bv bit_sz) (idx : Nat) : memory_byte :=
  match bv with
  | .BYTE_Pointer p k => BYTE_Pointer p (bit_sz.val * k / 8 + idx)
  | .BYTE_I x => BYTE_I (Integers.repr (extract_byte_vint x idx))
  | .BYTE_Mixed bits =>
    let m := (bits.drop (8 * idx)).take 8
    let pad := if !(m.length == 8) then List.replicate (8 - m.length) Bit_psn else []
    BYTE_Mixed (m ++ pad)

def baseByteGen : dvalue_base → Nat → memory_byte
  | .DVALUE_I _ x => memory_byte_of_dvalue_bv (BYTE_I x)
  | .DVALUE_Iptr x => fun i ↦ BYTE_I (Integers.repr (extract_byte_Z (Pa.IPTR.to_Z x) i))
  | .DVALUE_Pointer p => BYTE_Pointer p
  | .DVALUE_Float f => fun i ↦ BYTE_I (Integers.repr (extract_byte_Z (Integers.unsigned (Floats.Float32.to_bits f)) i))
  | .DVALUE_Double f => fun i ↦ BYTE_I (Integers.repr (extract_byte_Z (Integers.unsigned (Floats.Float.to_bits f)) i))
  | .DVALUE_Poison | .DVALUE_None => fun _ ↦ poison_memory_byte
  | .DVALUE_B _ bv => memory_byte_of_dvalue_bv bv

def acc_memory_bytes_of_dvalue_base (dt : dtyp_base) (dv : dvalue_base) (offset : Nat)
    (acc : List memory_byte) : Nat × List memory_byte :=
  let n := store_size_dtyp (.DTYPE_Base dt)
  (n + offset, N.rev_loop_acc (baseByteGen dv) n 0 acc)

def packed_vector_type : dtyp → Option (dtyp_base × Positive)
  | .DTYPE_Array true _ (.DTYPE_Base (.DTYPE_I m)) =>
    if m.val % 8 = 0 then none else some (DTYPE_I m, m)
  | .DTYPE_Array true _ (.DTYPE_Base (.DTYPE_B m)) =>
    if m.val % 8 = 0 then none else some (DTYPE_B m, m)
  | _ => none

def memory_bits_from (f : Nat → memory_bit) (n start : Nat) : List memory_bit :=
  (N.rev_loop_acc f n start []).reverse

def dvalue_bv_to_memory_bits {sz : Positive} : dvalue_bv sz → List memory_bit
  | .BYTE_I x => memory_bits_from (fun i ↦ Bit_bit (Integers.repr (extract_bit_vint x i))) sz.val 0
  | .BYTE_Pointer p idx => memory_bits_from (Bit_ptr p) sz.val (sz.val * idx)
  | .BYTE_Mixed bits => bits

def memory_byte_of_bits (bits : List memory_bit) : memory_byte :=
  if bits.all is_int_bit then BYTE_I (Integers.repr (int_bits_to_Z bits)) else BYTE_Mixed bits

def acc_bits_to_memory_bytes : Nat → List memory_bit → List memory_byte → List memory_byte
  | 0, _, acc => acc
  | n+1, bits, acc => acc_bits_to_memory_bytes n (bits.drop 8) (memory_byte_of_bits (bits.take 8) :: acc)

def acc_packed_bits_to_memory_bytes (nbytes : Nat) (bits : List memory_bit) (acc : List memory_byte) :=
  let pad := List.replicate (8 * nbytes - bits.length) (Bit_bit (Integers.repr 0))
  acc_bits_to_memory_bytes nbytes (bits ++ pad) acc

def memory_bit_to_bit : memory_bit → EOUP Int
  | .Bit_ptr p i => raise_ret (some (extract_bit_Z (Pa.P2I.ptr_to_int p) i))
  | .Bit_psn => raise_ret none
  | .Bit_bit b => raise_ret (some (Integers.unsigned b))

def memory_bits_to_Z (bits : List memory_bit) : EOUP Int := do
  let zs ← map_monad (m := EOUP) memory_bit_to_bit bits
  pure (concat_bits_Z zs)

def memory_byte_to_Z : memory_byte → EOUP Int
  | .BYTE_Pointer p i => raise_ret (some (extract_byte_Z (Pa.P2I.ptr_to_int p) i))
  | .BYTE_I x => raise_ret (some (Integers.unsigned x))
  | .BYTE_Mixed bits => memory_bits_to_Z bits

def absorb_pois {A : Type u} (c : EOUP A) (k : A → EOU dvalue_base) : EOU dvalue_base :=
  catch_pois DVALUE_Poison c k

def valid_pointer_bits (p : Pa.PTR.ptr) (base offset : Nat) : List memory_bit → EOUP Bool
  | [] => pure (offset == 8)
  | .Bit_ptr q j :: rest =>
    match Pa.PTR.eq_dec_ptr p q with
    | .inl _ => if j == base + offset then valid_pointer_bits p base (1 + offset) rest else pure false
    | .inr _ => pure false
  | .Bit_bit _ :: _ => pure false
  | .Bit_psn :: _ => raise_ret none

def valid_pointer_byte (p : Pa.PTR.ptr) (idx : Nat) : memory_byte → EOUP Bool
  | .BYTE_Pointer q i =>
    match Pa.PTR.eq_dec_ptr p q with
    | .inl _ => pure (idx == i)
    | .inr _ => pure false
  | .BYTE_Mixed bits => valid_pointer_bits p (idx * 8) 0 bits
  | .BYTE_I _ => pure false

def valid_pointer_bytes (p : Pa.PTR.ptr) (idx : Nat) : List memory_byte → EOUP Bool
  | [] => pure (idx == store_size_dtyp DTYPE_Pointer)
  | b :: bs => do
    let v ← valid_pointer_byte p idx b
    if v then valid_pointer_bytes p (1+idx) bs else pure false

def memory_bytes_to_address_ptr (dbs : List memory_byte) : EOUP Pa.PTR.ptr := do
  let zs ← map_monad (m := EOUP) memory_byte_to_Z dbs
  EOU.bind (Pa.P2I.int_to_ptr (concat_bytes_Z zs) Pa.PROV.nil_prov) (fun p ↦ raise_ret (some p))

def memory_bytes_to_pointer (dbs : List memory_byte) : EOUP Pa.PTR.ptr :=
  match dbs with
  | .BYTE_Pointer p _ :: _ | .BYTE_Mixed (.Bit_ptr p _ :: _) :: _ => do
    let valid ← valid_pointer_bytes p 0 dbs
    if valid then pure p else memory_bytes_to_address_ptr dbs
  | _ => memory_bytes_to_address_ptr dbs

def memory_byte_to_memory_bits (mb : memory_byte) : List memory_bit := dvalue_bv_to_memory_bits mb

def concat_bytes_Z_mixed (extra : Nat) : List memory_byte → EOUP Int
  | [] => pure 0
  | [.BYTE_I y] => pure (Integers.unsigned y % 2^extra)
  | [b] => memory_bits_to_Z ((memory_byte_to_memory_bits b).take extra)
  | b :: c :: rest => do
    let z ← memory_byte_to_Z b
    let r ← concat_bytes_Z_mixed extra (c :: rest)
    pure (z + 256 * r)

def memory_bytes_to_int (bit_sz : Positive) (dbs : List memory_byte) : EOUP Int := do
  let extra := bit_sz.val % 8
  if extra != 0 then concat_bytes_Z_mixed extra dbs else
    let zs ← map_monad (m := EOUP) memory_byte_to_Z dbs
    pure (concat_bytes_Z zs)

def get_bits_of_memory_byte_list (n : Nat) : List memory_byte → List memory_bit → List memory_bit
  | [], acc => if n == 0 then acc else N.rev_loop_acc (fun _ ↦ Bit_psn) n 0 acc
  | b :: bs, acc =>
    let bits := memory_byte_to_memory_bits b
    if n < 8 then (bits.take n).reverseAux acc
    else get_bits_of_memory_byte_list (n - 8) bs (bits.reverseAux acc)

def pointer_byte_at (p : Pa.PTR.ptr) (idx : Nat) (mb : memory_byte) : Bool :=
  match valid_pointer_byte p idx mb with
  | .raise_ret (some b) => b
  | _ => false

def pointer_slice_from (p : Pa.PTR.ptr) (idx : Nat) : List memory_byte → Bool
  | [] => true
  | b :: bs => pointer_byte_at p idx b && pointer_slice_from p (1+idx) bs

def memory_bytes_to_pointer_slice (dbs : List memory_byte) : Option (Pa.PTR.ptr × Nat) :=
  match dbs with
  | .BYTE_Pointer p k :: _ => if pointer_slice_from p k dbs then some (p,k) else none
  | .BYTE_Mixed (.Bit_ptr p j :: _) :: _ =>
    let k := j / 8
    if pointer_slice_from p k dbs then some (p,k) else none
  | _ => none

def pointer_chunk_aligned (bit_sz : Positive) (k : Nat) : Bool :=
  bit_sz.val % 8 == 0 && (k * 8) % bit_sz.val == 0

def memory_bytes_to_bits_value (bit_sz : Positive) (dbs : List memory_byte) : dvalue_bv bit_sz :=
  let bits := (get_bits_of_memory_byte_list bit_sz.val dbs []).reverse
  if bits.any is_ptr_bit || bits.any is_poison_bit then BYTE_Mixed bits else
    match memory_bytes_to_int bit_sz dbs with
    | .raise_ret (some x) => BYTE_I (Integers.repr x)
    | _ => BYTE_I (Integers.repr (int_bits_to_Z bits))

def memory_bytes_to_byte_value (bit_sz : Positive) (dbs : List memory_byte) : EOU (dvalue_bv bit_sz) :=
  match memory_bytes_to_pointer_slice dbs with
  | some (p, k) =>
    if pointer_chunk_aligned bit_sz k then pure (BYTE_Pointer p (k*8 / bit_sz.val))
    else pure (memory_bytes_to_bits_value bit_sz dbs)
  | none => pure (memory_bytes_to_bits_value bit_sz dbs)

def all_poison_bits (bits : List memory_bit) := bits.all is_poison_bit

def is_all_poison_byte : memory_byte → Bool
  | .BYTE_Mixed bits => all_poison_bits bits
  | _ => false

def poison_split : List memory_byte → Nat × List memory_byte
  | [] => (0, [])
  | b :: rest =>
    if is_all_poison_byte b then
      let (k, tl) := poison_split rest
      (1+k, tl)
    else (0, b :: rest)

def all_poison_bytes (dbs : List memory_byte) := (poison_split dbs).2.isEmpty

def memory_bytes_to_dvalue_base (dbs : List memory_byte) : dtyp_base → EOU dvalue_base
  | .DTYPE_I sz => absorb_pois (memory_bytes_to_int sz dbs) (fun v ↦ pure (DVALUE_I sz (Integers.repr v)))
  | .DTYPE_Iptr => absorb_pois (map_monad (m := EOUP) memory_byte_to_Z dbs) fun zs ↦
    DVALUE_Iptr <$> Pa.IPTR.from_Z (concat_bytes_Z zs)
  | .DTYPE_Pointer => absorb_pois (memory_bytes_to_pointer dbs) (fun p ↦ pure (DVALUE_Pointer p))
  | .DTYPE_Void => raise_error "memory_bytes_to_dvalue on void type.".toUTF8
  | .DTYPE_FP .FP_half => raise_error "memory_bytes_to_dvalue: unsupported half.".toUTF8
  | .DTYPE_FP .FP_bfloat => raise_error "memory_bytes_to_dvalue: unsupported bfloat".toUTF8
  | .DTYPE_FP .FP_float => absorb_pois (map_monad (m := EOUP) memory_byte_to_Z dbs) fun zs ↦
    pure (DVALUE_Float (Floats.Float32.of_bits (concat_bytes_Z_vint zs)))
  | .DTYPE_FP .FP_double => absorb_pois (map_monad (m := EOUP) memory_byte_to_Z dbs) fun zs ↦
    pure (DVALUE_Double (Floats.Float.of_bits (concat_bytes_Z_vint zs)))
  | .DTYPE_FP .FP_x86_fp80 => raise_error "memory_bytes_to_dvalue: unsupported X86_fp80.".toUTF8
  | .DTYPE_FP .FP_fp128 => raise_error "memory_bytes_to_dvalue: unsupported fp128.".toUTF8
  | .DTYPE_FP .FP_ppc_fp128 => raise_error "memory_bytes_to_dvalue: unsupported ppc_fp128.".toUTF8
  | .DTYPE_Label => raise_error "memory_bytes_to_dvalue: unsupported DTYPE_Label.".toUTF8
  | .DTYPE_Token => raise_error "memory_bytes_to_dvalue: unsupported DTYPE_Token.".toUTF8
  | .DTYPE_Metadata => raise_error "memory_bytes_to_dvalue: unsupported DTYPE_Metadata.".toUTF8
  | .DTYPE_X86_mmx => raise_error "memory_bytes_to_dvalue: unsupported DTYPE_X86_mmx.".toUTF8
  | .DTYPE_Opaque => raise_error "memory_bytes_to_dvalue: unsupported DTYPE_Opaque.".toUTF8
  | .DTYPE_B sz => do
    if all_poison_bytes dbs then pure DVALUE_Poison else
      let dv ← memory_bytes_to_byte_value sz dbs
      if dvalue_bv_all_poison dv then pure DVALUE_Poison else pure (DVALUE_B sz dv)

end Vellvm.Semantics.MemoryBytes
