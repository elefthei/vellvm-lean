import Vellvm.Semantics.MemoryBytes.Scalar
import Vellvm.Semantics.DynamicValues.Canonical
import Vellvm.Semantics.DynamicValues.Show

namespace Vellvm.Semantics.MemoryBytes
open Interfaces.Params Interfaces.Sizeof DynamicValues EOU Numeric Syntax.DynamicTypes Syntax.LLVMAst
open Utils.ListUtil

variable [Pa : Params]

private abbrev Bytes := List memory_byte
private abbrev Written := EOU (Nat × Bytes)

def packed_elt_bits (m : Positive) (dv : dvalue) : EOU (List memory_bit) :=
  match dv with
  | .DVALUE_Base (.DVALUE_I _ x) =>
    pure (memory_bits_from (fun i ↦ Bit_bit (Integers.repr (extract_bit_vint x i))) m.val 0)
  | .DVALUE_Base (.DVALUE_B _ bv) => pure (dvalue_bv_to_memory_bits bv)
  | .DVALUE_Base .DVALUE_Poison => pure (List.replicate m.val Bit_psn)
  | _ => raise_error ("packed vector: element is not an integer or byte value: ".toUTF8 ++ show_dvalue dv)

/-- A field is laid out from its own origin, even inside a packed parent. -/
def writeStructOn (ta pad : Option Nat) : (ts : List dtyp) →
    (∀ t ∈ ts, dvalue → Bytes → Written) → List dvalue → Nat → Bytes → Written
  | [], _, [], off, acc =>
    let (off', bs) := accumulate_padding off pad acc
    pure (accumulate_padding off' ta bs)
  | t :: ts, ser, f :: fs, off, acc => do
    let (start, pre) := accumulate_padding off (pad.map fun _ ↦ (dtyp_alignment t).preferred_alignment) acc
    let (extent, bs) ← ser t List.mem_cons_self f pre
    let (next, bs') := accumulate_padding_bytes (start + extent) (alloc_size_dtyp t - store_size_dtyp t) bs
    writeStructOn ta pad ts (fun u h ↦ ser u (List.mem_cons_of_mem _ h)) fs next bs'
  | _, _, _, _, _ => raise_error "type-mismatch: structs / fields have different lengths".toUTF8

def writeStruct (ser : dtyp → dvalue → Nat → Option Nat → Bytes → Written) (ta pad : Option Nat)
    (fs : List dvalue) (ts : List dtyp) (off : Nat) (acc : Bytes) : Written :=
  writeStructOn ta pad ts (fun t _ v ↦ ser t v 0 none) fs off acc

def writeArrayOn (ser : dvalue → Bytes → Written) (ta : Option Nat) (ep : Nat) :
    List dvalue → Nat → Bytes → Written
  | [], off, acc => pure (accumulate_padding off ta acc)
  | x :: xs, off, acc => do
    let (extent, bs) ← ser x acc
    let (next, bs') := accumulate_padding_bytes (off + extent) ep bs
    writeArrayOn ser ta ep xs next bs'

def writeArray (ser : dtyp → dvalue → Nat → Option Nat → Bytes → Written) (ta : Option Nat)
    (dt : dtyp) (ep : Nat) := writeArrayOn (fun v ↦ ser dt v 0 none) ta ep

def writePacked (m : Positive) (dt : dtyp) (elts : List dvalue) (off : Nat) (ta : Option Nat)
    (acc : Bytes) : Written := do
  let bitss ← map_monad (packed_elt_bits m) elts
  let n := store_size_dtyp dt
  pure (accumulate_padding (off+n) ta (acc_packed_bits_to_memory_bytes n bitss.flatten acc))

def acc_dvalue_to_memory_bytes_h (dt : dtyp) (dv : dvalue) (offset : Nat) (ta : Option Nat)
    (acc : List memory_byte) : EOU (Nat × List memory_byte) :=
  match dt with
  | .DTYPE_Base t =>
    match dv with
    | .DVALUE_Base v =>
      let (next, bs) := acc_memory_bytes_of_dvalue_base t v offset acc
      pure (accumulate_padding next ta bs)
    | _ => raise_error "acc_dvalue_to_memory_bytes_h: type-mismatch non-base value".toUTF8
  | .DTYPE_Struct p ts =>
    match dv with
    | .DVALUE_Struct _ fs =>
      let pad := if p then none else some (max_preferred_dtyp_alignment ts)
      writeStructOn ta pad ts (fun t _ x ↦ acc_dvalue_to_memory_bytes_h t x 0 none) fs offset acc
    | .DVALUE_Base .DVALUE_Poison =>
      let (next, bs) := accumulate_padding_bytes offset (store_size_dtyp (DTYPE_Struct p ts)) acc
      pure (accumulate_padding next ta bs)
    | _ => raise_error "acc_dvalue_to_memory_bytes_h: type-mismatch non-struct value".toUTF8
  | .DTYPE_Array vec n elt =>
    match dv with
    | .DVALUE_Array _ xs =>
      match packed_vector_type (DTYPE_Array vec n elt) with
      | some (_, m) => writePacked m (DTYPE_Array vec n elt) xs offset ta acc
      | none =>
        let ep := if vec then 0 else alloc_size_dtyp elt - store_size_dtyp elt
        writeArrayOn (fun x ↦ acc_dvalue_to_memory_bytes_h elt x 0 none) ta ep xs offset acc
    | .DVALUE_Base .DVALUE_Poison =>
      let (next, bs) := accumulate_padding_bytes offset (store_size_dtyp (DTYPE_Array vec n elt)) acc
      pure (accumulate_padding next ta bs)
    | _ => raise_error ("acc_dvalue_to_memory_bytes_h: type-mismatch non-array value: ".toUTF8 ++ show_dvalue dv)
termination_by sizeOf dt
decreasing_by all_goals decreasing_tactic

def dvalue_to_memory_bytes (dt : dtyp) (dv : dvalue) (tail_align : Option Nat) : EOU (List memory_byte) := do
  let (_, bs) ← acc_dvalue_to_memory_bytes_h dt dv 0 tail_align []
  pure bs.reverse

def packed_bits_to_dvalue (t : dtyp_base) (m : Positive) (bits : List memory_bit) : dvalue :=
  match t with
  | .DTYPE_B _ =>
    if bits.all is_poison_bit then DVALUE_Base DVALUE_Poison
    else if bits.all is_int_bit then DVALUE_Base (DVALUE_B m (BYTE_I (Integers.repr (int_bits_to_Z bits))))
    else DVALUE_Base (DVALUE_B m (BYTE_Mixed bits))
  | _ =>
    match memory_bits_to_Z bits with
    | .raise_ret (some z) => DVALUE_Base (DVALUE_I m (Integers.repr z))
    | _ => DVALUE_Base DVALUE_Poison

def packed_bits_to_elts (t : dtyp_base) (m : Positive) : Nat → List memory_bit → List dvalue
  | 0, _ => []
  | n+1, bits => packed_bits_to_dvalue t m (bits.take m.val) :: packed_bits_to_elts t m n (bits.drop m.val)

def readStructOn (np : Nat) (pad : Option Nat) : (ts : List dtyp) →
    (∀ t ∈ ts, Bytes → EOU dvalue) → Nat → Bytes → EOU (List dvalue)
  | [], _, _, _ => pure []
  | t :: ts, rd, off, dbs => do
    let n := if pad.isSome then pad_amount (dtyp_alignment t).preferred_alignment off else 0
    let start := off + n
    let bytes := dbs.drop n
    let ssz := store_size_dtyp t
    let asz := alloc_size_dtyp t
    let x ← if start + ssz ≤ np then pure (poison_of_dtyp t) else rd t List.mem_cons_self (bytes.take ssz)
    let xs ← readStructOn np pad ts (fun u h ↦ rd u (List.mem_cons_of_mem _ h)) (start+asz) (bytes.drop asz)
    pure (x :: xs)

def readStruct (rd : Bytes → dtyp → EOU dvalue) (np : Nat) (pad : Option Nat) (off : Nat)
    (ts : List dtyp) (dbs : Bytes) : EOU (List dvalue) :=
  readStructOn np pad ts (fun t _ bs ↦ rd bs t) off dbs

def readArrayOn (rd : Bytes → EOU dvalue) (np stride : Nat) (t : dtyp) (ssz : Nat) :
    Nat → Nat → Bytes → EOU (List dvalue)
  | 0, _, _ => pure []
  | n+1, offset, dbs => do
    let x ← if offset + ssz ≤ np then pure (poison_of_dtyp t) else rd (dbs.take ssz)
    let xs ← readArrayOn rd np stride t ssz n (offset+stride) (dbs.drop stride)
    pure (x :: xs)

def readArray (rd : Bytes → dtyp → EOU dvalue) (np stride : Nat) (t : dtyp) :=
  readArrayOn (fun bs ↦ rd bs t) np stride t (store_size_dtyp t)

def memory_bytes_to_dvalue (dbs : List memory_byte) (dt : dtyp) : EOU dvalue :=
  match dt with
  | .DTYPE_Base t => DVALUE_Base <$> memory_bytes_to_dvalue_base (dbs.take (store_size_dtyp (DTYPE_Base t))) t
  | .DTYPE_Struct p ts =>
    let (np, rest) := poison_split dbs
    match rest with
    | [] => pure (poison_of_dtyp (DTYPE_Struct p ts))
    | _ :: _ =>
      let pad := if p then none else some (max_preferred_dtyp_alignment ts)
      canonicalize_agg (DTYPE_Struct p ts) <$>
        readStructOn np pad ts (fun t _ bs ↦ memory_bytes_to_dvalue bs t) 0 dbs
  | .DTYPE_Array v n t =>
    let (np, rest) := poison_split dbs
    match rest with
    | [] => pure (poison_of_dtyp (DTYPE_Array v n t))
    | _ :: _ =>
      match packed_vector_type (DTYPE_Array v n t) with
      | some (tb, m) =>
        let bits := (get_bits_of_memory_byte_list (n*m.val) dbs []).reverse
        pure (canonicalize_agg (DTYPE_Array v n t) (packed_bits_to_elts tb m n bits))
      | none => do
        let ssz := store_size_dtyp t
        let stride := if v then ssz else alloc_size_dtyp t
        let xs ← readArrayOn (fun bs ↦ memory_bytes_to_dvalue bs t) np stride t ssz n 0 dbs
        pure (canonicalize_agg (DTYPE_Array v n t) xs)
termination_by sizeOf dt
decreasing_by all_goals decreasing_tactic

end Vellvm.Semantics.MemoryBytes
