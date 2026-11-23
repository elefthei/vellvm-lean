import PortChecks.SourceType
import Vellvm.Theory.MemoryBytesFacts.Layout

open Vellvm Vellvm.Syntax.DynamicTypes Vellvm.Utils.ListUtil Vellvm.Utils.ZUtil
open Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.Interfaces.Sizeof
open Vellvm.Semantics.DynamicValues Vellvm.Semantics.MemoryBytes Vellvm.Semantics.EOU
open Vellvm.Semantics.VellvmIntegers
open Vellvm.Numeric.Integers (bit_int)
open Vellvm.Theory.MemoryBytesFacts

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|byte_layout"
  byte_layout : ∀ [Pa : Params], dtyp → Prop

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|byte_layout_not_packed"
  byte_layout_not_packed : ∀ [Pa : Params], ∀ (vv : Bool) (sz : Nat) (t : dtyp), byte_layout t →
    packed_vector_type (DTYPE_Array vv sz t) = none

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|same_bits"
  same_bits : ∀ [Pa : Params], memory_byte → memory_byte → Prop

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|forallb_psn_repeat"
  forallb_psn_repeat : ∀ [Pa : Params], ∀ (l : List memory_bit), l.all is_poison_bit = true →
    l = List.replicate l.length Bit_psn

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|same_bits_poison"
  same_bits_poison : ∀ [Pa : Params], ∀ (b : memory_byte), memory_byte_wf b → is_all_poison_byte b = true →
    same_bits b poison_memory_byte

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|same_bits_all_poison"
  same_bits_all_poison : ∀ [Pa : Params], ∀ {dbs : List memory_byte}, List.Forall memory_byte_wf dbs →
    dbs.all is_all_poison_byte = true →
    List.Forall₂ same_bits dbs (List.replicate dbs.length poison_memory_byte)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|write_base_block"
  write_base_block : ∀ [Pa : Params], ∀ {dtb : dtyp_base} {v : dvalue_base} {acc : List memory_byte} {o bs},
    acc_dvalue_to_memory_bytes_h (DTYPE_Base dtb) (DVALUE_Base v) 0 none acc = raise_ret (o, bs) →
    bs = ((Nseq 0 (store_size_dtyp (DTYPE_Base dtb))).map (base_byte_gen v)).reverse ++ acc

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|write_poison_layout"
  write_poison_layout : ∀ [Pa : Params], ∀ (dt : dtyp) (acc : List memory_byte) {o bs}, byte_layout dt →
    acc_dvalue_to_memory_bytes_h dt (DVALUE_Base DVALUE_Poison) 0 none acc = raise_ret (o, bs) →
    bs = List.replicate (store_size_dtyp dt) poison_memory_byte ++ acc

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|all_pointer_bits_from_map"
  all_pointer_bits_from_map : ∀ [Pa : Params], ∀ (p : Pa.PTR.ptr) (l : List memory_bit) (s : Nat),
    all_pointer_bits_from p s l = true → l = (Nseq s l.length).map (Bit_ptr p)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|same_bits_pointer_byte"
  same_bits_pointer_byte : ∀ [Pa : Params], ∀ (b : memory_byte) (p : Pa.PTR.ptr) (j : Nat),
    memory_byte_wf b → pointer_byte_at p j b = true → same_bits b (BYTE_Pointer p j)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|pointer_slice_from_same_bits"
  pointer_slice_from_same_bits : ∀ [Pa : Params], ∀ (p : Pa.PTR.ptr) {dbs : List memory_byte} (k : Nat),
    List.Forall memory_byte_wf dbs → pointer_slice_from p k dbs = true →
    List.Forall₂ same_bits dbs ((Nseq k dbs.length).map (BYTE_Pointer p))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|pointer_slice_some"
  pointer_slice_some : ∀ [Pa : Params], ∀ (dbs : List memory_byte) {p k}, memory_bytes_to_pointer_slice dbs = some (p,k) →
    pointer_slice_from p k dbs = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|take_drop_concat_bytes"
  take_drop_concat_bytes : ∀ [Pa : Params], ∀ {dbs : List memory_byte} {i : Nat}, List.Forall memory_byte_wf dbs →
    i < dbs.length → take 8 (drop (8*i) (dbs.map memory_byte_to_memory_bits).flatten) =
      memory_byte_to_memory_bits (dbs.getD i poison_memory_byte)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|mixed_bytes_same_bits"
  mixed_bytes_same_bits : ∀ [Pa : Params], ∀ {dbs : List memory_byte}, List.Forall memory_byte_wf dbs →
    List.Forall₂ same_bits dbs ((Nseq 0 dbs.length).map
      (mixed_byte (dbs.map memory_byte_to_memory_bits).flatten))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|no_ptr_psn_bits"
  no_ptr_psn_bits : ∀ [Pa : Params], ∀ (l : List memory_bit), l.any is_ptr_bit = false → l.any is_poison_bit = false →
    ∃ bis : List int1, l = bis.map Bit_bit

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|same_bits_int_byte"
  same_bits_int_byte : ∀ [Pa : Params], ∀ (b : memory_byte) {z : Int}, memory_byte_wf b →
    (memory_byte_to_memory_bits b).any is_ptr_bit = false →
    (memory_byte_to_memory_bits b).any is_poison_bit = false →
    memory_byte_to_Z b = raise_ret (NoPois z) → same_bits b (BYTE_I (repr z))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|byte_val"
  byte_val : ∀ [Pa : Params], memory_byte → Int

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_byte_to_Z_no_psn"
  memory_byte_to_Z_no_psn : ∀ [Pa : Params], ∀ (b : memory_byte), (memory_byte_to_memory_bits b).any is_poison_bit = false →
    memory_byte_to_Z b = raise_ret (NoPois (byte_val b))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|byte_val_range"
  byte_val_range : ∀ [Pa : Params], ∀ (b : memory_byte), memory_byte_wf b →
    (memory_byte_to_memory_bits b).any is_ptr_bit = false →
    (memory_byte_to_memory_bits b).any is_poison_bit = false →
    0 ≤ byte_val b ∧ byte_val b < 256

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|map_monad_byte_to_Z_no_psn"
  map_monad_byte_to_Z_no_psn : ∀ [Pa : Params], ∀ (dbs : List memory_byte),
    (∀ b ∈ dbs, (memory_byte_to_memory_bits b).any is_poison_bit = false) →
    map_monad (m := EOUP) memory_byte_to_Z dbs = raise_ret (NoPois (dbs.map byte_val))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|extract_byte_vint_concat"
  extract_byte_vint_concat : ∀ {sz : Positive} {zs : List Int} {i : Nat},
    8 * (zs.length : Int) = (sz.val : Int) → List.Forall (fun z ↦ 0 ≤ z ∧ z < 256) zs →
    i < zs.length → extract_byte_vint (repr (concat_bytes_Z zs) : bit_int sz) i = zs.getD i 0

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|int_bytes_same_bits"
  int_bytes_same_bits : ∀ [Pa : Params], ∀ {sz : Positive} {dbs : List memory_byte},
    List.Forall memory_byte_wf dbs → 8 * dbs.length = sz.val →
    (dbs.map memory_byte_to_memory_bits).flatten.any is_ptr_bit = false →
    (dbs.map memory_byte_to_memory_bits).flatten.any is_poison_bit = false →
    List.Forall₂ same_bits dbs ((Nseq 0 dbs.length).map
      (memory_byte_of_dvalue_bv (BYTE_I (repr (concat_bytes_Z (dbs.map byte_val)) : bit_int sz))))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|bits_value_same_bits"
  bits_value_same_bits : ∀ [Pa : Params], ∀ {sz : Positive} {dbs : List memory_byte},
    List.Forall memory_byte_wf dbs → 8 * dbs.length = sz.val →
    List.Forall₂ same_bits dbs ((Nseq 0 dbs.length).map
      (memory_byte_of_dvalue_bv (memory_bytes_to_bits_value sz dbs)))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|bits_value_all_poison"
  bits_value_all_poison : ∀ [Pa : Params], ∀ {sz : Positive} {dbs : List memory_byte},
    List.Forall memory_byte_wf dbs → 8 * dbs.length = sz.val →
    dvalue_bv_all_poison (memory_bytes_to_bits_value sz dbs) = true →
    dbs.all is_all_poison_byte = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|packed_extent_store"
  packed_extent_store : ∀ [Pa : Params], ∀ (dts : List dtyp), FORALL (fun t ↦ byte_layout t ∧ alloc_size_dtyp t = store_size_dtyp t) dts →
    struct_fields_extent true dts = dts.foldr (fun t a ↦ store_size_dtyp t + a) 0

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|byte_layout_serializable"
  byte_layout_serializable : ∀ [Pa : Params], ∀ (dt : dtyp), byte_layout dt → serializable dt

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|byte_layout_empty_store_size"
  byte_layout_empty_store_size : ∀ [Pa : Params], ∀ (dt : dtyp), byte_layout dt → dtyp_is_empty dt = true → store_size_dtyp dt = 0

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|rt_bytes"
  rt_bytes : ∀ [Pa : Params], dtyp → List memory_byte → dvalue → Prop

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|rt_bytes_poison"
  rt_bytes_poison : ∀ [Pa : Params], ∀ (dt : dtyp) {mb : List memory_byte}, byte_layout dt → List.Forall memory_byte_wf mb →
    mb.length = store_size_dtyp dt → mb.all is_all_poison_byte = true →
    rt_bytes dt mb (poison_of_dtyp dt)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|rt_bytes_B"
  rt_bytes_B : ∀ [Pa : Params], ∀ (sz : Positive) {mb : List memory_byte} {dv : dvalue}, sz.val % 8 = 0 →
    List.Forall memory_byte_wf mb → mb.length = store_size_dtyp (DTYPE_Base (DTYPE_B sz)) →
    memory_bytes_to_dvalue mb (DTYPE_Base (DTYPE_B sz)) = raise_ret dv →
    rt_bytes (DTYPE_Base (DTYPE_B sz)) mb dv

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_array_loop_bytes"
  read_array_loop_bytes : ∀ [Pa : Params], ∀ {t : dtyp} (np n offset : Nat) {dbs : List memory_byte} {elts : List dvalue},
    byte_layout t →
    (∀ (chunk : List memory_byte) (v : dvalue), List.Forall memory_byte_wf chunk →
      chunk.length = store_size_dtyp t → memory_bytes_to_dvalue chunk t = raise_ret v → rt_bytes t chunk v) →
    List.Forall memory_byte_wf dbs → dbs.length = n * store_size_dtyp t →
    (take (np-offset) dbs).all is_all_poison_byte = true →
    read_array_loop memory_bytes_to_dvalue np (store_size_dtyp t) t n offset dbs = raise_ret elts →
    (dtyp_is_empty t = false → elts.all dvalue_is_poison = true → dbs.all is_all_poison_byte = true) ∧
    (∀ off acc o bs, array_bytes_loop acc_dvalue_to_memory_bytes_h none t 0 elts off acc = raise_ret (o,bs) →
      ∃ w, bs = w ++ acc ∧ List.Forall₂ same_bits dbs w.reverse)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_struct_loop_bytes"
  read_struct_loop_bytes : ∀ [Pa : Params], ∀ (np : Nat) (dts : List dtyp) (offset : Nat) {dbs : List memory_byte} {vs : List dvalue},
    FORALL (fun t ↦ byte_layout t ∧ alloc_size_dtyp t = store_size_dtyp t) dts →
    (∀ t ∈ dts, ∀ (chunk : List memory_byte) (v : dvalue), List.Forall memory_byte_wf chunk →
      chunk.length = store_size_dtyp t → memory_bytes_to_dvalue chunk t = raise_ret v → rt_bytes t chunk v) →
    List.Forall memory_byte_wf dbs → dbs.length = dts.foldr (fun t a ↦ store_size_dtyp t + a) 0 →
    (take (np-offset) dbs).all is_all_poison_byte = true →
    read_struct_loop memory_bytes_to_dvalue np none offset dts dbs = raise_ret vs →
    (fields_all_poison dts vs = true → dbs.all is_all_poison_byte = true) ∧
    (∀ off acc o bs, struct_bytes_loop acc_dvalue_to_memory_bytes_h none none vs dts off acc = raise_ret (o,bs) →
      ∃ w, bs = w ++ acc ∧ List.Forall₂ same_bits dbs w.reverse)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|bytes_round_trip_h"
  bytes_round_trip_h : ∀ [Pa : Params], ∀ (dt : dtyp), byte_layout dt → ∀ {mb : List memory_byte} {dv : dvalue},
    List.Forall memory_byte_wf mb → mb.length = store_size_dtyp dt →
    memory_bytes_to_dvalue mb dt = raise_ret dv → rt_bytes dt mb dv

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bytes_round_trip_bytes"
  memory_bytes_round_trip_bytes : ∀ [Pa : Params], ∀ (dt : dtyp) {mb : List memory_byte} {dv : dvalue} {mb' : List memory_byte},
    byte_layout dt → List.Forall memory_byte_wf mb → mb.length = store_size_dtyp dt →
    memory_bytes_to_dvalue mb dt = raise_ret dv → dvalue_to_memory_bytes dt dv none = raise_ret mb' →
    List.Forall₂ same_bits mb mb'
