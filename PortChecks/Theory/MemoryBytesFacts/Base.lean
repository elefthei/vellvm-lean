import PortChecks.SourceType
import Vellvm.Theory.MemoryBytesFacts.Base

open Vellvm Vellvm.Numeric Vellvm.Semantics Vellvm.Semantics.EOU
open Vellvm.Semantics.DynamicValues Vellvm.Semantics.MemoryBytes
open Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.Interfaces.Sizeof
open Vellvm.Syntax.DynamicTypes Vellvm.Syntax.LLVMAst Vellvm.Utils.ListUtil
open Vellvm.Theory.MemoryBytesFacts

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|serializable_base"
  serializable_base : dtyp_base → Prop

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|serializable"
  serializable : dtyp → Prop

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|serializable_NO_VOID"
  serializable_NO_VOID : ∀ dt, serializable dt → NO_VOID dt

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|base_byte_gen"
  base_byte_gen : ∀ [Pa : Params], dvalue_base → Nat → memory_byte

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|acc_base_unfold"
  acc_base_unfold : ∀ [Pa : Params] dt v off acc, acc_memory_bytes_of_dvalue_base dt v off acc =
    (store_size_dtyp (DTYPE_Base dt) + off,
     N.rev_loop_acc (base_byte_gen v) (store_size_dtyp (DTYPE_Base dt)) 0 acc)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|base_block_length"
  base_block_length : ∀ [Pa : Params] dt v,
    ((Nseq 0 (store_size_dtyp (DTYPE_Base dt))).map (base_byte_gen v)).length = store_size_dtyp (DTYPE_Base dt)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|accumulate_poison_bytes_app"
  accumulate_poison_bytes_app : ∀ [Pa : Params] n acc,
    accumulate_poison_bytes n acc = List.replicate n poison_memory_byte ++ acc

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|is_all_poison_memory_byte"
  is_all_poison_memory_byte : ∀ [Pa : Params], is_all_poison_byte poison_memory_byte = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|poison_split_repeat"
  poison_split_repeat : ∀ [Pa : Params] k, poison_split (List.replicate k poison_memory_byte) = (k, [])

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|poison_of_dtyp_base"
  poison_of_dtyp_base : ∀ [Pa : Params] t, poison_of_dtyp (DTYPE_Base t) = DVALUE_Base DVALUE_Poison

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|poison_of_dtyp_nonempty"
  poison_of_dtyp_nonempty : ∀ [Pa : Params] t, dtyp_is_empty t = false → poison_of_dtyp t = DVALUE_Base DVALUE_Poison

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|poison_of_dtyp_empty"
  poison_of_dtyp_empty : ∀ [Pa : Params] t, dtyp_is_empty t = true → poison_of_dtyp t = empty_dvalue_of_dtyp t

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|has_dtyp_empty"
  has_dtyp_empty : ∀ [Pa : Params] {t v}, dvalue_has_dtyp v t → dtyp_is_empty t = true → v = empty_dvalue_of_dtyp t

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|struct_canonical_cases"
  struct_canonical_cases : ∀ [Pa : Params] {p fs ts}, dvalue_has_dtyp (DVALUE_Struct p fs) (DTYPE_Struct p ts) →
    DVALUE_Struct p fs = poison_of_dtyp (DTYPE_Struct p ts) ∨ fields_all_poison ts fs = false

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|array_canonical_cases"
  array_canonical_cases : ∀ [Pa : Params] {p xs n t}, dvalue_has_dtyp (DVALUE_Array p xs) (DTYPE_Array p n t) →
    DVALUE_Array p xs = poison_of_dtyp (DTYPE_Array p n t) ∨
      (dtyp_is_empty t = false ∧ xs.all dvalue_is_poison = false)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|agg_is_poison_nonempty"
  agg_is_poison_nonempty : ∀ [Pa : Params] dt vs, agg_is_poison dt vs = true → dtyp_is_empty dt = false

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|empty_dvalue_has_dtyp"
  empty_dvalue_has_dtyp : ∀ [Pa : Params] t, NO_VOID t → dtyp_is_empty t = true → dvalue_has_dtyp (empty_dvalue_of_dtyp t) t

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|poison_of_dtyp_has_dtyp"
  poison_of_dtyp_has_dtyp : ∀ [Pa : Params] t, NO_VOID t → dvalue_has_dtyp (poison_of_dtyp t) t

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|dvalue_poison_of_dtyp_dec"
  dvalue_poison_of_dtyp_dec : ∀ [Pa : Params] v t, Decidable (v = poison_of_dtyp t)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_repeat_poison_agg"
  read_repeat_poison_agg : ∀ [Pa : Params] (dt : dtyp) (n : Nat),
    (match dt with | .DTYPE_Base _ => False | _ => True) →
    memory_bytes_to_dvalue (List.replicate n poison_memory_byte) dt = raise_ret (poison_of_dtyp dt)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|serializable_base_pos"
  serializable_base_pos : ∀ [Pa : Params] t, serializable_base t → 0 < store_size_dtyp (DTYPE_Base t)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_byte_to_Z_poison"
  memory_byte_to_Z_poison : ∀ [Pa : Params], memory_byte_to_Z poison_memory_byte = raise_ret Pois

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bits_to_Z_poison_cons"
  memory_bits_to_Z_poison_cons : ∀ [Pa : Params] rest, memory_bits_to_Z (Bit_psn :: rest) = raise_ret Pois

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|map_monad_byte_to_Z_poison"
  map_monad_byte_to_Z_poison : ∀ [Pa : Params] {k}, 0 < k →
    map_monad (m := EOUP) memory_byte_to_Z (List.replicate k poison_memory_byte) = raise_ret Pois

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|concat_bytes_Z_mixed_poison"
  concat_bytes_Z_mixed_poison : ∀ [Pa : Params] {e k}, 0 < e → 0 < k →
    concat_bytes_Z_mixed e (List.replicate k poison_memory_byte) = raise_ret Pois

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bytes_to_int_poison"
  memory_bytes_to_int_poison : ∀ [Pa : Params] sz {k}, 0 < k → memory_bytes_to_int sz (List.replicate k poison_memory_byte) = raise_ret Pois

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bytes_to_pointer_poison"
  memory_bytes_to_pointer_poison : ∀ [Pa : Params] {k}, 0 < k → memory_bytes_to_pointer (List.replicate k poison_memory_byte) = raise_ret Pois

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|all_poison_bytes_repeat"
  all_poison_bytes_repeat : ∀ [Pa : Params] k, all_poison_bytes (List.replicate k poison_memory_byte) = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_base_block_poison"
  read_base_block_poison : ∀ [Pa : Params] t, serializable_base t → memory_bytes_to_dvalue_base
    (List.replicate (store_size_dtyp (DTYPE_Base t)) poison_memory_byte) t = raise_ret DVALUE_Poison

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|valid_pointer_bytes_run"
  valid_pointer_bytes_run : ∀ [Pa : Params] (p : Pa.PTR.ptr) n i,
    valid_pointer_bytes p i ((Nseq i n).map (fun j ↦ (BYTE_Pointer p j : memory_byte))) =
      (pure (i + n == store_size_dtyp DTYPE_Pointer) : EOUP Bool)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bytes_to_pointer_run"
  memory_bytes_to_pointer_run : ∀ [Pa : Params] (p : Pa.PTR.ptr) {n}, 0 < n → n = store_size_dtyp DTYPE_Pointer →
    memory_bytes_to_pointer ((Nseq 0 n).map (fun i ↦ (BYTE_Pointer p i : memory_byte))) = raise_ret (NoPois p)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_base_block_pointer"
  read_base_block_pointer : ∀ [Pa : Params] p, memory_bytes_to_dvalue_base
    ((Nseq 0 (store_size_dtyp DTYPE_Pointer)).map (base_byte_gen (DVALUE_Pointer p))) DTYPE_Pointer = raise_ret (DVALUE_Pointer p)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|map_monad_byte_to_Z_BYTE_I"
  map_monad_byte_to_Z_BYTE_I : ∀ [Pa : Params] (f : Nat → VellvmIntegers.int8) (l : List Nat),
    map_monad (m := EOUP) memory_byte_to_Z (l.map (fun i ↦ BYTE_I (f i))) =
      raise_ret (NoPois (l.map (fun i ↦ Integers.unsigned (f i))))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_int_block_mult8"
  read_int_block_mult8 : ∀ [Pa : Params] {sz} (x : Integers.bit_int sz), sz.val % 8 = 0 → memory_bytes_to_dvalue_base
    ((Nseq 0 (store_size_dtyp (DTYPE_I sz))).map (memory_byte_of_dvalue_bv (BYTE_I x))) (DTYPE_I sz) = raise_ret (DVALUE_I sz x)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bits_to_Z_of_bits"
  memory_bits_to_Z_of_bits : ∀ [Pa : Params] (zs : List Int), memory_bits_to_Z (zs.map Z_to_memory_bit) =
    raise_ret (NoPois (concat_bits_Z (zs.map (fun z ↦ z % 2))))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|concat_bytes_Z_mixed_cons_app"
  concat_bytes_Z_mixed_cons_app : ∀ [Pa : Params] e b (ys : List VellvmIntegers.int8) lastb,
    concat_bytes_Z_mixed e (b :: (ys.map BYTE_I ++ [lastb])) = (do
      let z ← memory_byte_to_Z b
      let r ← concat_bytes_Z_mixed e (ys.map BYTE_I ++ [lastb])
      pure (z + (r <<< 8)) : EOUP Int)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|concat_bytes_Z_mixed_app_ret"
  concat_bytes_Z_mixed_app_ret : ∀ [Pa : Params] e (ys : List VellvmIntegers.int8) lastb v,
    concat_bytes_Z_mixed e [lastb] = raise_ret (NoPois v) →
    concat_bytes_Z_mixed e (ys.map BYTE_I ++ [lastb]) =
      raise_ret (NoPois (concat_bytes_Z (ys.map Integers.unsigned) + v * 2^(8*ys.length)))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|gen_plain"
  gen_plain : ∀ [Pa : Params] {sz} (x : Integers.bit_int sz) idx, memory_byte_of_dvalue_bv (BYTE_I x) idx = BYTE_I (Integers.repr (extract_byte_vint x idx))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_int_block_mixed"
  read_int_block_mixed : ∀ [Pa : Params] {sz} (x : Integers.bit_int sz), sz.val % 8 ≠ 0 → memory_bytes_to_dvalue_base
    ((Nseq 0 (store_size_dtyp (DTYPE_I sz))).map (memory_byte_of_dvalue_bv (BYTE_I x))) (DTYPE_I sz) = raise_ret (DVALUE_I sz x)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_base_block_double"
  read_base_block_double : ∀ [Pa : Params] d, memory_bytes_to_dvalue_base
    ((Nseq 0 (store_size_dtyp (DTYPE_FP FP_double))).map (base_byte_gen (DVALUE_Double d))) (DTYPE_FP FP_double) = raise_ret (DVALUE_Double d)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_base_block_float"
  read_base_block_float : ∀ [Pa : Params] f, memory_bytes_to_dvalue_base
    ((Nseq 0 (store_size_dtyp (DTYPE_FP FP_float))).map (base_byte_gen (DVALUE_Float f))) (DTYPE_FP FP_float) = raise_ret (DVALUE_Float f)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bytes_to_int_of_read"
  memory_bytes_to_int_of_read : ∀ [Pa : Params] {sz} {x : Integers.bit_int sz} (dbs : List memory_byte),
    memory_bytes_to_dvalue_base dbs (DTYPE_I sz) = raise_ret (DVALUE_I sz x) →
    ∃ v, memory_bytes_to_int sz dbs = raise_ret (NoPois v) ∧ Integers.repr v = x

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|pointer_slice_from_run"
  pointer_slice_from_run : ∀ [Pa : Params] (p : Pa.PTR.ptr) n i,
    pointer_slice_from p i ((Nseq i n).map (fun j ↦ (BYTE_Pointer p j : memory_byte))) = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|BYTE_I_byte0"
  BYTE_I_byte0 : ∀ [Pa : Params] {sz} (x : Integers.bit_int sz),
    memory_byte_of_dvalue_bv (BYTE_I x) 0 = BYTE_I (Integers.repr (extract_byte_vint x 0)) ∨
    ∃ b bs, memory_byte_of_dvalue_bv (BYTE_I x) 0 = BYTE_Mixed (Bit_bit b :: bs)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|all_poison_BYTE_I_block"
  all_poison_BYTE_I_block : ∀ [Pa : Params] {sz} (x : Integers.bit_int sz) {k}, 0 < k →
    all_poison_bytes ((Nseq 0 k).map (memory_byte_of_dvalue_bv (BYTE_I x))) = false

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|pointer_slice_BYTE_I_block"
  pointer_slice_BYTE_I_block : ∀ [Pa : Params] {sz} (x : Integers.bit_int sz) {k}, 0 < k →
    memory_bytes_to_pointer_slice ((Nseq 0 k).map (memory_byte_of_dvalue_bv (BYTE_I x))) = none

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|In_get_bits"
  In_get_bits : ∀ [Pa : Params] (dbs : List memory_byte) n acc b, b ∈ get_bits_of_memory_byte_list n dbs acc →
    b ∈ acc ∨ b = Bit_psn ∨ ∃ d ∈ dbs, b ∈ memory_byte_to_memory_bits d

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|In_get_bits_full"
  In_get_bits_full : ∀ [Pa : Params] (dbs : List memory_byte) {n} acc b, n ≤ 8 * dbs.length →
    b ∈ get_bits_of_memory_byte_list n dbs acc → b ∈ acc ∨ ∃ d ∈ dbs, b ∈ memory_byte_to_memory_bits d

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|BYTE_I_byte_no_ptr"
  BYTE_I_byte_no_ptr : ∀ [Pa : Params] {sz} {x : Integers.bit_int sz} {idx b},
    b ∈ memory_byte_to_memory_bits (memory_byte_of_dvalue_bv (BYTE_I x) idx) → is_ptr_bit b = false

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|no_ptr_bits_BYTE_I_block"
  no_ptr_bits_BYTE_I_block : ∀ [Pa : Params] {sz} (x : Integers.bit_int sz) k,
    ((get_bits_of_memory_byte_list sz.val ((Nseq 0 k).map (memory_byte_of_dvalue_bv (BYTE_I x))) []).reverseAux []).any is_ptr_bit = false

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|BYTE_I_byte_no_psn"
  BYTE_I_byte_no_psn : ∀ [Pa : Params] {sz} {x : Integers.bit_int sz} {idx b},
    b ∈ memory_byte_to_memory_bits (memory_byte_of_dvalue_bv (BYTE_I x) idx) → is_poison_bit b = false

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|no_psn_bits_BYTE_I_block"
  no_psn_bits_BYTE_I_block : ∀ [Pa : Params] {sz} (x : Integers.bit_int sz) k, sz.val ≤ 8 * k →
    ((get_bits_of_memory_byte_list sz.val ((Nseq 0 k).map (memory_byte_of_dvalue_bv (BYTE_I x))) []).reverseAux []).any is_poison_bit = false

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|not_all_int_no_ptr_pois"
  not_all_int_no_ptr_pois : ∀ [Pa : Params] (bs : List memory_bit), (!bs.all is_int_bit) = true → bs.any is_ptr_bit = false → bs.any is_poison_bit = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_base_block_BYTE_I"
  read_base_block_BYTE_I : ∀ [Pa : Params] {sz} (x : Integers.bit_int sz), memory_bytes_to_dvalue_base
    ((Nseq 0 (store_size_dtyp (DTYPE_B sz))).map (memory_byte_of_dvalue_bv (BYTE_I x))) (DTYPE_B sz) = raise_ret (DVALUE_B sz (BYTE_I x))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|all_poison_pointer_run"
  all_poison_pointer_run : ∀ [Pa : Params] (p : Pa.PTR.ptr) i n,
    all_poison_bytes ((Nseq i (n+1)).map (fun j ↦ (BYTE_Pointer p j : memory_byte))) = false

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bytes_to_pointer_slice_run"
  memory_bytes_to_pointer_slice_run : ∀ [Pa : Params] (p : Pa.PTR.ptr) i n, memory_bytes_to_pointer_slice
    ((Nseq i (n+1)).map (fun j ↦ (BYTE_Pointer p j : memory_byte))) = some (p,i)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_base_block_BYTE_Pointer"
  read_base_block_BYTE_Pointer : ∀ [Pa : Params] (sz : Positive) (p : Pa.PTR.ptr) k, sz.val % 8 = 0 → memory_bytes_to_dvalue_base
    ((Nseq 0 (store_size_dtyp (DTYPE_B sz))).map (memory_byte_of_dvalue_bv (BYTE_Pointer (bit_sz := sz) p k)))
      (DTYPE_B sz) = raise_ret (DVALUE_B sz (BYTE_Pointer p k))
