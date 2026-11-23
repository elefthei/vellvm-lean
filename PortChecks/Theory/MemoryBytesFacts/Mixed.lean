import PortChecks.SourceType
import Vellvm.Theory.MemoryBytesFacts.Mixed

open Vellvm Vellvm.Semantics Vellvm.Syntax.DynamicTypes Vellvm.Utils.ListUtil
open DynamicValues MemoryBytes EOU Interfaces.Params Interfaces.Sizeof
open Vellvm.Theory.MemoryBytesFacts

private abbrev rendered [Params] (bits : List memory_bit) (n : Nat) :=
  (Nseq 0 n).map (mixed_byte bits)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|mixed_byte"
  mixed_byte : ∀ [Params], List memory_bit → Nat → memory_byte

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|writer_mixed_byte"
  writer_mixed_byte : ∀ [Params] (sz : Positive) (bits : List memory_bit) (idx : Nat),
    memory_byte_of_dvalue_bv (BYTE_Mixed (bit_sz := sz) bits) idx = mixed_byte bits idx

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|mixed_byte_shift"
  mixed_byte_shift : ∀ [Params] (bits : List memory_bit) (j : Nat),
    mixed_byte bits (1 + j) = mixed_byte (drop 8 bits) j

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_byte_to_memory_bits_mixed"
  memory_byte_to_memory_bits_mixed : ∀ [Params] (bits : List memory_bit) (idx : Nat),
    memory_byte_to_memory_bits (mixed_byte bits idx) =
      (let m := take 8 (drop (8 * idx) bits)
       m ++ (if !(m.length == 8) then List.replicate (8 - m.length) Bit_psn else []))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|get_bits_writer"
  get_bits_writer : ∀ [Params] (n : Nat) (bits acc : List memory_bit), bits.length ≤ 8 * n →
    get_bits_of_memory_byte_list bits.length (rendered bits n) acc = bits.reverseAux acc

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|all_poison_bytes_forallb"
  all_poison_bytes_forallb : ∀ [Params] (l : List memory_byte),
    all_poison_bytes l = l.all is_all_poison_byte

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|mixed_all_poison"
  mixed_all_poison : ∀ [Params] (n : Nat) (bits : List memory_bit), bits.length ≤ 8 * n →
    (rendered bits n).all is_all_poison_byte = true → bits.all is_poison_bit = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|map_monad_bit_pois"
  map_monad_bit_pois : ∀ [Params] (l : List memory_bit), l.any is_poison_bit = true →
    map_monad (m := EOUP) memory_bit_to_bit l = raise_ret (none : Option (List Int))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bits_to_Z_pois"
  memory_bits_to_Z_pois : ∀ [Params] (l : List memory_bit), l.any is_poison_bit = true →
    memory_bits_to_Z l = raise_ret (none : Option Int)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_byte_to_Z_mixed_pois"
  memory_byte_to_Z_mixed_pois : ∀ [Params] (bits : List memory_bit) (idx : Nat),
    (take 8 (drop (8 * idx) bits)).any is_poison_bit = true →
    memory_byte_to_Z (mixed_byte bits idx) = raise_ret none

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|map_monad_bit_ret"
  map_monad_bit_ret : ∀ [Params] (l : List memory_bit),
    ∃ r : Option (List Int), map_monad (m := EOUP) memory_bit_to_bit l = raise_ret r

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bits_to_Z_total"
  memory_bits_to_Z_total : ∀ [Params] (bits : List memory_bit),
    memory_bits_to_Z bits = raise_ret none ∨ ∃ z, memory_bits_to_Z bits = raise_ret (some z)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_byte_to_Z_mixed_ret"
  memory_byte_to_Z_mixed_ret : ∀ [Params] (bits : List memory_bit) (idx : Nat),
    ∃ r : Option Int, memory_byte_to_Z (mixed_byte bits idx) = raise_ret r

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|map_monad_byte_mixed_pois"
  map_monad_byte_mixed_pois : ∀ [Params] (n : Nat) (bits : List memory_bit),
    bits.length ≤ 8 * n → bits.any is_poison_bit = true →
    map_monad (m := EOUP) memory_byte_to_Z (rendered bits n) = raise_ret none

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|cbmix_cons"
  cbmix_cons : ∀ [Params] (extra : Nat) (b : memory_byte) (f : Nat → memory_byte) (a n : Nat),
    concat_bytes_Z_mixed extra (b :: (Nseq a (n + 1)).map f) =
    (do let z ← memory_byte_to_Z b
        let r ← concat_bytes_Z_mixed extra ((Nseq a (n + 1)).map f)
        pure (z + (r <<< 8)) : EOUP Int)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|concat_bytes_Z_mixed_mixed_pois"
  concat_bytes_Z_mixed_mixed_pois : ∀ [Params] (n : Nat) {extra : Nat} (bits : List memory_bit),
    (0 < extra ∧ extra ≤ 8) → bits.length = 8 * n + extra → bits.any is_poison_bit = true →
    concat_bytes_Z_mixed extra (rendered bits (n + 1)) = raise_ret none

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|all_pointer_bits_from_app"
  all_pointer_bits_from_app : ∀ [Pa : Params] (l₁ : List memory_bit) (p : Pa.PTR.ptr) (j : Nat)
    (l₂ : List memory_bit), all_pointer_bits_from p j (l₁ ++ l₂) =
      (all_pointer_bits_from p j l₁ && all_pointer_bits_from p (j + l₁.length) l₂)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|all_pointer_bits_from_repeat_psn"
  all_pointer_bits_from_repeat_psn : ∀ [Pa : Params] (m : Nat) (p : Pa.PTR.ptr) (j : Nat),
    all_pointer_bits_from p j (List.replicate m Bit_psn) = true → m = 0

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|valid_pointer_bits_implies"
  valid_pointer_bits_implies : ∀ [Pa : Params] (l : List memory_bit) (p : Pa.PTR.ptr)
    (base offset : Nat), valid_pointer_bits p base offset l = raise_ret (some true) →
    all_pointer_bits_from p (base + offset) l = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|pointer_slice_implies_bits"
  pointer_slice_implies_bits : ∀ [Pa : Params] (n : Nat) (bits : List memory_bit) (p : Pa.PTR.ptr)
    (k : Nat), bits.length ≤ 8 * n → pointer_slice_from p k (rendered bits n) = true →
    all_pointer_bits_from p (8 * k) bits = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|mixed_block_head"
  mixed_block_head : ∀ [Params] (bits : List memory_bit) (n : Nat), rendered bits (n + 1) =
    mixed_byte bits 0 :: (Nseq 1 n).map (mixed_byte bits)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|mixed_byte_0"
  mixed_byte_0 : ∀ [Params] (bits : List memory_bit), mixed_byte bits 0 =
    BYTE_Mixed (take 8 bits ++ (if !((take 8 bits).length == 8)
      then List.replicate (8 - (take 8 bits).length) Bit_psn else []))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|pointer_slice_head"
  pointer_slice_head : ∀ [Params] (bits : List memory_bit) (n : Nat),
    match bits with
    | .Bit_ptr q j :: _ => memory_bytes_to_pointer_slice (rendered bits (n + 1)) =
        (if pointer_slice_from q (j / 8) (rendered bits (n + 1)) then some (q, j / 8) else none)
    | _ => memory_bytes_to_pointer_slice (rendered bits (n + 1)) = none

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|pointer_slice_mixed_unaligned"
  pointer_slice_mixed_unaligned : ∀ [Pa : Params] (sz : Positive) {n : Nat} (bits : List memory_bit)
    {p : Pa.PTR.ptr} {k : Nat}, bits.length ≤ 8 * (n + 1) → (!is_pointer_chunk sz bits) = true →
    memory_bytes_to_pointer_slice (rendered bits (n + 1)) = some (p, k) →
    pointer_chunk_aligned sz k = false

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_base_block_BYTE_Mixed"
  read_base_block_BYTE_Mixed : ∀ [Params] {sz : Positive} (bits : List memory_bit),
    bits.length = sz.val → (!is_pointer_chunk sz bits) = true → (!(bits.all is_int_bit)) = true →
    (!(bits.all is_poison_bit)) = true → memory_bytes_to_dvalue_base
      ((Nseq 0 (store_size_dtyp (DTYPE_Base (DTYPE_B sz)))).map
        (memory_byte_of_dvalue_bv (BYTE_Mixed (bit_sz := sz) bits))) (DTYPE_B sz) =
      raise_ret (DVALUE_B sz (BYTE_Mixed bits))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_base_block"
  read_base_block : ∀ [Params] (dtb : dtyp_base) (dv : dvalue_base), serializable_base dtb →
    dvalue_base_has_dtyp_base dv dtb = true → dvalue_base_canonical dv = true →
    memory_bytes_to_dvalue_base ((Nseq 0 (store_size_dtyp (DTYPE_Base dtb))).map (base_byte_gen dv))
      dtb = raise_ret dv
