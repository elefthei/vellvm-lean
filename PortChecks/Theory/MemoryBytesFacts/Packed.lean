import PortChecks.SourceType
import Vellvm.Theory.MemoryBytesFacts.Packed

open Vellvm Vellvm.Numeric Vellvm.Semantics Vellvm.Semantics.Interfaces.Params
open Vellvm.Semantics.DynamicValues Vellvm.Semantics.MemoryBytes Vellvm.Semantics.VellvmIntegers
open Vellvm.Semantics.EOU Vellvm.Syntax.DynamicTypes Vellvm.Utils.ListUtil Vellvm.Utils.ZUtil
open Vellvm.Numeric.Integers (bit_int)
universe u
open Vellvm.Theory.MemoryBytesFacts

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_byte_wf"
  memory_byte_wf : ∀ [Pa : Params], memory_byte → Prop

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_byte_bits_length"
  memory_byte_bits_length : ∀ [Pa : Params] (mb : memory_byte), memory_byte_wf mb → (memory_byte_to_memory_bits mb).length = 8

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|get_bits_fwd"
  get_bits_fwd : ∀ [Pa : Params], Nat → List memory_byte → List memory_bit

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|get_bits_fwd_spec"
  get_bits_fwd_spec : ∀ [Pa : Params] (dbs : List memory_byte) (n : Nat) (acc : List memory_bit),
    get_bits_of_memory_byte_list n dbs acc = (get_bits_fwd n dbs).reverseAux acc

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|reader_bits_fwd"
  reader_bits_fwd : ∀ [Pa : Params] (n : Nat) (dbs : List memory_byte),
    (get_bits_of_memory_byte_list n dbs []).reverseAux [] = get_bits_fwd n dbs

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|get_bits_fwd_length"
  get_bits_fwd_length : ∀ [Pa : Params] {dbs : List memory_byte} (n : Nat),
    List.Forall memory_byte_wf dbs → (get_bits_fwd n dbs).length = n

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|concat_bits_Z_digits"
  concat_bits_Z_digits : ∀ l : List Int, concat_bits_Z l = concat_digits 1 l

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|concat_bytes_Z_digits"
  concat_bytes_Z_digits : ∀ l : List Int, concat_bytes_Z l = concat_digits 8 l

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|extract_bit_vint_8"
  extract_bit_vint_8 : ∀ (x : int8) {i : Nat}, i < 8 → extract_bit_vint x i = unsigned x / 2 ^ i % 2

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|BYTE_I_bits"
  BYTE_I_bits : ∀ [Pa : Params] (x : int8), memory_byte_to_memory_bits (BYTE_I (Pa := Pa) x) =
    (Nseq 0 8).map (fun i ↦ Bit_bit (VInt.repr (extract_bit_vint x i)))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|get_bits_fwd_concat"
  get_bits_fwd_concat : ∀ [Pa : Params] {dbs : List memory_byte} {n : Nat},
    List.Forall memory_byte_wf dbs → 8 * dbs.length = n →
    get_bits_fwd n dbs = (dbs.map memory_byte_to_memory_bits).flatten

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|bit_unsigned_range"
  bit_unsigned_range : ∀ b : int1, 0 ≤ unsigned b ∧ unsigned b < (2 : Int) ^ (1 : Nat)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bits_to_Z_ints"
  memory_bits_to_Z_ints : ∀ [Pa : Params] (bis : List int1),
    memory_bits_to_Z (bis.map (Bit_bit (Pa := Pa))) = raise_ret (some (concat_bits_Z (bis.map unsigned)))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|bytes_of_bits"
  bytes_of_bits : ∀ [Pa : Params], Nat → List memory_bit → List memory_byte

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|acc_bits_to_memory_bytes_fwd"
  acc_bits_to_memory_bytes_fwd : ∀ [Pa : Params] (n : Nat) (bits : List memory_bit) (acc : List memory_byte),
    acc_bits_to_memory_bytes n bits acc = (bytes_of_bits n bits).reverse ++ acc

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|all_int_bits_map"
  all_int_bits_map : ∀ [Pa : Params] (bits : List memory_bit), bits.all is_int_bit = true →
    ∃ bis : List int1, bits = bis.map Bit_bit

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|forallb_int_map"
  forallb_int_map : ∀ [Pa : Params] (bis : List int1), (bis.map (Bit_bit (Pa := Pa))).all is_int_bit = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|int_bits_to_Z_map"
  int_bits_to_Z_map : ∀ [Pa : Params] (bis : List int1),
    int_bits_to_Z (bis.map (Bit_bit (Pa := Pa))) = concat_bits_Z (bis.map unsigned)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|concat_bits_Z_range"
  concat_bits_Z_range : ∀ bis : List int1,
    0 ≤ concat_bits_Z (bis.map unsigned) ∧ concat_bits_Z (bis.map unsigned) < 2 ^ bis.length

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|concat_bits_Z_nth"
  concat_bits_Z_nth : ∀ (bis : List int1) {i : Nat}, i < bis.length →
    concat_bits_Z (bis.map unsigned) / 2 ^ i % 2 = unsigned (bis.getD i (VInt.repr 0))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|repr_unsigned_bit"
  repr_unsigned_bit : ∀ b : int1, VInt.repr (unsigned b) = b

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|extract_bit_vint_spec"
  extract_bit_vint_spec : ∀ {sz : Positive} (x : bit_int sz) {i : Nat},
    i < sz.val → extract_bit_vint x i = unsigned x / 2 ^ i % 2

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bits_from_map"
  memory_bits_from_map : ∀ [Pa : Params] (f : Nat → memory_bit) (n s : Nat),
    memory_bits_from f n s = (Nseq s n).map f

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|int_elt_bits"
  int_elt_bits : ∀ {m : Positive}, bit_int m → List int1

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|int_elt_bits_eq"
  int_elt_bits_eq : ∀ [Pa : Params] {m : Positive} (x : bit_int m),
    memory_bits_from (fun i ↦ Bit_bit (Pa := Pa) (VInt.repr (extract_bit_vint x i))) m.val 0 =
      (int_elt_bits x).map Bit_bit

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|int_elt_bits_length"
  int_elt_bits_length : ∀ {m : Positive} (x : bit_int m), (int_elt_bits x).length = m.val

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|int_elt_bits_value"
  int_elt_bits_value : ∀ {m : Positive} (x : bit_int m), concat_bits_Z ((int_elt_bits x).map unsigned) = unsigned x

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_byte_of_bits_int"
  memory_byte_of_bits_int : ∀ [Pa : Params] (bis : List int1), bis.length = 8 →
    memory_byte_to_memory_bits (memory_byte_of_bits (bis.map (Bit_bit (Pa := Pa)))) = bis.map Bit_bit

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|take_app_ge"
  take_app_ge : ∀ {A : Type u} (l r : List A) {n : Nat}, l.length ≤ n →
    take n (l ++ r) = l ++ take (n - l.length) r

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|take_add"
  take_add : ∀ {A : Type u} (l : List A) (a b : Nat),
    take (a + b) l = take a l ++ take b (drop a l)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_byte_of_bits_bits"
  memory_byte_of_bits_bits : ∀ [Pa : Params] (c : List memory_bit), c.length = 8 →
    memory_byte_to_memory_bits (memory_byte_of_bits c) = c

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_byte_of_bits_wf"
  memory_byte_of_bits_wf : ∀ [Pa : Params] (c : List memory_bit), c.length = 8 → memory_byte_wf (memory_byte_of_bits c)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|take_8_length"
  take_8_length : ∀ [Pa : Params] (l : List memory_bit), 8 ≤ l.length → (take 8 l).length = 8

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|drop_8_length"
  drop_8_length : ∀ [Pa : Params] (l : List memory_bit), (drop 8 l).length = l.length - 8

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|bytes_of_bits_length"
  bytes_of_bits_length : ∀ [Pa : Params] (n : Nat) (l : List memory_bit), (bytes_of_bits n l).length = n

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|bytes_of_bits_wf"
  bytes_of_bits_wf : ∀ [Pa : Params] (n : Nat) (l : List memory_bit), 8 * n ≤ l.length →
    List.Forall memory_byte_wf (bytes_of_bits n l)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|bytes_of_bits_bits"
  bytes_of_bits_bits : ∀ [Pa : Params] (n : Nat) (l : List memory_bit), 8 * n ≤ l.length →
    ((bytes_of_bits n l).map memory_byte_to_memory_bits).flatten = take (8 * n) l

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|get_bits_fwd_app"
  get_bits_fwd_app : ∀ [Pa : Params] {dbs : List memory_byte} (extra : List memory_byte) {k : Nat},
    List.Forall memory_byte_wf dbs → k ≤ 8 * dbs.length →
    get_bits_fwd k (dbs ++ extra) = take k (dbs.map memory_byte_to_memory_bits).flatten

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|packed_bits_to_dvalue_poison"
  packed_bits_to_dvalue_poison : ∀ [Pa : Params] (t : dtyp_base) (m : Positive) {bits : List memory_bit},
    bits ≠ [] → bits.all is_poison_bit = true → packed_bits_to_dvalue t m bits = DVALUE_Base DVALUE_Poison

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|repeat_psn_ne"
  repeat_psn_ne : ∀ [Pa : Params] (m : Positive), List.replicate m.val (Bit_psn (Pa := Pa)) ≠ []

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|forallb_poison_bits_repeat"
  forallb_poison_bits_repeat : ∀ [Pa : Params] (k : Nat),
    (List.replicate k (Bit_psn (Pa := Pa))).all is_poison_bit = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|int_elt_bits_ne"
  int_elt_bits_ne : ∀ [Pa : Params] {m : Positive} (x : bit_int m),
    (int_elt_bits x).map (Bit_bit (Pa := Pa)) ≠ []

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|forallb_poison_int_bits"
  forallb_poison_int_bits : ∀ [Pa : Params] {bis : List int1}, bis ≠ [] →
    (bis.map (Bit_bit (Pa := Pa))).all is_poison_bit = false

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|map_Bit_bit_ne"
  map_Bit_bit_ne : ∀ [Pa : Params] {bis : List int1}, (bis.map (Bit_bit (Pa := Pa))) ≠ [] → bis ≠ []

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|packed_elt_round_trip"
  packed_elt_round_trip : ∀ [Pa : Params] {tb : dtyp_base} {m : Positive} {e : dvalue} {bits : List memory_bit},
    (tb = DTYPE_I m ∨ tb = DTYPE_B m) → m.val % 8 ≠ 0 → dvalue_has_dtyp e (DTYPE_Base tb) →
    packed_elt_bits m e = raise_ret bits → bits.length = m.val ∧ packed_bits_to_dvalue tb m bits = e

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|packed_bits_to_elts_concat"
  packed_bits_to_elts_concat : ∀ [Pa : Params] (tb : dtyp_base) (m : Positive) {elts : List dvalue}
    {bitss : List (List memory_bit)} (rest : List memory_bit),
    List.Forall₂ (fun e b ↦ b.length = m.val ∧ packed_bits_to_dvalue tb m b = e) elts bitss →
    packed_bits_to_elts tb m elts.length (bitss.flatten ++ rest) = elts

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|concat_length_uniform"
  concat_length_uniform : ∀ [Pa : Params] (tb : dtyp_base) (m : Positive) {elts : List dvalue}
    {bitss : List (List memory_bit)},
    List.Forall₂ (fun e b ↦ b.length = m.val ∧ packed_bits_to_dvalue tb m b = e) elts bitss →
    bitss.flatten.length = elts.length * m.val

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|get_bits_fwd_all_poison"
  get_bits_fwd_all_poison : ∀ [Pa : Params] (dbs : List memory_byte) (n : Nat),
    dbs.all is_all_poison_byte = true → (get_bits_fwd n dbs).all is_poison_bit = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|packed_bits_to_elts_poison"
  packed_bits_to_elts_poison : ∀ [Pa : Params] (tb : dtyp_base) (m : Positive) (n : Nat) (bits : List memory_bit),
    bits.all is_poison_bit = true → n * m.val ≤ bits.length →
    (packed_bits_to_elts tb m n bits).all dvalue_is_poison = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|packed_fwd"
  packed_fwd : ∀ [Pa : Params], Nat → List memory_bit → List memory_byte

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|acc_packed_bits_fwd"
  acc_packed_bits_fwd : ∀ [Pa : Params] (nb : Nat) (bits : List memory_bit) (acc : List memory_byte),
    acc_packed_bits_to_memory_bytes nb bits acc = (packed_fwd nb bits).reverse ++ acc

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|packed_round_trip"
  packed_round_trip : ∀ [Pa : Params] {tb : dtyp_base} {m : Positive} (sz : Nat) {elts : List dvalue}
    {bitss : List (List memory_bit)}, (tb = DTYPE_I m ∨ tb = DTYPE_B m) → m.val % 8 ≠ 0 →
    List.Forall (fun e ↦ dvalue_has_dtyp e (DTYPE_Base tb)) elts → elts.length = sz →
    map_monad (packed_elt_bits m) elts = raise_ret bitss →
    let fwd := packed_fwd ((sz * m.val + 7) / 8) bitss.flatten
    List.Forall memory_byte_wf fwd ∧ fwd.length = (sz * m.val + 7) / 8 ∧
      (∀ extra, packed_vector_elts tb m sz (fwd ++ extra) = elts) ∧
      (elts.all dvalue_is_poison = false → fwd.all is_all_poison_byte = false)
