import PortChecks.SourceType
import Vellvm.Theory.MemoryBytesFacts.Reader

open Vellvm Vellvm.Syntax.DynamicTypes Vellvm.Semantics
open Interfaces.Params Interfaces.Sizeof DynamicValues MemoryBytes EOU Vellvm.Utils.ListUtil
open Vellvm.Theory.MemoryBytesFacts

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|valid_pointer_bits_of_run"
  Vellvm.Theory.MemoryBytesFacts.valid_pointer_bits_of_run : ∀ [Pa : Params],
    ∀ (bits : List memory_bit) (p : Pa.PTR.ptr) (base off : Nat),
    all_pointer_bits_from p (base + off) bits = true → bits.length + off = 8 →
    valid_pointer_bits p base off bits = raise_ret (some true)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|BYTE_Pointer_bits"
  Vellvm.Theory.MemoryBytesFacts.BYTE_Pointer_bits : ∀ [Pa : Params],
    ∀ (p : Pa.PTR.ptr) (k : Nat),
    memory_byte_to_memory_bits (BYTE_Pointer p k) = (Nseq (8 * k) 8).map (Bit_ptr p)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|pointer_byte_at_run"
  Vellvm.Theory.MemoryBytesFacts.pointer_byte_at_run : ∀ [Pa : Params],
    ∀ (b : memory_byte) (p : Pa.PTR.ptr) (i : Nat), memory_byte_wf b →
    all_pointer_bits_from p (8 * i) (memory_byte_to_memory_bits b) = true → pointer_byte_at p i b = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|pointer_slice_from_chunk"
  Vellvm.Theory.MemoryBytesFacts.pointer_slice_from_chunk : ∀ [Pa : Params],
    ∀ {dbs : List memory_byte} (p : Pa.PTR.ptr) (i : Nat) {n : Nat},
    List.Forall memory_byte_wf dbs → 8 * dbs.length ≤ n →
    all_pointer_bits_from p (8 * i) (get_bits_fwd n dbs) = true → pointer_slice_from p i dbs = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|pointer_slice_of_chunk"
  Vellvm.Theory.MemoryBytesFacts.pointer_slice_of_chunk : ∀ [Pa : Params],
    ∀ {sz : Positive} {dbs : List memory_byte}, List.Forall memory_byte_wf dbs →
    8 * dbs.length ≤ sz.val → is_pointer_chunk sz (get_bits_fwd sz.val dbs) = true →
    ∃ p k, memory_bytes_to_pointer_slice dbs = some (p, k) ∧ pointer_chunk_aligned sz k = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|mix_not_all_int"
  Vellvm.Theory.MemoryBytesFacts.mix_not_all_int : ∀ [Pa : Params],
    ∀ l : List memory_bit, (l.any is_ptr_bit || l.any is_poison_bit) = true →
    l.all is_int_bit = false

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bytes_to_bits_value_canonical"
  Vellvm.Theory.MemoryBytesFacts.memory_bytes_to_bits_value_canonical : ∀ [Pa : Params],
    ∀ (sz : Positive) {dbs : List memory_byte},
    List.Forall memory_byte_wf dbs → dbs.length ≤ store_size_dtyp (DTYPE_Base (DTYPE_B sz)) →
    (∀ p k, memory_bytes_to_pointer_slice dbs = some (p, k) → pointer_chunk_aligned sz k = false) →
    dvalue_bv_all_poison (memory_bytes_to_bits_value sz dbs) = false →
    dvalue_bv_canonical (memory_bytes_to_bits_value sz dbs) = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bytes_to_byte_value_canonical"
  Vellvm.Theory.MemoryBytesFacts.memory_bytes_to_byte_value_canonical : ∀ [Pa : Params],
    ∀ {sz : Positive} {dbs : List memory_byte} {bv : dvalue_bv sz},
    List.Forall memory_byte_wf dbs → dbs.length ≤ store_size_dtyp (DTYPE_Base (DTYPE_B sz)) →
    memory_bytes_to_byte_value sz dbs = raise_ret bv → dvalue_bv_all_poison bv = false →
    dvalue_bv_canonical bv = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bytes_to_dvalue_base_has_dtyp"
  Vellvm.Theory.MemoryBytesFacts.memory_bytes_to_dvalue_base_has_dtyp : ∀ [Pa : Params],
    ∀ (dt : dtyp_base) {dbs : List memory_byte} {v : dvalue_base},
    serializable_base dt → List.Forall memory_byte_wf dbs → dbs.length ≤ store_size_dtyp (DTYPE_Base dt) →
    memory_bytes_to_dvalue_base dbs dt = raise_ret v → dvalue_has_dtyp (DVALUE_Base v) (DTYPE_Base dt)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_struct_loop_has_dtyp"
  Vellvm.Theory.MemoryBytesFacts.read_struct_loop_has_dtyp : ∀ [Pa : Params],
    ∀ (rd : List memory_byte → dtyp → EOU dvalue) (np : Nat) (pad : Option Nat)
    (dts : List dtyp) (offset : Nat) {dbs : List memory_byte} {vs : List dvalue},
    (∀ t ∈ dts, ∀ mb v, List.Forall memory_byte_wf mb → rd mb t = raise_ret v → dvalue_has_dtyp v t) →
    (∀ t ∈ dts, NO_VOID t) → List.Forall memory_byte_wf dbs →
    read_struct_loop rd np pad offset dts dbs = raise_ret vs → List.Forall₂ dvalue_has_dtyp vs dts

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_array_loop_has_dtyp"
  Vellvm.Theory.MemoryBytesFacts.read_array_loop_has_dtyp : ∀ [Pa : Params],
    ∀ (rd : List memory_byte → dtyp → EOU dvalue) (np stride : Nat)
    {t : dtyp} (n offset : Nat) {dbs : List memory_byte} {vs : List dvalue},
    (∀ mb v, List.Forall memory_byte_wf mb → rd mb t = raise_ret v → dvalue_has_dtyp v t) →
    NO_VOID t → List.Forall memory_byte_wf dbs → read_array_loop rd np stride t n offset dbs = raise_ret vs →
    List.Forall (fun v ↦ dvalue_has_dtyp v t) vs ∧ vs.length = n

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|packed_bits_to_dvalue_has_dtyp"
  Vellvm.Theory.MemoryBytesFacts.packed_bits_to_dvalue_has_dtyp : ∀ [Pa : Params],
    ∀ {tb : dtyp_base} {m : Positive} (bits : List memory_bit),
    (tb = DTYPE_I m ∨ tb = DTYPE_B m) → m.val % 8 ≠ 0 → bits.length = m.val →
    dvalue_has_dtyp (packed_bits_to_dvalue tb m bits) (DTYPE_Base tb)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|packed_bits_to_elts_has_dtyp"
  Vellvm.Theory.MemoryBytesFacts.packed_bits_to_elts_has_dtyp : ∀ [Pa : Params],
    ∀ {tb : dtyp_base} {m : Positive} (n : Nat) (bits : List memory_bit),
    (tb = DTYPE_I m ∨ tb = DTYPE_B m) → m.val % 8 ≠ 0 → n * m.val ≤ bits.length →
    List.Forall (fun v ↦ dvalue_has_dtyp v (DTYPE_Base tb)) (packed_bits_to_elts tb m n bits) ∧
    (packed_bits_to_elts tb m n bits).length = n

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bytes_to_dvalue_has_dtyp"
  Vellvm.Theory.MemoryBytesFacts.memory_bytes_to_dvalue_has_dtyp : ∀ [Pa : Params],
    ∀ (dt : dtyp) {mb : List memory_byte} {dv : dvalue},
    serializable dt → List.Forall memory_byte_wf mb → memory_bytes_to_dvalue mb dt = raise_ret dv →
    dvalue_has_dtyp dv dt

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bytes_to_dvalue_idempotent"
  Vellvm.Theory.MemoryBytesFacts.memory_bytes_to_dvalue_idempotent : ∀ [Pa : Params],
    ∀ (dt : dtyp) {dv : dvalue} {mb1 mb2 : List memory_byte},
    serializable dt → List.Forall memory_byte_wf mb1 → memory_bytes_to_dvalue mb1 dt = raise_ret dv →
    dvalue_to_memory_bytes dt dv none = raise_ret mb2 → memory_bytes_to_dvalue mb2 dt = raise_ret dv

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_byte_of_dvalue_bv_wf"
  Vellvm.Theory.MemoryBytesFacts.memory_byte_of_dvalue_bv_wf : ∀ [Pa : Params],
    ∀ {sz : Positive} (bv : dvalue_bv sz) (idx : Nat),
    memory_byte_wf (memory_byte_of_dvalue_bv bv idx)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|poison_memory_byte_wf"
  Vellvm.Theory.MemoryBytesFacts.poison_memory_byte_wf : ∀ [Pa : Params],
    memory_byte_wf (poison_memory_byte (Pa := Pa))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|Forall_wf_poison_app"
  Vellvm.Theory.MemoryBytesFacts.Forall_wf_poison_app : ∀ [Pa : Params],
    ∀ (k : Nat) {acc : List memory_byte}, List.Forall memory_byte_wf acc →
    List.Forall memory_byte_wf (List.replicate k poison_memory_byte ++ acc)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|accumulate_padding_wf"
  Vellvm.Theory.MemoryBytesFacts.accumulate_padding_wf : ∀ [Pa : Params],
    ∀ (o : Nat) (q : Option Nat) {acc : List memory_byte}, List.Forall memory_byte_wf acc →
    List.Forall memory_byte_wf (accumulate_padding o q acc).2

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|accumulate_padding_bytes_wf"
  Vellvm.Theory.MemoryBytesFacts.accumulate_padding_bytes_wf : ∀ [Pa : Params],
    ∀ (o n : Nat) {acc : List memory_byte}, List.Forall memory_byte_wf acc →
    List.Forall memory_byte_wf (accumulate_padding_bytes o n acc).2

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|acc_memory_bytes_of_dvalue_base_wf"
  Vellvm.Theory.MemoryBytesFacts.acc_memory_bytes_of_dvalue_base_wf : ∀ [Pa : Params],
    ∀ (dtb : dtyp_base) (dv : dvalue_base) (offset : Nat)
    {acc : List memory_byte}, List.Forall memory_byte_wf acc →
    List.Forall memory_byte_wf (acc_memory_bytes_of_dvalue_base dtb dv offset acc).2

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|struct_bytes_loop_wf"
  Vellvm.Theory.MemoryBytesFacts.struct_bytes_loop_wf : ∀ [Pa : Params],
    ∀ (ser : dtyp → dvalue → Nat → Option Nat → List memory_byte → EOU (Nat × List memory_byte))
    (ta pad : Option Nat) (fields : List dvalue) (types : List dtyp) (offset : Nat)
    {acc : List memory_byte} {r : Nat × List memory_byte},
    (∀ f ∈ fields, ∀ dt o ta' acc' r', List.Forall memory_byte_wf acc' → ser dt f o ta' acc' = raise_ret r' →
      List.Forall memory_byte_wf r'.2) → List.Forall memory_byte_wf acc →
    struct_bytes_loop ser ta pad fields types offset acc = raise_ret r → List.Forall memory_byte_wf r.2

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|array_bytes_loop_wf"
  Vellvm.Theory.MemoryBytesFacts.array_bytes_loop_wf : ∀ [Pa : Params],
    ∀ (ser : dtyp → dvalue → Nat → Option Nat → List memory_byte → EOU (Nat × List memory_byte))
    (ta : Option Nat) (dt : dtyp) (elt_pad : Nat) (elts : List dvalue) (offset : Nat)
    {acc : List memory_byte} {r : Nat × List memory_byte},
    (∀ e ∈ elts, ∀ o ta' acc' r', List.Forall memory_byte_wf acc' → ser dt e o ta' acc' = raise_ret r' →
      List.Forall memory_byte_wf r'.2) → List.Forall memory_byte_wf acc →
    array_bytes_loop ser ta dt elt_pad elts offset acc = raise_ret r → List.Forall memory_byte_wf r.2

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|packed_fwd_wf"
  Vellvm.Theory.MemoryBytesFacts.packed_fwd_wf : ∀ [Pa : Params],
    ∀ (nb : Nat) (bits : List memory_bit), List.Forall memory_byte_wf (packed_fwd nb bits)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|packed_vector_bytes_wf"
  Vellvm.Theory.MemoryBytesFacts.packed_vector_bytes_wf : ∀ [Pa : Params],
    ∀ (m : Positive) (dt : dtyp) (elts : List dvalue) (offset : Nat) (ta : Option Nat)
    {acc : List memory_byte} {r : Nat × List memory_byte}, List.Forall memory_byte_wf acc →
    packed_vector_bytes m dt elts offset ta acc = raise_ret r → List.Forall memory_byte_wf r.2

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|acc_dvalue_to_memory_bytes_h_wf"
  Vellvm.Theory.MemoryBytesFacts.acc_dvalue_to_memory_bytes_h_wf : ∀ [Pa : Params],
    ∀ (dv : dvalue) (dt : dtyp) (offset : Nat) (ta : Option Nat)
    {acc : List memory_byte} {r : Nat × List memory_byte}, List.Forall memory_byte_wf acc →
    acc_dvalue_to_memory_bytes_h dt dv offset ta acc = raise_ret r → List.Forall memory_byte_wf r.2

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|dvalue_to_memory_bytes_wf"
  Vellvm.Theory.MemoryBytesFacts.dvalue_to_memory_bytes_wf : ∀ [Pa : Params],
    ∀ (dt : dtyp) (dv : dvalue) (ta : Option Nat) {mb : List memory_byte},
    dvalue_to_memory_bytes dt dv ta = raise_ret mb → List.Forall memory_byte_wf mb

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bytes_to_dvalue_idempotent_written"
  Vellvm.Theory.MemoryBytesFacts.memory_bytes_to_dvalue_idempotent_written : ∀ [Pa : Params],
    ∀ (dt : dtyp) (dv0 : dvalue) (ta : Option Nat)
    {dv : dvalue} {mb1 mb2 : List memory_byte}, serializable dt → dvalue_to_memory_bytes dt dv0 ta = raise_ret mb1 →
    memory_bytes_to_dvalue mb1 dt = raise_ret dv → dvalue_to_memory_bytes dt dv none = raise_ret mb2 →
    memory_bytes_to_dvalue mb2 dt = raise_ret dv
