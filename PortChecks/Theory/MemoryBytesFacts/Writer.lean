import PortChecks.SourceType
import Vellvm.Theory.MemoryBytesFacts.Writer

open Vellvm Vellvm.Syntax.DynamicTypes Vellvm.Semantics Vellvm.Semantics.DynamicValues
open Vellvm.Semantics.EOU Vellvm.Semantics.MemoryBytes Vellvm.Semantics.Interfaces.Params
open Vellvm.Semantics.Interfaces.Sizeof Vellvm.Theory.MemoryBytesFacts Vellvm.Utils.ListUtil

private abbrev Serializer [Params] :=
  dtyp → dvalue → Nat → Option Nat → List memory_byte → EOU (Nat × List memory_byte)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|tapad"
  tapad : Option Nat → Nat → Nat
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|tapad_ge"
  tapad_ge : ∀ ta x, x ≤ tapad ta x
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|accumulate_poison_bytes_length"
  accumulate_poison_bytes_length : ∀ [Params] n acc,
    (accumulate_poison_bytes n acc).length = n + acc.length
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|accumulate_padding_spec"
  accumulate_padding_spec : ∀ [Params] offset ta acc,
    (accumulate_padding offset ta acc).1 = tapad ta offset ∧
    (accumulate_padding offset ta acc).2.length = acc.length + (tapad ta offset - offset)
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|accumulate_padding_bytes_spec"
  accumulate_padding_bytes_spec : ∀ [Params] offset n acc,
    (accumulate_padding_bytes offset n acc).1 = offset + n ∧
    (accumulate_padding_bytes offset n acc).2.length = acc.length + n
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|acc_memory_bytes_of_dvalue_base_spec"
  acc_memory_bytes_of_dvalue_base_spec : ∀ [Params] dtb dv offset acc,
    (acc_memory_bytes_of_dvalue_base dtb dv offset acc).1 = store_size_dtyp (DTYPE_Base dtb) + offset ∧
    (acc_memory_bytes_of_dvalue_base dtb dv offset acc).2.length = acc.length + store_size_dtyp (DTYPE_Base dtb)
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|struct_bytes_loop"
  struct_bytes_loop : ∀ [Params], Serializer → Option Nat → Option Nat → List dvalue → List dtyp →
    Nat → List memory_byte → EOU (Nat × List memory_byte)
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|array_bytes_loop"
  array_bytes_loop : ∀ [Params], Serializer → Option Nat → dtyp → Nat → List dvalue →
    Nat → List memory_byte → EOU (Nat × List memory_byte)
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|ser_struct_unfold"
  ser_struct_unfold : ∀ [Params] p ts q fs o ta acc,
    acc_dvalue_to_memory_bytes_h (DTYPE_Struct p ts) (DVALUE_Struct q fs) o ta acc =
    struct_bytes_loop acc_dvalue_to_memory_bytes_h ta (if p then none else some (max_preferred_dtyp_alignment ts)) fs ts o acc
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|packed_vector_bytes"
  packed_vector_bytes : ∀ [Params], Positive → dtyp → List dvalue → Nat → Option Nat →
    List memory_byte → EOU (Nat × List memory_byte)
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|ser_array_unfold"
  ser_array_unfold : ∀ [Params] vec sz t p elts o ta acc,
    acc_dvalue_to_memory_bytes_h (DTYPE_Array vec sz t) (DVALUE_Array p elts) o ta acc =
    match packed_vector_type (DTYPE_Array vec sz t) with
    | some (_, m) => packed_vector_bytes m (DTYPE_Array vec sz t) elts o ta acc
    | none => array_bytes_loop acc_dvalue_to_memory_bytes_h ta t
        (if vec then 0 else alloc_size_dtyp t - store_size_dtyp t) elts o acc
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|packed_vector_type_Some"
  packed_vector_type_Some : ∀ dt {tb m}, packed_vector_type dt = some (tb, m) →
    ∃ sz, dt = DTYPE_Array true sz (DTYPE_Base tb) ∧ (tb = DTYPE_I m ∨ tb = DTYPE_B m) ∧ m.val % 8 ≠ 0
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|store_size_packed_vector"
  store_size_packed_vector : ∀ [Params] dt {tb m}, packed_vector_type dt = some (tb, m) →
    ∃ sz, dt = DTYPE_Array true sz (DTYPE_Base tb) ∧ store_size_dtyp dt = (sz * m.val + 7) / 8
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|store_size_unpacked_vector"
  store_size_unpacked_vector : ∀ [Params] sz t, packed_vector_type (DTYPE_Array true sz t) = none →
    store_size_dtyp (DTYPE_Array true sz t) = sz * store_size_dtyp t
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|acc_bits_to_memory_bytes_length"
  acc_bits_to_memory_bytes_length : ∀ [Params] n bits acc,
    (acc_bits_to_memory_bytes n bits acc).length = n + acc.length
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|acc_packed_bits_to_memory_bytes_length"
  acc_packed_bits_to_memory_bytes_length : ∀ [Params] n bits acc,
    (acc_packed_bits_to_memory_bytes n bits acc).length = acc.length + n
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|packed_vector_bytes_spec"
  packed_vector_bytes_spec : ∀ [Params] m dt elts offset ta acc {offset' bs},
    packed_vector_bytes m dt elts offset ta acc = raise_ret (offset', bs) →
    offset' = tapad ta (offset + store_size_dtyp dt) ∧ bs.length = acc.length + (offset' - offset)
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|ser_base_unfold"
  ser_base_unfold : ∀ [Params] dtb dv o ta acc,
    acc_dvalue_to_memory_bytes_h (DTYPE_Base dtb) (DVALUE_Base dv) o ta acc =
    let (o', bs) := acc_memory_bytes_of_dvalue_base dtb dv o acc
    raise_ret (accumulate_padding o' ta bs)
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|ser_struct_poison_unfold"
  ser_struct_poison_unfold : ∀ [Params] p ts o ta acc,
    acc_dvalue_to_memory_bytes_h (DTYPE_Struct p ts) (DVALUE_Base DVALUE_Poison) o ta acc =
    let (o', bs) := accumulate_padding_bytes o (store_size_dtyp (DTYPE_Struct p ts)) acc
    raise_ret (accumulate_padding o' ta bs)
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|ser_array_poison_unfold"
  ser_array_poison_unfold : ∀ [Params] v n t o ta acc,
    acc_dvalue_to_memory_bytes_h (DTYPE_Array v n t) (DVALUE_Base DVALUE_Poison) o ta acc =
    let (o', bs) := accumulate_padding_bytes o (store_size_dtyp (DTYPE_Array v n t)) acc
    raise_ret (accumulate_padding o' ta bs)
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|sfe_step"
  sfe_step : ∀ [Params], Option Nat → Nat → dtyp → Nat
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|struct_bytes_loop_nil"
  struct_bytes_loop_nil : ∀ [Params] (ser : Serializer) ta pad o acc,
    struct_bytes_loop ser ta pad [] [] o acc =
    let (o', acc') := accumulate_padding o pad acc
    raise_ret (accumulate_padding o' ta acc')
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|struct_bytes_loop_cons"
  struct_bytes_loop_cons : ∀ [Params] (ser : Serializer) ta pad f fs t ts o acc,
    struct_bytes_loop ser ta pad (f :: fs) (t :: ts) o acc = (do
      let (o₁, a₁) := accumulate_padding o (pad.map fun _ ↦ (dtyp_alignment t).preferred_alignment) acc
      let (coff, a₂) ← ser t f 0 none a₁
      let (o₂, a₃) := accumulate_padding_bytes (o₁ + coff) (alloc_size_dtyp t - store_size_dtyp t) a₂
      struct_bytes_loop ser ta pad fs ts o₂ a₃)
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|array_bytes_loop_nil"
  array_bytes_loop_nil : ∀ [Params] (ser : Serializer) ta t ep o acc,
    array_bytes_loop ser ta t ep [] o acc = raise_ret (accumulate_padding o ta acc)
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|array_bytes_loop_cons"
  array_bytes_loop_cons : ∀ [Params] (ser : Serializer) ta t ep e es o acc,
    array_bytes_loop ser ta t ep (e :: es) o acc = (do
      let (coff, bs) ← ser t e 0 none acc
      let (o', bs') := accumulate_padding_bytes (o + coff) ep bs
      array_bytes_loop ser ta t ep es o' bs')
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|ser_spec"
  ser_spec : ∀ [Params], dvalue → Prop
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|struct_bytes_loop_spec"
  struct_bytes_loop_spec : ∀ [Params] {fs ts}, List.Forall₂ dvalue_has_dtyp fs ts → List.Forall ser_spec fs →
    ∀ pad ta offset acc {offset' bs},
    struct_bytes_loop acc_dvalue_to_memory_bytes_h ta pad fs ts offset acc = raise_ret (offset', bs) →
    offset' = tapad ta (tapad pad (ts.foldl (sfe_step pad) offset)) ∧
    bs.length = acc.length + (offset' - offset) ∧ offset ≤ offset'
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|array_bytes_loop_spec"
  array_bytes_loop_spec : ∀ [Params] {es t}, List.Forall (fun x ↦ dvalue_has_dtyp x t) es → List.Forall ser_spec es →
    ∀ ta ep offset acc {offset' bs},
    array_bytes_loop acc_dvalue_to_memory_bytes_h ta t ep es offset acc = raise_ret (offset', bs) →
    offset' = tapad ta (offset + es.length * (store_size_dtyp t + ep)) ∧
    bs.length = acc.length + (offset' - offset) ∧ offset ≤ offset'
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|acc_dvalue_to_memory_bytes_h_spec"
  acc_dvalue_to_memory_bytes_h_spec : ∀ [Params] {dv dt}, dvalue_has_dtyp dv dt → ∀ ta acc {o bs},
    acc_dvalue_to_memory_bytes_h dt dv 0 ta acc = raise_ret (o, bs) →
    o = tapad ta (store_size_dtyp dt) ∧ bs.length = acc.length + o
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|dvalue_to_memory_bytes_sizeof"
  dvalue_to_memory_bytes_sizeof : ∀ [Params] {dt dv} ta {bytes}, dvalue_has_dtyp dv dt →
    dvalue_to_memory_bytes dt dv ta = raise_ret bytes → bytes.length = match ta with
      | none => store_size_dtyp dt
      | some a => pad_to a (store_size_dtyp dt)
#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|concat_bytes_Z_mixed_cons2"
  concat_bytes_Z_mixed_cons2 : ∀ [Params] extra b d rest,
    concat_bytes_Z_mixed extra (b :: d :: rest) = (do
      let z ← memory_byte_to_Z b
      let r ← concat_bytes_Z_mixed extra (d :: rest)
      pure (z + 256 * r) : EOUP Int)
