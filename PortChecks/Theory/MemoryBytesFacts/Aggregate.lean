import PortChecks.SourceType
import Vellvm.Theory.MemoryBytesFacts.Aggregate

open Vellvm Vellvm.Syntax.DynamicTypes Vellvm.Semantics.Interfaces.Params
open Vellvm.Semantics.Interfaces.Sizeof Vellvm.Semantics.DynamicValues Vellvm.Semantics.EOU
open Vellvm.Utils.ListUtil Vellvm.Semantics.MemoryBytes Vellvm.Theory.MemoryBytesFacts

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|poison_block_shape"
  poison_block_shape : ∀ [Pa : Params] (n : Nat) (ta : Option Nat) (acc : List memory_byte),
    (let (o, bs) := accumulate_padding_bytes 0 n acc
     pure (accumulate_padding o ta bs) : EOU (Nat × List memory_byte)) =
    raise_ret (tapad ta n, List.replicate (tapad ta n) poison_memory_byte ++ acc)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|ser_poison_agg"
  ser_poison_agg : ∀ [Pa : Params] (dt : dtyp) (ta : Option Nat) (acc : List memory_byte),
    (match dt with | .DTYPE_Base _ => False | _ => True) →
    acc_dvalue_to_memory_bytes_h dt (DVALUE_Base DVALUE_Poison) 0 ta acc =
      raise_ret (tapad ta (store_size_dtyp dt),
        List.replicate (tapad ta (store_size_dtyp dt)) poison_memory_byte ++ acc)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|poison_split_app_live"
  poison_split_app_live : ∀ [Pa : Params] (w extra : List memory_byte),
    (poison_split w).2 ≠ [] → poison_split (w ++ extra) =
      ((poison_split w).1, (poison_split w).2 ++ extra)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|poison_split_app_poison"
  poison_split_app_poison : ∀ [Pa : Params] (w extra : List memory_byte),
    (poison_split w).2 = [] → poison_split (w ++ extra) =
      ((poison_split w).1 + (poison_split extra).1, (poison_split extra).2)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_base_trailing"
  read_base_trailing : ∀ [Pa : Params] (dtb : dtyp_base) (w extra : List memory_byte),
    store_size_dtyp (DTYPE_Base dtb) ≤ w.length →
    memory_bytes_to_dvalue (w ++ extra) (DTYPE_Base dtb) = memory_bytes_to_dvalue w (DTYPE_Base dtb)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_struct_loop"
  read_struct_loop : ∀ [Pa : Params], (List memory_byte → dtyp → EOU dvalue) → Nat →
    Option Nat → Nat → List dtyp → List memory_byte → EOU (List dvalue)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_struct_unfold"
  read_struct_unfold : ∀ [Pa : Params] (packed : Bool) (dts : List dtyp) (dbs : List memory_byte),
    memory_bytes_to_dvalue dbs (DTYPE_Struct packed dts) =
      (let (np, rest) := poison_split dbs
       match rest with
       | [] => pure (poison_of_dtyp (DTYPE_Struct packed dts))
       | _ :: _ => canonicalize_agg (DTYPE_Struct packed dts) <$>
           read_struct_loop memory_bytes_to_dvalue np
             (if packed then none else some (max_preferred_dtyp_alignment dts)) 0 dts dbs)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|poison_split_prefix"
  poison_split_prefix : ∀ [Pa : Params] (l : List memory_byte),
    (take (poison_split l).1 l).all is_all_poison_byte = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|forallb_head_false"
  forallb_head_false : ∀ [Pa : Params] (b : memory_byte) (l : List memory_byte),
    is_all_poison_byte b = false → (b :: l).all is_all_poison_byte = false

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|base_block_not_all_poison"
  base_block_not_all_poison : ∀ [Pa : Params] (dtb : dtyp_base) {dv : dvalue_base},
    serializable_base dtb → dvalue_base_has_dtyp_base dv dtb = true →
    dvalue_base_canonical dv = true → dv ≠ DVALUE_Poison →
    ((Nseq 0 (store_size_dtyp (DTYPE_Base dtb))).map (base_byte_gen dv)).all is_all_poison_byte = false

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|rt_spec"
  rt_spec : ∀ [Pa : Params], dvalue → Prop

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_array_loop"
  read_array_loop : ∀ [Pa : Params], (List memory_byte → dtyp → EOU dvalue) → Nat → Nat → dtyp →
    Nat → Nat → List memory_byte → EOU (List dvalue)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|packed_vector_elts"
  packed_vector_elts : ∀ [Pa : Params], dtyp_base → Positive → Nat → List memory_byte → List dvalue

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_array_unfold"
  read_array_unfold : ∀ [Pa : Params] (vec : Bool) (sz : Nat) (t : dtyp) (dbs : List memory_byte),
    memory_bytes_to_dvalue dbs (DTYPE_Array vec sz t) =
      (let (np, rest) := poison_split dbs
       match rest with
       | [] => pure (poison_of_dtyp (DTYPE_Array vec sz t))
       | _ :: _ => match packed_vector_type (DTYPE_Array vec sz t) with
         | some (tb, m) => pure (canonicalize_agg (DTYPE_Array vec sz t) (packed_vector_elts tb m sz dbs))
         | none => do
           let elts ← read_array_loop memory_bytes_to_dvalue np
             (if vec then store_size_dtyp t else alloc_size_dtyp t) t sz 0 dbs
           pure (canonicalize_agg (DTYPE_Array vec sz t) elts))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_array_loop_cons"
  read_array_loop_cons : ∀ [Pa : Params] (rd : List memory_byte → dtyp → EOU dvalue)
    (np stride : Nat) (t : dtyp) (n offset : Nat) (dbs : List memory_byte),
    read_array_loop rd np stride t (n + 1) offset dbs =
      ((if offset + store_size_dtyp t ≤ np then pure (poison_of_dtyp t)
        else rd (take (store_size_dtyp t) dbs) t) >>= fun e ↦
       read_array_loop rd np stride t n (offset + stride) (drop stride dbs) >>= fun rest ↦
       pure (e :: rest))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|accumulate_padding_shape"
  accumulate_padding_shape : ∀ [Pa : Params] (offset : Nat) (q : Option Nat) (acc : List memory_byte),
    accumulate_padding offset q acc =
      (tapad q offset, List.replicate (tapad q offset - offset) poison_memory_byte ++ acc)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|accumulate_padding_bytes_shape"
  accumulate_padding_bytes_shape : ∀ [Pa : Params] (offset n : Nat) (acc : List memory_byte),
    accumulate_padding_bytes offset n acc = (offset + n, List.replicate n poison_memory_byte ++ acc)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|forallb_poison_repeat"
  forallb_poison_repeat : ∀ [Pa : Params] (k : Nat), (List.replicate k poison_memory_byte).all is_all_poison_byte = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|forallb_sub"
  forallb_sub : ∀ [Pa : Params] (l : List memory_byte) {n : Nat} (i m : Nat), i + m ≤ n →
    (take n l).all is_all_poison_byte = true → (take m (drop i l)).all is_all_poison_byte = true

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|read_struct_loop_cons"
  read_struct_loop_cons : ∀ [Pa : Params] (rd : List memory_byte → dtyp → EOU dvalue)
    (np : Nat) (pad : Option Nat) (offset : Nat) (dt : dtyp) (dts : List dtyp) (dbs : List memory_byte),
    read_struct_loop rd np pad offset (dt :: dts) dbs =
      (let padding := if pad.isSome then pad_amount (preferred_alignment (dtyp_alignment dt)) offset else 0
       let dbs' := drop padding dbs
       let start := offset + padding
       (if start + store_size_dtyp dt ≤ np then pure (poison_of_dtyp dt)
        else rd (take (store_size_dtyp dt) dbs') dt) >>= fun f ↦
       read_struct_loop rd np pad (start + alloc_size_dtyp dt) dts (drop (alloc_size_dtyp dt) dbs') >>=
         fun rest ↦ pure (f :: rest))

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|struct_loop_read"
  struct_loop_read : ∀ [Pa : Params] {fields : List dvalue} {dts : List dtyp},
    List.Forall₂ dvalue_has_dtyp fields dts → List.Forall rt_spec fields → FORALL serializable dts →
    ∀ (ta pad : Option Nat) (offset : Nat) (acc : List memory_byte) {offset' : Nat} {bs : List memory_byte},
      struct_bytes_loop acc_dvalue_to_memory_bytes_h ta pad fields dts offset acc = raise_ret (offset', bs) →
      ∃ w, bs = w ++ acc ∧ w.length = offset' - offset ∧ offset ≤ offset' ∧
        (fields_all_poison dts fields = false → w.reverse.all is_all_poison_byte = false) ∧
        (∀ np extra, (take (np-offset) (w.reverse ++ extra)).all is_all_poison_byte = true →
          read_struct_loop memory_bytes_to_dvalue np pad offset dts (w.reverse ++ extra) = pure fields)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|array_loop_read"
  array_loop_read : ∀ [Pa : Params] {elts : List dvalue} {t : dtyp},
    List.Forall (fun e ↦ dvalue_has_dtyp e t) elts → List.Forall rt_spec elts → serializable t →
    ∀ (ta : Option Nat) (ep offset : Nat) (acc : List memory_byte) {offset' : Nat} {bs : List memory_byte},
      array_bytes_loop acc_dvalue_to_memory_bytes_h ta t ep elts offset acc = raise_ret (offset', bs) →
      ∃ w, bs = w ++ acc ∧ w.length = offset' - offset ∧ offset ≤ offset' ∧
        (dtyp_is_empty t = false → elts.all dvalue_is_poison = false → w.reverse.all is_all_poison_byte = false) ∧
        (∀ np extra, (take (np-offset) (w.reverse ++ extra)).all is_all_poison_byte = true →
          read_array_loop memory_bytes_to_dvalue np (store_size_dtyp t + ep) t elts.length offset
            (w.reverse ++ extra) = pure elts)
