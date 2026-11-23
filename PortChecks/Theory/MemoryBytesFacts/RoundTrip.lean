import PortChecks.SourceType
import Vellvm.Theory.MemoryBytesFacts.RoundTrip

open Vellvm Vellvm.Semantics Vellvm.Semantics.DynamicValues Vellvm.Syntax.DynamicTypes
open Vellvm.Semantics.EOU Vellvm.Semantics.MemoryBytes Vellvm.Semantics.Interfaces.Sizeof
open Vellvm.Semantics.Interfaces.Params Vellvm.Theory.MemoryBytesFacts

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|round_trip_h"
  Vellvm.Theory.MemoryBytesFacts.round_trip_h : ∀ [Pa : Params] {dv : dvalue} {dt : dtyp},
    dvalue_has_dtyp dv dt → serializable dt → ∀ ta acc {offset' bs},
    acc_dvalue_to_memory_bytes_h dt dv 0 ta acc = raise_ret (offset', bs) →
    ∃ w, bs = w ++ acc ∧ w.length = tapad ta (store_size_dtyp dt) ∧
      memory_bytes_to_dvalue w.reverse dt = raise_ret dv ∧
      (dv ≠ poison_of_dtyp dt → w.reverse.all is_all_poison_byte = false)

#source_check "src/rocq/Theory/MemoryBytesFacts.v|Vellvm.Theory.MemoryBytesFacts|memory_bytes_round_trip1"
  Vellvm.Theory.MemoryBytesFacts.memory_bytes_round_trip1 : ∀ [Pa : Params] {dt : dtyp}
    {dv : dvalue} (ta : Option Nat) {mb : List memory_byte}, serializable dt →
    dvalue_has_dtyp dv dt → dvalue_to_memory_bytes dt dv ta = raise_ret mb →
    memory_bytes_to_dvalue mb dt = raise_ret dv
