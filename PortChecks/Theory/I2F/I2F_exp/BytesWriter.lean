import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.BytesWriter

open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_accumulate_struct_bytes"
  I2F_accumulate_struct_bytes : ∀ {fs gs}, List.Forall₂ (fun a b ↦ ∀ dt o ta {xs ys}, List.Forall₂ I2F_memory_byte xs ys →
        I2F_EOU I2F_ser_state (@acc_dvalue_to_memory_bytes_h PInf dt a o ta xs) (@acc_dvalue_to_memory_bytes_h PFin dt b o ta ys)) fs gs →
    ∀ ts ta pad o {bs cs}, List.Forall₂ I2F_memory_byte bs cs → I2F_EOU I2F_ser_state
      (@accumulate_struct_bytes PInf ta pad fs ts o bs) (@accumulate_struct_bytes PFin ta pad gs ts o cs)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_accumulate_array_bytes"
  I2F_accumulate_array_bytes : ∀ {es fs}, List.Forall₂ (fun a b ↦ ∀ dt o ta {xs ys}, List.Forall₂ I2F_memory_byte xs ys →
        I2F_EOU I2F_ser_state (@acc_dvalue_to_memory_bytes_h PInf dt a o ta xs) (@acc_dvalue_to_memory_bytes_h PFin dt b o ta ys)) es fs →
    ∀ v t ta o {bs cs}, List.Forall₂ I2F_memory_byte bs cs → I2F_EOU I2F_ser_state
      (@accumulate_array_bytes PInf ta v t es o bs) (@accumulate_array_bytes PFin ta v t fs o cs)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_acc_dvalue_to_memory_bytes_h"
  I2F_acc_dvalue_to_memory_bytes_h : ∀ {a b}, I2F_dvalue a b → (fun a b ↦ ∀ dt o ta {xs ys}, List.Forall₂ I2F_memory_byte xs ys →
        I2F_EOU I2F_ser_state (@acc_dvalue_to_memory_bytes_h PInf dt a o ta xs) (@acc_dvalue_to_memory_bytes_h PFin dt b o ta ys)) a b

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_memory_dvalue_to_memory_bytes"
  I2F_memory_dvalue_to_memory_bytes : ∀ t {a b}, I2F_dvalue a b → ∀ ta, I2F_EOU (List.Forall₂ I2F_memory_byte)
    (@dvalue_to_memory_bytes PInf t a ta) (@dvalue_to_memory_bytes PFin t b ta)
