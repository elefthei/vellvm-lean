import PortChecks.SourceType
import Vellvm.Semantics.MemoryBytes

open Vellvm Vellvm.Syntax.DynamicTypes Vellvm.Semantics.DynamicValues Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.Interfaces.Params

#source_check "src/rocq/Semantics/MemoryBytes.v|Vellvm.Semantics.MemoryBytes|memory_byte"
  memory_byte : ∀ [Pa : Params], Type
#source_check "src/rocq/Semantics/MemoryBytes.v|Vellvm.Semantics.MemoryBytes|memory_byte_of_dvalue_bv"
  memory_byte_of_dvalue_bv : ∀ [Pa : Params] {sz : Positive}, dvalue_bv sz → Nat → memory_byte
#source_check "src/rocq/Semantics/MemoryBytes.v|Vellvm.Semantics.MemoryBytes|dvalue_to_memory_bytes"
  dvalue_to_memory_bytes : ∀ [Pa : Params], dtyp → dvalue → Option Nat → EOU (List memory_byte)
#source_check "src/rocq/Semantics/MemoryBytes.v|Vellvm.Semantics.MemoryBytes|memory_bytes_to_dvalue"
  memory_bytes_to_dvalue : ∀ [Pa : Params], List memory_byte → dtyp → EOU dvalue
