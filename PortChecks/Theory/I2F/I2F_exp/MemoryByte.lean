import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.MemoryByte

open Vellvm.Semantics.MemoryBytes Vellvm.Theory.I2F.Refinement
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_memory_byte"
  I2F_memory_byte : @memory_byte PInf → @memory_byte PFin → Prop
