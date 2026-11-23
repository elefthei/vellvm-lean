import Vellvm.Theory.I2F.Refinement.Values
import Vellvm.Semantics.MemoryBytes.Basic

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm.Semantics.MemoryBytes Vellvm.Theory.I2F.Refinement

def I2F_memory_byte : @memory_byte PInf → @memory_byte PFin → Prop := I2F_dvalue_bv

end Vellvm.Theory.I2F.I2F_exp
