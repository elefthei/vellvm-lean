import PortChecks.SourceType
import Vellvm.Semantics.Implementations.IPtrInfinite

open Vellvm.Semantics.Interfaces.IPtr Vellvm.Semantics.Implementations.IPtrInfinite

#source_check "src/rocq/Semantics/Implementations/IPtrInfinite.v|Vellvm.Semantics.Implementations.IPtrInfinite|IPZ"
  IPZ : IPtr
#source_check "src/rocq/Semantics/Implementations/IPtrInfinite.v|Vellvm.Semantics.Implementations.IPtrInfinite|IPZTheory"
  IPZTheory : @IPtrTheory IPZ

open Vellvm.Semantics.EOU

example : IPZ.from_Z (2^64) = raise_ret ((2 : Int)^64) := rfl
example : IPZ.VMemInt_iptr.mdivs (7 : Int) (-2 : Int) = raise_ret (-4 : Int) := rfl
example : IPZ.VMemInt_iptr.mmodu (7 : Int) (-2 : Int) = (-1 : Int) := rfl
