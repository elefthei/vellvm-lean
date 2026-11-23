import PortChecks.SourceType
import Vellvm.Semantics.Implementations.IPtrFinite

open Vellvm Vellvm.Numeric.Integers Vellvm.Semantics.VellvmIntegers
open Vellvm.Semantics.Interfaces.IPtr Vellvm.Semantics.Implementations.IPtrFinite

#source_check "src/rocq/Semantics/Implementations/IPtrFinite.v|Vellvm.Semantics.Implementations.IPtrFinite|VMemInt_intptr_ix"
  VMemInt_intptr_ix : ∀ {sz : Positive}, VMemInt (bit_int sz)
#source_check "src/rocq/Semantics/Implementations/IPtrFinite.v|Vellvm.Semantics.Implementations.IPtrFinite|IP64Bit"
  IP64Bit : IPtr
#source_check "src/rocq/Semantics/Implementations/IPtrFinite.v|Vellvm.Semantics.Implementations.IPtrFinite|IP64BitTheory"
  IP64BitTheory : @IPtrTheory IP64Bit

open Vellvm.Semantics.EOU

example : IP64Bit.from_Z (2^64) = raise_oom "IPBit from_Z oom.".toUTF8 := rfl
example : IP64Bit.from_Z (-1) = raise_oom "IPBit from_Z oom.".toUTF8 := rfl
example : (@VMemInt_intptr_ix ⟨8, by decide⟩).mmul (Vellvm.Numeric.Integers.repr 128)
    (Vellvm.Numeric.Integers.repr 2) = raise_ret (Vellvm.Numeric.Integers.repr 0) := rfl
example : (@VMemInt_intptr_ix ⟨65, by decide⟩).mmul (Vellvm.Numeric.Integers.repr (2^64))
    (Vellvm.Numeric.Integers.repr 1) = raise_oom "IPBit multiplication overflow.".toUTF8 := rfl
example : IP64Bit.VMemInt_iptr.mshl (Vellvm.Numeric.Integers.repr 1)
    (Vellvm.Numeric.Integers.repr (-1)) = raise_oom "IP64Bit left shift overflow.".toUTF8 := rfl
example : IP64Bit.VMemInt_iptr.mshl (Vellvm.Numeric.Integers.repr 0)
    (Vellvm.Numeric.Integers.repr (-1)) = raise_ret IP64Bit.zero_iptr := rfl
