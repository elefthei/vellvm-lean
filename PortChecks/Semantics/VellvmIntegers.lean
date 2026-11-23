import PortChecks.SourceType
import Vellvm.Semantics.VellvmIntegers

open Vellvm Vellvm.Numeric.Integers Vellvm.Semantics.VellvmIntegers
universe u

#source_check "src/rocq/Semantics/VellvmIntegers.v|Vellvm.Semantics.VellvmIntegers|VMemInt_Z"
  VMemInt_Z : VMemInt Int
#source_check "src/rocq/Semantics/VellvmIntegers.v|Vellvm.Semantics.VellvmIntegers|VInt_Bounded"
  VInt_Bounded : ∀ sz : Positive, VInt (bit_int sz)
#source_check "src/rocq/Semantics/VellvmIntegers.v|Vellvm.Semantics.VellvmIntegers|VIntVMemInt"
  VIntVMemInt : ∀ {I : Type u} [VInt I], VMemInt I
