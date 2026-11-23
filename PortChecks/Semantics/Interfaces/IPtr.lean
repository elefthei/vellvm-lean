import PortChecks.SourceType
import Vellvm.Semantics.Interfaces.IPtr

open Vellvm.Semantics.EOU Vellvm.Semantics.Interfaces.IPtr Vellvm.Syntax.DynamicTypes

#source_check "src/rocq/Semantics/Interfaces/IPtr.v|Vellvm.Semantics.Interfaces.IPtr|from_Z_to_Z"
  from_Z_to_Z : ∀ [P : IPtr] [@IPtrTheory P] (z : Int) {i : P.iptr},
    P.from_Z z = raise_ret i → P.to_Z i = z
#source_check "src/rocq/Semantics/Interfaces/IPtr.v|Vellvm.Semantics.Interfaces.IPtr|from_Z_injective"
  from_Z_injective : ∀ [P : IPtr] [@IPtrTheory P] (z₁ z₂ : Int) {i : P.iptr},
    P.from_Z z₁ = raise_ret i → P.from_Z z₂ = raise_ret i → z₁ = z₂
#source_check "src/rocq/Semantics/Interfaces/IPtr.v|Vellvm.Semantics.Interfaces.IPtr|to_Z_from_Z"
  to_Z_from_Z : ∀ [P : IPtr] [@IPtrTheory P] (i : P.iptr), P.from_Z (P.to_Z i) = raise_ret i
#source_check "src/rocq/Semantics/Interfaces/IPtr.v|Vellvm.Semantics.Interfaces.IPtr|from_Z_0"
  from_Z_0 : ∀ [P : IPtr] [@IPtrTheory P], P.from_Z 0 = raise_ret P.zero_iptr
#source_check "src/rocq/Semantics/Interfaces/IPtr.v|Vellvm.Semantics.Interfaces.IPtr|to_Z_0"
  to_Z_0 : ∀ [P : IPtr] [@IPtrTheory P], P.to_Z P.zero_iptr = 0
#source_check "src/rocq/Semantics/Interfaces/IPtr.v|Vellvm.Semantics.Interfaces.IPtr|to_Z_inj"
  to_Z_inj : ∀ [P : IPtr] [@IPtrTheory P] (x y : P.iptr), P.to_Z x = P.to_Z y → x = y
#source_check "src/rocq/Semantics/Interfaces/IPtr.v|Vellvm.Semantics.Interfaces.IPtr|VMemInt_iptr_dtyp"
  VMemInt_iptr_dtyp : ∀ [P : IPtr] [@IPtrTheory P], P.VMemInt_iptr.mdtyp_of_int = DTYPE_Iptr
#source_check "src/rocq/Semantics/Interfaces/IPtr.v|Vellvm.Semantics.Interfaces.IPtr|VMemInt_iptr_mrepr_from_Z"
  VMemInt_iptr_mrepr_from_Z : ∀ [P : IPtr] [@IPtrTheory P] (x : Int),
    P.VMemInt_iptr.mrepr x = P.from_Z x
#source_check "src/rocq/Semantics/Interfaces/IPtr.v|Vellvm.Semantics.Interfaces.IPtr|to_Z_to_unsigned"
  to_Z_to_unsigned : ∀ [P : IPtr] [@IPtrTheory P] (x : P.iptr), P.to_Z x = P.to_unsigned x
