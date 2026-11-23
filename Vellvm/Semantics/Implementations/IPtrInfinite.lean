module

public import Vellvm.Semantics.Interfaces.IPtr
public import Vellvm.Utils.StringUtil

@[expose] public section
namespace Vellvm.Semantics.Implementations.IPtrInfinite
open Interfaces.IPtr VellvmIntegers EOU Numeric.Rocqlib

abbrev IPZ : IPtr where
  iptr := Int
  zero_iptr := 0
  VMemInt_iptr := VMemInt_Z
  eq_dec_iptr a b := decideSum (a = b)
  eqb_iptr := (· == ·)
  to_Z := id
  to_unsigned := id
  from_Z := raise_ret
  show_iptr := Utils.StringUtil.show_Z

attribute [local instance] IPZ

instance IPZTheory : @IPtrTheory IPZ where
  from_Z_to_Z _ _ h := (EOU.raise_ret.inj h).symm
  from_Z_injective _ _ _ h₁ h₂ := EOU.raise_ret.inj (h₁.trans h₂.symm)
  to_Z_from_Z _ := rfl
  from_Z_0 := rfl
  to_Z_0 := rfl
  to_Z_inj _ _ h := h
  VMemInt_iptr_dtyp := rfl
  VMemInt_iptr_mrepr_from_Z _ := rfl
  to_Z_to_unsigned _ := rfl

end Vellvm.Semantics.Implementations.IPtrInfinite
