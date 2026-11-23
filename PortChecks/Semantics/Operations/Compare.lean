import PortChecks.SourceType
import Vellvm.Semantics.Operations.Compare

open Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.DynamicValues Vellvm.Semantics.EOU
open Vellvm.Syntax.DynamicTypes Vellvm.Syntax.LLVMAst Vellvm.Semantics.Operations.Compare

#source_check "src/rocq/Semantics/Operations/Compare.v|Vellvm.Semantics.Operations.Compare|is_icmp_operand"
  is_icmp_operand : ∀ [Pa : Params], dvalue_base → Bool
#source_check "src/rocq/Semantics/Operations/Compare.v|Vellvm.Semantics.Operations.Compare|eval_icmp_int_base"
  eval_icmp_int_base : ∀ [Pa : Params], Bool → icmp → dvalue_base → dvalue_base → EOU dvalue_base
#source_check "src/rocq/Semantics/Operations/Compare.v|Vellvm.Semantics.Operations.Compare|ptr_to_addr"
  ptr_to_addr : ∀ [Pa : Params], Pa.PTR.ptr → EOU dvalue_base
#source_check "src/rocq/Semantics/Operations/Compare.v|Vellvm.Semantics.Operations.Compare|eval_icmp_base"
  eval_icmp_base : ∀ [Pa : Params], Bool → icmp → dvalue_base → dvalue_base → EOU dvalue_base
#source_check "src/rocq/Semantics/Operations/Compare.v|Vellvm.Semantics.Operations.Compare|eval_icmp"
  eval_icmp : ∀ [Pa : Params], Bool → icmp → dtyp → dvalue → dvalue → EOU dvalue

variable [Pa : Params]

-- In i3, 4 has its sign bit set, so even equality is poison under samesign.
example : eval_icmp_int_base true .Eq (DVALUE_I ⟨3, by decide⟩ (Vellvm.Numeric.Integers.repr 4))
    (DVALUE_I ⟨3, by decide⟩ Vellvm.Numeric.Integers.zero) = raise_ret DVALUE_Poison := rfl

example : eval_icmp false .Eq (DTYPE_Array true 1 DTYPE_Pointer)
    (DVALUE_Base DVALUE_Poison) (DVALUE_Array true []) =
    raise_ub "icmp of different-length vectors".toUTF8 := rfl

example (a : Pa.PTR.ptr) (h : Pa.SIZE.bit_sizeof_dtyp (DTYPE_Base DTYPE_Pointer) = 3) :
    ptr_to_addr a = raise_ret (DVALUE_I ⟨3, by decide⟩
      (Vellvm.Numeric.Integers.repr (Pa.P2I.ptr_to_int a))) := by
  simp only [ptr_to_addr, h] <;> rfl
