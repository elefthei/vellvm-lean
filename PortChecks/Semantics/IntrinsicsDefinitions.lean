import Vellvm.Semantics.IntrinsicsDefinitions

namespace PortChecks.IntrinsicsDefinitions
open Vellvm Vellvm.Semantics.IntrinsicsDefinitions Vellvm.Syntax.DynamicTypes

private abbrev i8 : Positive := ⟨8, by decide⟩

example (t : dtyp) : llvm_uadd_with_overflow t [.IV_Int i8 255, .IV_Int i8 1] =
    some (.IR_Overflow i8 256 true) := rfl

example (t : dtyp) : llvm_sshl_sat t [.IV_Int i8 1, .IV_Int i8 8] = some .IR_Poison := rfl

example (t : dtyp) : llvm_smax t [.IV_Int i8 255, .IV_Int i8 0] = some (.IR_Int i8 0) := rfl

example [Vellvm.Semantics.Interfaces.Params.Params] (t : dtyp) :
    named_intrinsic_semantics (E := Vellvm.Semantics.LLVMEvents.MCFGEtop)
      (B := Vellvm.Tree.NoChoice) t "llvm.memmove.p0.p0.i64".toUTF8 = none := rfl

end PortChecks.IntrinsicsDefinitions
