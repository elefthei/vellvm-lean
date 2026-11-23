import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_interp.Intrinsics

open Vellvm.Semantics.DynamicValues Vellvm.Semantics.LLVMEvents
open Vellvm.Semantics.IntrinsicsDefinitions Vellvm.Semantics.Handlers.Intrinsics
open Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Rocqlib
open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_interp

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_pure_base_to_semantic"
  I2F_pure_base_to_semantic : ∀ (f : @pure_base_function PInf) (g : @pure_base_function PFin),
    (∀ xs ys, List.Forall₂ I2F_dvalue_base xs ys →
      I2F_EOU (Sum.LiftRel I2F_dvalue_base I2F_dvalue_base) (f xs) (g ys)) →
    ∀ xs ys va vb, List.Forall₂ I2F_dvalue xs ys → I2F_refine_MCFG I2F_exc_dvalue
      (pure_base_to_semantic (Pa := PInf) f xs va) (pure_base_to_semantic (Pa := PFin) g ys vb)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_llvm_fabs"
  I2F_llvm_fabs : ∀ xs ys, List.Forall₂ I2F_dvalue_base xs ys →
    I2F_EOU (Sum.LiftRel I2F_dvalue_base I2F_dvalue_base) (@llvm_fabs PInf xs) (@llvm_fabs PFin ys)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_llvm_maxnum"
  I2F_llvm_maxnum : ∀ xs ys, List.Forall₂ I2F_dvalue_base xs ys →
    I2F_EOU (Sum.LiftRel I2F_dvalue_base I2F_dvalue_base)
      (@llvm_maxnum PInf xs) (@llvm_maxnum PFin ys)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_llvm_minimum"
  I2F_llvm_minimum : ∀ xs ys, List.Forall₂ I2F_dvalue_base xs ys →
    I2F_EOU (Sum.LiftRel I2F_dvalue_base I2F_dvalue_base)
      (@llvm_minimum PInf xs) (@llvm_minimum PFin ys)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_llvm_assume"
  I2F_llvm_assume : ∀ xs ys, List.Forall₂ I2F_dvalue_base xs ys →
    I2F_EOU (Sum.LiftRel I2F_dvalue_base I2F_dvalue_base)
      (@llvm_assume PInf xs) (@llvm_assume PFin ys)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_llvm_vellvm_internal_throw"
  I2F_llvm_vellvm_internal_throw : ∀ xs ys, List.Forall₂ I2F_dvalue_base xs ys →
    I2F_EOU (Sum.LiftRel I2F_dvalue_base I2F_dvalue_base)
      (@llvm_vellvm_internal_throw PInf xs) (@llvm_vellvm_internal_throw PFin ys)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_dvalue_to_ival"
  I2F_dvalue_to_ival : ∀ x y, I2F_dvalue x y → @dvalue_to_ival PInf x = @dvalue_to_ival PFin y

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_dvalues_to_ivals"
  I2F_dvalues_to_ivals : ∀ xs ys, List.Forall₂ I2F_dvalue xs ys →
    @dvalues_to_ivals PInf xs = @dvalues_to_ivals PFin ys

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_llvm_int_intrinsic"
  I2F_llvm_int_intrinsic : ∀ (f : int_intrinsic) (t : dtyp) xs ys va vb,
    List.Forall₂ I2F_dvalue xs ys → I2F_refine_MCFG I2F_exc_dvalue
      (pure_to_semantic (Pa := PInf) (@llvm_int_intrinsic PInf f t) xs va)
      (pure_to_semantic (Pa := PFin) (@llvm_int_intrinsic PFin f t) ys vb)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_llvm_va_start"
  I2F_llvm_va_start : ∀ xs ys va vb, List.Forall₂ I2F_dvalue xs ys → option_rel I2F_Addr va vb →
    I2F_refine_MCFG I2F_exc_dvalue (llvm_va_start (Pa := PInf) xs va)
      (llvm_va_start (Pa := PFin) ys vb)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_llvm_va_copy"
  I2F_llvm_va_copy : ∀ xs ys va vb, List.Forall₂ I2F_dvalue xs ys →
    I2F_refine_MCFG I2F_exc_dvalue (llvm_va_copy (Pa := PInf) xs va)
      (llvm_va_copy (Pa := PFin) ys vb)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_llvm_va_end"
  I2F_llvm_va_end : ∀ xs ys va vb, I2F_refine_MCFG I2F_exc_dvalue
    (llvm_va_end (Pa := PInf) xs va) (llvm_va_end (Pa := PFin) ys vb)

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_handle_intrinsics"
  I2F_handle_intrinsics : ∀ (e : @IntrinsicRequest PInf) (f : @IntrinsicRequest PFin),
    I2FE_Intrinsic e f → I2F_refine_MCFG (fun x y ↦ I2FA_Intrinsic e x f y)
      (handle_intrinsics (Pa := PInf) e) (handle_intrinsics (Pa := PFin) f)
