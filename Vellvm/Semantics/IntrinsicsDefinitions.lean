module

public import Vellvm.Semantics.IntrinsicsDefinitions.Pure
public import Vellvm.Semantics.LLVMEvents

@[expose] public section
namespace Vellvm.Semantics.IntrinsicsDefinitions
open ITree (Effect Subeffect)
open CTree (CTree)
open Tree Interfaces.Params DynamicValues Syntax.DynamicTypes LLVMEvents

namespace Worker
variable {M : Effect → Effect → Type → Type v} [Runtime M] [Instrumentation.Diagnostics M]
variable [Pa : Params] {E B : Effect}

abbrev semantic_function (M : Effect → Effect → Type → Type v) (E B : Effect) :=
  List dvalue → Option Pa.PTR.ptr → M E B (dvalue ⊕ dvalue)

def llvm_va_start [MemoryE -< E] [UBE -< E] [FailureE -< E] : semantic_function M E B
  | [a], some va => do
    match a with
    | .DVALUE_Base .DVALUE_Poison =>
      LLVMEvents.Worker.raiseUB "Store to poisoned address in va_start.".toUTF8
    | _ =>
      LLVMEvents.Worker.store (.DTYPE_Base .DTYPE_Pointer) a (.DVALUE_Base (.DVALUE_Pointer va))
      pure (.inr (.DVALUE_Base .DVALUE_None))
  | _, _ => LLVMEvents.Worker.«raise» "va_start: invalid arguments.".toUTF8

def llvm_va_copy [MemoryE -< E] [FailureE -< E] : semantic_function M E B
  | [dest, src], _ => do
    let v ← LLVMEvents.Worker.load (.DTYPE_Base .DTYPE_Pointer) src
    LLVMEvents.Worker.store (.DTYPE_Base .DTYPE_Pointer) dest v
    pure (.inr (.DVALUE_Base .DVALUE_None))
  | _, _ => LLVMEvents.Worker.«raise» ": va_copy invalid arguments".toUTF8

def llvm_va_end : semantic_function M E B := fun _ _ ↦ pure (.inr (.DVALUE_Base .DVALUE_None))

variable [FailureE -< E] [UBE -< E] [OOME -< E]

def pure_to_semantic (f : pure_function) : semantic_function M E B :=
  fun args _ ↦ LLVMEvents.Worker.EOU_to_itree (f args)

def pure_base_to_semantic (f : pure_base_function) : semantic_function M E B :=
  pure_to_semantic (pure_base_to_pure f)

variable [MemoryE -< E]

def intrinsic_semantics (t : dtyp) : intrinsic_family → Option (semantic_function M E B)
  | .Intr_int f => some (pure_to_semantic (llvm_int_intrinsic f t))
  | .Intr_fabs => some (pure_base_to_semantic llvm_fabs)
  | .Intr_maxnum => some (pure_base_to_semantic llvm_maxnum)
  | .Intr_minimum => some (pure_base_to_semantic llvm_minimum)
  | .Intr_throw => some (pure_base_to_semantic llvm_vellvm_internal_throw)
  | .Intr_assume => some (pure_base_to_semantic llvm_assume)
  | .Intr_va_start => some llvm_va_start
  | .Intr_va_end => some llvm_va_end
  | .Intr_va_copy => some llvm_va_copy
  | .Intr_memcpy | .Intr_memmove | .Intr_memset | .Intr_malloc | .Intr_free => none

def named_intrinsic_semantics (t : dtyp) (name : IRString) : Option (semantic_function M E B) :=
  (lookup_intrinsic name).bind (intrinsic_semantics t)

end Worker

variable [Pa : Params] {E B : Effect}

abbrev semantic_function (E B : Effect) := Worker.semantic_function CTree E B

def llvm_va_start [FailureE -< E] [UBE -< E] [MemoryE -< E] : semantic_function E B :=
  Worker.llvm_va_start

def llvm_va_copy [FailureE -< E] [MemoryE -< E] : semantic_function E B := Worker.llvm_va_copy

def llvm_va_end : semantic_function E B := Worker.llvm_va_end

variable [FailureE -< E] [UBE -< E] [OOME -< E]

def pure_to_semantic (f : pure_function) : semantic_function E B := Worker.pure_to_semantic f

def pure_base_to_semantic (f : pure_base_function) : semantic_function E B :=
  Worker.pure_base_to_semantic f

variable [MemoryE -< E]

def intrinsic_semantics (t : dtyp) (fam : intrinsic_family) : Option (semantic_function E B) :=
  Worker.intrinsic_semantics t fam

def named_intrinsic_semantics (t : dtyp) (name : IRString) : Option (semantic_function E B) :=
  Worker.named_intrinsic_semantics t name

end Vellvm.Semantics.IntrinsicsDefinitions
