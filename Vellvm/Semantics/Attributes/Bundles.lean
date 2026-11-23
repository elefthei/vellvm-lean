import Vellvm.Semantics.Attributes.Memory
import Vellvm.Semantics.IntrinsicsDefinitions.Families

namespace Vellvm.Semantics.Attributes
open ITree (Effect)
open CTree (CTree)
open Tree LLVMEvents Interfaces.Params DynamicValues Syntax.DynamicTypes Syntax.LLVMAst

def is_llvm_assume (f : exp dtyp) : Bool :=
  match IntrinsicsDefinitions.intrinsic_exp f with
  | some s => s == "llvm.assume".toUTF8
  | none => false

namespace Worker
variable {M : Effect → Effect → Type → Type v} [Runtime M] [Instrumentation.Diagnostics M]
variable [Pa : Params] {E B : Effect} [FailureE -< E] [UBE -< E] [MemoryE -< E]

def bundle_check (f : exp dtyp) (tag : IRString) : Option (assume_bundle_check (M := M) (E := E) (B := B)) :=
  if is_llvm_assume f then ((assume_bundle_checks (M := M) (E := E) (B := B)).find? (fun p ↦ p.1 == tag)).map Prod.snd
  else none

end Worker

variable [Pa : Params] {E B : Effect} [FailureE -< E] [UBE -< E] [OOME -< E] [MemoryE -< E]

def assert_dereferenceable : Bool → Nat → dvalue → IRString → CTree E B Unit :=
  Worker.assert_dereferenceable (M := CTree)

def assert_attrs_dereferenceable : List param_attr → dvalue → IRString → CTree E B Unit :=
  Worker.assert_attrs_dereferenceable (M := CTree)

def assert_load_dereferenceable : List (metadata dtyp) → dvalue → IRString → CTree E B Unit :=
  Worker.assert_load_dereferenceable (M := CTree)

def apply_attrs : List param_attr → IRString → dtyp → dvalue → CTree E B dvalue :=
  Worker.apply_attrs (M := CTree)

def apply_args_attrs : List (List param_attr) → IRString → List (dtyp × dvalue) → CTree E B (List (dtyp × dvalue)) :=
  Worker.apply_args_attrs (M := CTree)

def check_call_return : List fn_attr → List param_attr → Option (List (int_syntax × int_syntax)) → IRString → dtyp → List dvalue → (exc ⊕ dvalue) → CTree E B (exc ⊕ dvalue) :=
  Worker.check_call_return (M := CTree)

abbrev assume_bundle_check := Worker.assume_bundle_check (M := CTree) (Pa := Pa) (E := E) (B := B)

def assume_violated {A : Type} : IRString → IRString → CTree E B A :=
  Worker.assume_violated (M := CTree)

def assume_malformed {A : Type} : IRString → IRString → CTree E B A :=
  Worker.assume_malformed (M := CTree)

def assume_nonnull : assume_bundle_check (E := E) (B := B) :=
  Worker.assume_nonnull (M := CTree)

def assume_noundef : assume_bundle_check (E := E) (B := B) :=
  Worker.assume_noundef (M := CTree)

def assume_align : assume_bundle_check (E := E) (B := B) :=
  Worker.assume_align (M := CTree)

def assume_dereferenceable : Bool → assume_bundle_check (E := E) (B := B) :=
  Worker.assume_dereferenceable (M := CTree)

def assume_bundle_checks : List (IRString × assume_bundle_check (E := E) (B := B)) :=
  Worker.assume_bundle_checks (M := CTree)

def bundle_check : exp dtyp → IRString → Option (assume_bundle_check (E := E) (B := B)) :=
  Worker.bundle_check (M := CTree)

end Vellvm.Semantics.Attributes
