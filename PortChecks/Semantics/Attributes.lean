import PortChecks.SourceType
import Vellvm.Semantics.Attributes

open Vellvm Vellvm.Syntax.LLVMAst Vellvm.Syntax.DynamicTypes
open Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.DynamicValues Vellvm.Semantics.EOU
open Vellvm.Semantics.LLVMEvents Vellvm.Semantics.Attributes
open ITree (Effect)
open CTree (CTree)

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|denote_int_syntax"
  denote_int_syntax : int_syntax → Int

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|explicit_alignment"
  explicit_alignment : List (annotation dtyp) → Option Nat

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|attr_is_nonnull"
  attr_is_nonnull : param_attr → Bool

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|attr_is_noundef"
  attr_is_noundef : param_attr → Bool

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|in_wrapping_range"
  in_wrapping_range : Positive → Int → Int → Int → Bool

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|fp_class_of_bits"
  fp_class_of_bits : Int → Int → Int → Int

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|is_power_of_two"
  is_power_of_two : Int → Bool

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|assert_aligned_to"
  assert_aligned_to : ∀ [Pa : Params], dvalue → Option int_syntax → IRString → EOU Unit

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|assert_alignment"
  assert_alignment : ∀ [Pa : Params], dvalue → List (annotation dtyp) → IRString → EOU Unit

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|value_attr_nonnull"
  value_attr_nonnull : ∀ [Pa : Params], List param_attr → dvalue → dvalue

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|value_attr_align"
  value_attr_align : ∀ [Pa : Params], List param_attr → dvalue → dvalue

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|value_attr_range"
  value_attr_range : ∀ [Pa : Params], List param_attr → dvalue → dvalue

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|fp_class"
  fp_class : ∀ [Pa : Params], dvalue_base → Option Int

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|value_nofpclass"
  value_nofpclass : ∀ [Pa : Params], Int → dtyp → dvalue → dvalue

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|value_attr_nofpclass"
  value_attr_nofpclass : ∀ [Pa : Params], List param_attr → dtyp → dvalue → dvalue

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|value_attrs_poison"
  value_attrs_poison : ∀ [Pa : Params], List param_attr → dtyp → dvalue → dvalue

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|apply_value_attrs"
  apply_value_attrs : ∀ [Pa : Params], List param_attr → IRString → dtyp → dvalue → EOU dvalue

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|in_metadata_ranges"
  in_metadata_ranges : Positive → Int → List (int_syntax × int_syntax) → Bool

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|value_metadata_range_base"
  value_metadata_range_base : ∀ [Pa : Params], List (int_syntax × int_syntax) → dvalue → dvalue

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|value_metadata_range"
  value_metadata_range : ∀ [Pa : Params], Option (List (int_syntax × int_syntax)) → dtyp → dvalue → dvalue

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|check_call_result"
  check_call_result : ∀ [Pa : Params], List fn_attr → IRString → List dvalue → (exc ⊕ dvalue) → EOU Unit

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|check_cconv"
  check_cconv : cconv → cconv → IRString → EOU Unit

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|check_callee"
  check_callee : ∀ [Pa : Params], dvalue → EOU Unit

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|bundle_uint"
  bundle_uint : ∀ [Pa : Params], dvalue → Option Int

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|bundle_sint"
  bundle_sint : ∀ [Pa : Params], dvalue → Option Int

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|is_llvm_assume"
  is_llvm_assume : exp dtyp → Bool

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|assert_dereferenceable"
  assert_dereferenceable : ∀ [Pa : Params] {E B : Effect} [FailureE -< E] [UBE -< E] [MemoryE -< E],
    Bool → Nat → dvalue → IRString → CTree E B Unit

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|assert_attrs_dereferenceable"
  assert_attrs_dereferenceable : ∀ [Pa : Params] {E B : Effect} [FailureE -< E] [UBE -< E] [MemoryE -< E],
    List param_attr → dvalue → IRString → CTree E B Unit

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|assert_load_dereferenceable"
  assert_load_dereferenceable : ∀ [Pa : Params] {E B : Effect} [FailureE -< E] [UBE -< E] [MemoryE -< E],
    List (metadata dtyp) → dvalue → IRString → CTree E B Unit

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|apply_attrs"
  apply_attrs : ∀ [Pa : Params] {E B : Effect} [FailureE -< E] [UBE -< E] [OOME -< E] [MemoryE -< E],
    List param_attr → IRString → dtyp → dvalue → CTree E B dvalue

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|apply_args_attrs"
  apply_args_attrs : ∀ [Pa : Params] {E B : Effect} [FailureE -< E] [UBE -< E] [OOME -< E] [MemoryE -< E],
    List (List param_attr) → IRString → List (dtyp × dvalue) → CTree E B (List (dtyp × dvalue))

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|check_call_return"
  check_call_return : ∀ [Pa : Params] {E B : Effect} [FailureE -< E] [UBE -< E] [OOME -< E] [MemoryE -< E],
    List fn_attr → List param_attr → Option (List (int_syntax × int_syntax)) → IRString → dtyp → List dvalue → (exc ⊕ dvalue) → CTree E B (exc ⊕ dvalue)

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|assume_bundle_check"
  assume_bundle_check : ∀ [Pa : Params] {E B : Effect.{0}}, Type

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|assume_violated"
  assume_violated : ∀ {E B : Effect} [UBE -< E] {A : Type},
    IRString → IRString → CTree E B A

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|assume_malformed"
  assume_malformed : ∀ {E B : Effect} [FailureE -< E] {A : Type},
    IRString → IRString → CTree E B A

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|assume_nonnull"
  assume_nonnull : ∀ [Pa : Params] {E B : Effect} [FailureE -< E] [UBE -< E],
    @assume_bundle_check Pa E B

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|assume_noundef"
  assume_noundef : ∀ [Pa : Params] {E B : Effect} [FailureE -< E] [UBE -< E],
    @assume_bundle_check Pa E B

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|assume_align"
  assume_align : ∀ [Pa : Params] {E B : Effect} [FailureE -< E] [UBE -< E],
    @assume_bundle_check Pa E B

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|assume_dereferenceable"
  assume_dereferenceable : ∀ [Pa : Params] {E B : Effect} [FailureE -< E] [UBE -< E] [MemoryE -< E],
    Bool → @assume_bundle_check Pa E B

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|assume_bundle_checks"
  assume_bundle_checks : ∀ [Pa : Params] {E B : Effect} [FailureE -< E] [UBE -< E] [MemoryE -< E],
    List (IRString × @assume_bundle_check Pa E B)

#source_check "src/rocq/Semantics/Attributes.v|Vellvm.Semantics.Attributes|bundle_check"
  bundle_check : ∀ [Pa : Params] {E B : Effect} [FailureE -< E] [UBE -< E] [MemoryE -< E],
    exp dtyp → IRString → Option (@assume_bundle_check Pa E B)

example : in_wrapping_range ⟨3, by decide⟩ (-1) 6 2 = true := rfl
example : in_wrapping_range ⟨3, by decide⟩ 0 0 8 = false := rfl
example : fp_class_of_bits 8 23 0x80000000 = 32 := by decide
example : fp_class_of_bits 8 23 0x7f800001 = 1 := by decide
example : fp_class_of_bits 8 23 0x7fc00001 = 2 := by decide

-- A two-operand alignment bundle has the right arity; a non-pointer violates its guarantee.
example [Pa : Params] {E B : Effect} [FailureE -< E] [UBE -< E] (loc : IRString) :
    assume_align (E := E) (B := B) loc [DVALUE_Base DVALUE_None, DVALUE_Base DVALUE_None] =
      assume_violated loc "align".toUTF8 := rfl

-- A poison pointer still raises UB when zero bytes are requested.
example [Pa : Params] {E B : Effect} [FailureE -< E] [UBE -< E] [MemoryE -< E] (loc : IRString) :
    assert_dereferenceable (E := E) (B := B) true 0 (DVALUE_Base DVALUE_Poison) loc =
      raiseUB loc := rfl
