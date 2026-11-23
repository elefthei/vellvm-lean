import Vellvm.Semantics.Attributes.Values

namespace Vellvm.Semantics.Attributes
open ITree (Effect)
open Tree LLVMEvents Interfaces.Params DynamicValues Syntax.DynamicTypes Syntax.LLVMAst

namespace Worker
variable {M : Effect → Effect → Type → Type v} [Runtime M] [Instrumentation.Diagnostics M]
variable [Pa : Params] {E B : Effect} [FailureE -< E] [UBE -< E] [OOME -< E] [MemoryE -< E]

def assert_dereferenceable (or_null : Bool) (n : Nat) (v : dvalue) (msg : IRString) : M E B Unit :=
  match v with
  | DVALUE_Base (DVALUE_Pointer p) =>
    if (or_null && Pa.P2I.ptr_to_int p == Pa.P2I.ptr_to_int Pa.PTR.null) || n == 0 then pure ()
    else LLVMEvents.Worker.load (DTYPE_Array false n (DTYPE_B ⟨8, by decide⟩)) v >>= fun _ ↦ pure ()
  | DVALUE_Base DVALUE_Poison => LLVMEvents.Worker.raiseUB msg
  | _ => LLVMEvents.Worker.«raise» (msg ++ " (not a pointer)".toUTF8)

def assert_attrs_dereferenceable (attrs : List param_attr) (v : dvalue) (msg : IRString) : M E B Unit :=
  match attrs.findSome? attr_dereferenceable, v with
  | some (or_null, n), DVALUE_Base (DVALUE_Pointer _) =>
    assert_dereferenceable or_null (denote_int_syntax n).toNat v msg
  | _, _ => pure ()

def assert_load_dereferenceable (md : List (metadata dtyp)) (v : dvalue) (msg : IRString) : M E B Unit :=
  match load_metadata_dereferenceable md with
  | some (or_null, n) => assert_dereferenceable or_null (denote_int_syntax n).toNat v msg
  | none => pure ()

def apply_attrs (attrs : List param_attr) (msg : IRString) (dt : dtyp) (v : dvalue) : M E B dvalue :=
  LLVMEvents.Worker.EOU_to_itree (apply_value_attrs attrs msg dt v) >>= fun v' ↦
    assert_attrs_dereferenceable attrs v' msg >>= fun _ ↦ pure v'

def apply_args_attrs (attrss : List (List param_attr)) (msg : IRString) :
    List (dtyp × dvalue) → M E B (List (dtyp × dvalue))
  | [] => pure []
  | (t, v) :: vs => do
    let v' ← apply_attrs (attrss.headD []) msg t v
    let vs' ← apply_args_attrs attrss.tail msg vs
    pure ((t, v') :: vs')

def check_call_return (fattrs : List fn_attr) (ret_attrs : List param_attr)
    (ranges : Option (List (int_syntax × int_syntax))) (loc : IRString) (ret_t : dtyp)
    (args : List dvalue) (res : exc ⊕ dvalue) : M E B (exc ⊕ dvalue) :=
  LLVMEvents.Worker.EOU_to_itree (check_call_result fattrs loc args res) >>= fun _ ↦
    match res with
    | .inl _ => pure res
    | .inr v => do
      let v' ← apply_attrs ret_attrs (loc ++ " return value violates noundef.".toUTF8)
        ret_t (value_metadata_range ranges ret_t v)
      pure (.inr v')

abbrev assume_bundle_check := IRString → List dvalue → M E B Unit

private def violation (loc tag : IRString) : IRString :=
  loc ++ ": llvm.assume operand bundle \"".toUTF8 ++ tag ++ "\" is violated.".toUTF8

def assume_violated {A : Type} (loc tag : IRString) : M E B A :=
  LLVMEvents.Worker.raiseUB (violation loc tag)

def assume_malformed {A : Type} (loc tag : IRString) : M E B A :=
  LLVMEvents.Worker.«raise» (loc ++ ": malformed llvm.assume operand bundle \"".toUTF8 ++ tag ++ "\".".toUTF8)

def assume_nonnull : assume_bundle_check (M := M) (E := E) (B := B) := fun loc vs ↦
  match vs with
  | [p] =>
    match dvalue_ptr_address p with
    | some a => if a == 0 then assume_violated loc "nonnull".toUTF8 else pure ()
    | none => assume_violated loc "nonnull".toUTF8
  | _ => assume_malformed loc "nonnull".toUTF8

def assume_noundef : assume_bundle_check (M := M) (E := E) (B := B) := fun loc vs ↦
  match vs with
  | [v] => if dvalue_well_defined v then pure () else assume_violated loc "noundef".toUTF8
  | _ => assume_malformed loc "noundef".toUTF8

def assume_align : assume_bundle_check (M := M) (E := E) (B := B) := fun loc vs ↦
  match vs with
  | p :: al :: off =>
    let offset := match off with
      | [] => some 0
      | [o] => bundle_sint o
      | _ => none
    match dvalue_ptr_address p, bundle_uint al, offset with
    | some a, some n, some o =>
      if (if is_power_of_two n then (a - o) % n == 0 else a == 0) then pure ()
      else assume_violated loc "align".toUTF8
    | _, _, _ => assume_violated loc "align".toUTF8
  | _ => assume_malformed loc "align".toUTF8

def assume_dereferenceable (or_null : Bool) : assume_bundle_check (M := M) (E := E) (B := B) :=
  fun loc vs ↦
    let tag := if or_null then "dereferenceable_or_null".toUTF8 else "dereferenceable".toUTF8
    match vs with
    | [p, sz] =>
      match dvalue_ptr_address p, bundle_uint sz with
      | some _, some n =>
        if n == 0 then pure () else assert_dereferenceable or_null n.toNat p (violation loc tag)
      | _, _ => assume_violated loc tag
    | _ => assume_malformed loc tag

def assume_bundle_checks : List (IRString × assume_bundle_check (M := M) (E := E) (B := B)) :=
  [("nonnull".toUTF8, assume_nonnull), ("noundef".toUTF8, assume_noundef),
   ("align".toUTF8, assume_align), ("dereferenceable".toUTF8, assume_dereferenceable false),
   ("dereferenceable_or_null".toUTF8, assume_dereferenceable true)]

end Worker
end Vellvm.Semantics.Attributes
