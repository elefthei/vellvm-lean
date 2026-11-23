import Vellvm.Semantics.DynamicValues.Basic

namespace Vellvm.Semantics.Operations.Gep
open Syntax.LLVMAst Syntax.DynamicTypes DynamicValues EOU Interfaces.Params Interfaces.Sizeof
open Numeric.Rocqlib Numeric.Integers

variable [Pa : Params]

/-- A bit-packed vector element that does not occupy whole bytes has no address. -/
def gep_indexable : dtyp → Bool
  | DTYPE_Array true _ ta => bit_sizeof_dtyp ta == 8 * store_size_dtyp ta
  | _ => true

/-- Vector elements are contiguous at store size; array elements include allocation padding. -/
def sequential_stride (vector : Bool) (ta : dtyp) : Nat :=
  if vector then store_size_dtyp ta else alloc_size_dtyp ta

def gep_index_bits : Int := 8 * Int.ofNat pointer_size

def trunc_to_index (k : Int) : Int :=
  let half := two_p (gep_index_bits - 1)
  (k + half) % (2 * half) - half

def gep_index : dvalue → Option Int
  | DVALUE_Base (DVALUE_I sz i) =>
    some (if Int.ofNat sz.val ≤ gep_index_bits then signed i else trunc_to_index (signed i))
  | DVALUE_Base (DVALUE_Iptr i) => some (Pa.IPTR.to_Z i)
  | _ => none

def gep_struct_field (packed : Bool) (ts : List dtyp) (n : Nat) : Option (Nat × dtyp) := do
  let t ← ts[n]?
  let off := struct_fields_extent packed (ts.take n)
  return (if packed then off else pad_to_align (dtyp_alignment t) off, t)

def gep_steps_h (t : dtyp) (vs : List dvalue) : EOUP (List (Int × Int)) :=
  match vs with
  | [] => pure []
  | v :: rest =>
    if !gep_indexable t then
      raise_ub "getelementptr into a vector with non-byte-addressable element type".toUTF8
    else match v, t with
    | DVALUE_Base DVALUE_Poison, _ => raise_ret none
    | _, DTYPE_Array vec _ ta =>
      match gep_index v with
      | some k => List.cons (k, Int.ofNat (sequential_stride vec ta)) <$> gep_steps_h ta rest
      | none => raise_error "gep_steps_h: index is not an integer".toUTF8
    | DVALUE_Base (DVALUE_I sz i), DTYPE_Struct packed ts =>
      if sz.val == 32 then
        match gep_struct_field packed ts (unsigned i).toNat with
        | some (off, t') => List.cons (Int.ofNat off, 1) <$> gep_steps_h t' rest
        | none => raise_error "gep_steps_h: no such struct field".toUTF8
      else raise_error "gep_steps_h: a struct index must be an i32".toUTF8
    | _, DTYPE_Struct _ _ => raise_error "gep_steps_h: a struct index must be an i32".toUTF8
    | _, _ => raise_error "gep_steps_h: indexing into a non-aggregate type".toUTF8
termination_by structural vs

def gep_steps (t : dtyp) : List dvalue → EOUP (List (Int × Int))
  | [] => raise_error "gep_steps: no indices".toUTF8
  | DVALUE_Base DVALUE_Poison :: _ => raise_ret none
  | v :: rest =>
    match gep_index v with
    | some k => List.cons (k, Int.ofNat (alloc_size_dtyp t)) <$> gep_steps_h t rest
    | none => raise_error "gep_steps: index is not an integer".toUTF8

def gep_offset (steps : List (Int × Int)) : Int :=
  steps.foldl (fun off (k, size) ↦ off + k * size) 0

def in_signed_index_range (x : Int) : Bool :=
  let half := two_p (gep_index_bits - 1)
  decide (-half ≤ x) && decide (x < half)

def in_unsigned_index_range (x : Int) : Bool :=
  decide (0 ≤ x) && decide (x < two_p gep_index_bits)

def gep_nusw_ok (addr off : Int) : List (Int × Int) → Bool
  | [] => true
  | (k, size) :: rest =>
    let o := k * size
    let off' := off + o
    in_signed_index_range k && in_signed_index_range o && in_signed_index_range off' &&
      in_unsigned_index_range (addr + off') && gep_nusw_ok addr off' rest

def gep_nuw_ok (addr off : Int) : List (Int × Int) → Bool
  | [] => true
  | (k, size) :: rest =>
    let o := (k % two_p gep_index_bits) * size
    let off' := off + o
    in_unsigned_index_range o && in_unsigned_index_range off' &&
      in_unsigned_index_range (addr + off') && gep_nuw_ok addr off' rest

def gep_inbounds_null_ok (off : Int) : List (Int × Int) → Bool
  | [] => true
  | (k, size) :: rest =>
    let off' := off + k * size
    off' == 0 && gep_inbounds_null_ok off' rest

def gep_index_trunc_ok (unsigned_rule : Bool) : dvalue → Bool
  | DVALUE_Base (DVALUE_I sz i) =>
    decide (Int.ofNat sz.val ≤ gep_index_bits) ||
      (if unsigned_rule then in_unsigned_index_range (unsigned i) else in_signed_index_range (signed i))
  | _ => true

def gep_trunc_violated (flags : gep_flags) (vs : List dvalue) : Bool :=
  ((flags.gep_inbounds || flags.gep_nusw) && !(vs.all (gep_index_trunc_ok false))) ||
    (flags.gep_nuw && !(vs.all (gep_index_trunc_ok true)))

/-- The pure semantics checks wrap and null-base inbounds, not allocated-object bounds. -/
def gep_flags_violated (flags : gep_flags) (addr : Int) (steps : List (Int × Int)) : Bool :=
  let a := addr % two_p gep_index_bits
  ((flags.gep_inbounds || flags.gep_nusw) && !gep_nusw_ok a 0 steps) ||
    (flags.gep_nuw && !gep_nuw_ok a 0 steps) ||
    (flags.gep_inbounds && addr == 0 && !gep_inbounds_null_ok 0 steps)

def handle_gep_ptr (flags : gep_flags) (t : dtyp) (a : Pa.PTR.ptr) (vs : List dvalue) :
    EOUP Pa.PTR.ptr := do
  let addr := Pa.P2I.ptr_to_int a
  let steps ← gep_steps t vs
  if gep_flags_violated flags addr steps || gep_trunc_violated flags vs then
    raise_ret none
  else
    EOU.bind (Pa.P2I.int_to_ptr (addr + gep_offset steps) (Pa.PTR.ptr_provenance a))
      (fun p ↦ raise_ret (some p))

private theorem handle_gep_ptr_single (dt : dtyp) (p : Pa.PTR.ptr) (ix : Pa.IPTR.iptr) :
    handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr ix)] =
      EOU.bind (Pa.P2I.int_to_ptr (Pa.P2I.ptr_to_int p + Int.ofNat (alloc_size_dtyp dt) * Pa.IPTR.to_Z ix)
        (Pa.PTR.ptr_provenance p)) (fun p' ↦ raise_ret (some p')) := by
  change EOU.bind (Pa.P2I.int_to_ptr (Pa.P2I.ptr_to_int p +
    (0 + Pa.IPTR.to_Z ix * Int.ofNat (alloc_size_dtyp dt))) _) _ = _
  rw [Int.zero_add, Int.mul_comm (Pa.IPTR.to_Z ix)]

theorem handle_gep_ptr_0 (dt : dtyp) (p : Pa.PTR.ptr) :
    handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr Pa.IPTR.zero_iptr)] = pure p := by
  rw [handle_gep_ptr_single, Pa.IPTRT.to_Z_0, Int.mul_zero, Int.add_zero,
    Pa.P2IT.int_to_ptr_ptr_to_int p rfl]
  rfl

theorem handle_gep_ptr_nil (flags : gep_flags) (dt : dtyp) (p : Pa.PTR.ptr) :
    handle_gep_ptr flags dt p [] = raise_error "gep_steps: no indices".toUTF8 := rfl

theorem handle_gep_ptr_ix (dt : dtyp) (p : Pa.PTR.ptr) {p' : Pa.PTR.ptr} (ix : Pa.IPTR.iptr)
    (h : handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr ix)] = pure p') :
    Pa.P2I.ptr_to_int p' = Pa.P2I.ptr_to_int p + Int.ofNat (alloc_size_dtyp dt) * Pa.IPTR.to_Z ix := by
  rw [handle_gep_ptr_single] at h
  obtain ⟨a, ha, hr⟩ := EOU_bind_ret_inv _ _ (some p') h
  cases hr
  exact Pa.P2IT.ptr_to_int_int_to_ptr _ _ ha

theorem handle_gep_ptr_ix_OOM (dt : dtyp) (p p' : Pa.PTR.ptr) (ix : Pa.IPTR.iptr) {msg : IRString}
    (h : handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr ix)] = raise_oom msg) :
    ∃ msg', Pa.P2I.int_to_ptr (Pa.P2I.ptr_to_int p + Int.ofNat (alloc_size_dtyp dt) * Pa.IPTR.to_Z ix)
      (Pa.PTR.ptr_provenance p) = raise_oom msg' := by
  rw [handle_gep_ptr_single] at h
  refine ⟨msg, ?_⟩
  generalize Pa.P2I.int_to_ptr _ _ = result at h ⊢
  cases result <;> cases h <;> rfl

theorem handle_gep_ptr_ix' (dt : dtyp) (p : Pa.PTR.ptr) {p' : Pa.PTR.ptr} (ix : Pa.IPTR.iptr)
    (h : raise_ret p' = Pa.P2I.int_to_ptr (Pa.P2I.ptr_to_int p + Int.ofNat (alloc_size_dtyp dt) * Pa.IPTR.to_Z ix)
      (Pa.PTR.ptr_provenance p)) :
    handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr ix)] = pure p' := by
  rw [handle_gep_ptr_single, ← h]
  rfl

theorem handle_gep_ptr_ix'_OOM (dt : dtyp) (p p' : Pa.PTR.ptr) (ix : Pa.IPTR.iptr) {msg : IRString}
    (h : Pa.P2I.int_to_ptr (Pa.P2I.ptr_to_int p + Int.ofNat (alloc_size_dtyp dt) * Pa.IPTR.to_Z ix)
      (Pa.PTR.ptr_provenance p) = raise_oom msg) :
    ∃ msg', handle_gep_ptr gep_no_flags dt p [DVALUE_Base (DVALUE_Iptr ix)] = raise_oom msg' := by
  refine ⟨msg, ?_⟩
  rw [handle_gep_ptr_single, h]
  rfl

theorem handle_gep_ptr_preserves_provenance (flags : gep_flags) (dt : dtyp) (ixs : List dvalue)
    (p : Pa.PTR.ptr) {p' : Pa.PTR.ptr} (h : handle_gep_ptr flags dt p ixs = pure p') :
    Pa.PTR.ptr_provenance p = Pa.PTR.ptr_provenance p' := by
  obtain ⟨result, _, hr⟩ := EOU_bind_ret_inv (gep_steps dt ixs) _ (some p') h
  cases result with
  | none => cases hr
  | some steps =>
    change (if gep_flags_violated flags (Pa.P2I.ptr_to_int p) steps || gep_trunc_violated flags ixs then
      raise_ret none else EOU.bind _ _) = raise_ret (some p') at hr
    split at hr
    · cases hr
    · obtain ⟨a, ha, hret⟩ := EOU_bind_ret_inv _ _ (some p') hr
      cases hret
      exact (Pa.P2IT.int_to_ptr_provenance _ _ ha).symm

def eval_gep (flags : gep_flags) (t : dtyp) (dv : dvalue) (vs : List dvalue) : EOU dvalue :=
  match dv with
  | DVALUE_Base (DVALUE_Pointer a) =>
    catch_pois (DVALUE_Base DVALUE_Poison) (handle_gep_ptr flags t a vs)
      (fun p ↦ raise_ret (DVALUE_Base (DVALUE_Pointer p)))
  | DVALUE_Base DVALUE_Poison => raise_ret (DVALUE_Base DVALUE_Poison)
  | _ => raise_error "non-ptr".toUTF8

end Vellvm.Semantics.Operations.Gep
