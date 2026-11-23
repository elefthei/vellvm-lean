import Vellvm.Theory.I2F.I2F_exp.BytesValidPointer
import Vellvm.Theory.I2F.I2F_exp.BytesPointer

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof

theorem I2F_pointer_byte_at : ∀ {p q} i {b c}, I2F_Addr p q → I2F_memory_byte b c → @pointer_byte_at PInf p i b = @pointer_byte_at PFin q i c := by
  intro p q i b c hp hb
  have h := I2F_EOUP_no_cut_inv Eq (I2F_EOUP_valid_pointer_byte i hp hb)
    (@no_cut_valid_pointer_byte PInf p i b) (@no_cut_valid_pointer_byte PFin q i c)
  unfold pointer_byte_at
  rcases h with ⟨x,y,hx,hy,rfl⟩ | ⟨hx,hy⟩ | ⟨_,_,hx,hy⟩ <;> rw [hx,hy]

theorem I2F_pointer_slice_from : ∀ {p q bs cs}, I2F_Addr p q → List.Forall₂ I2F_memory_byte bs cs → ∀ i,
    @pointer_slice_from PInf p i bs = @pointer_slice_from PFin q i cs := by
  intro p q bs cs hp h
  induction h with
  | nil => exact fun _ ↦ rfl
  | cons hb ht ih => intro i; simp only [pointer_slice_from, I2F_pointer_byte_at i hp hb, ih]

theorem I2F_memory_bytes_to_pointer_slice : ∀ {bs cs}, List.Forall₂ I2F_memory_byte bs cs →
    match @memory_bytes_to_pointer_slice PInf bs, @memory_bytes_to_pointer_slice PFin cs with
    | none, none => True
    | some (p,i), some (q,j) => I2F_Addr p q ∧ i = j
    | _, _ => False := by
  intro bs cs h
  have same {p q} (i : Nat) (hp : I2F_Addr p q) (b : Bool) :
      match (if b then some (p,i) else none), (if b then some (q,i) else none) with
      | none, none => True
      | some (a,j), some (a',k) => I2F_Addr a a' ∧ j = k
      | _, _ => False := by cases b <;> first | trivial | exact ⟨hp,rfl⟩
  cases h with
  | nil => trivial
  | cons hb ht =>
    have hw := List.Forall₂.cons hb ht
    cases hb with
    | I2F_BYTE_I => trivial
    | I2F_BYTE_Pointer p q i hp =>
      simp only [memory_bytes_to_pointer_slice, I2F_pointer_slice_from hp hw]
      exact same _ hp _
    | I2F_BYTE_Mixed hm =>
      cases hm with
      | nil => trivial
      | cons hbit _ =>
        cases hbit with
        | I2F_Bit_bit | I2F_Bit_psn => trivial
        | I2F_Bit_ptr p q j hp =>
          simp only [memory_bytes_to_pointer_slice, I2F_pointer_slice_from hp hw]
          exact same _ hp _

theorem I2F_EOUP_memory_bytes_to_pointer : ∀ {bs cs}, List.Forall₂ I2F_memory_byte bs cs → I2F_EOUP I2F_Addr (@memory_bytes_to_pointer PInf bs) (@memory_bytes_to_pointer PFin cs) := by
  intro bs cs h
  have ha := I2F_EOUP_memory_bytes_to_address_ptr h
  have leading {p q} (hp : I2F_Addr p q) := I2F_EOUP_bind
    (fun (b : Bool) ↦ if b then pure p else @memory_bytes_to_address_ptr PInf bs)
    (fun (b : Bool) ↦ if b then pure q else @memory_bytes_to_address_ptr PFin cs)
    (I2F_EOUP_valid_pointer_bytes 0 hp h) (by
      intro x y e; cases e; cases x <;> first | exact .I2F_EOUP_ret _ _ hp | exact ha)
  cases h with
  | nil => exact ha
  | cons hb _ => cases hb with
    | I2F_BYTE_I => exact ha
    | I2F_BYTE_Pointer _ _ _ hp => exact leading hp
    | I2F_BYTE_Mixed hm => cases hm with
      | nil => exact ha
      | cons hbit _ => cases hbit <;> first | exact ha | apply leading; assumption

end Vellvm.Theory.I2F.I2F_exp
