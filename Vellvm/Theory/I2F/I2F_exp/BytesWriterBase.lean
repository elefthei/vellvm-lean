import Vellvm.Theory.I2F.I2F_exp.BytesBasic

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof

theorem I2F_store_size_dtyp : ∀ t, @store_size_dtyp PInf.SIZE t = @store_size_dtyp PFin.SIZE t := fun _ ↦ rfl

theorem I2F_dtyp_alignment : ∀ t, @dtyp_alignment PInf.SIZE t = @dtyp_alignment PFin.SIZE t := fun _ ↦ rfl

theorem I2F_alloc_size_dtyp : ∀ t, @alloc_size_dtyp PInf.SIZE t = @alloc_size_dtyp PFin.SIZE t := fun _ ↦ rfl

theorem I2F_max_alignment : ∀ t, @max_preferred_dtyp_alignment PInf.SIZE t = @max_preferred_dtyp_alignment PFin.SIZE t := fun _ ↦ rfl

theorem I2F_memory_byte_of_dvalue_bv : ∀ {sz} {b b'} i, @I2F_dvalue_bv sz b b' → I2F_memory_byte
    (@memory_byte_of_dvalue_bv PInf sz b i) (@memory_byte_of_dvalue_bv PFin sz b' i) := by
  intro sz b c i h
  cases h with
  | I2F_BYTE_I => exact I2F_BYTE_I _
  | I2F_BYTE_Pointer _ _ _ h => exact I2F_BYTE_Pointer _ _ _ h
  | I2F_BYTE_Mixed h =>
    have hm := List.forall₂_take 8 (List.forall₂_drop (8*i) h)
    apply I2F_BYTE_Mixed
    apply List.rel_append hm
    rw [hm.length_eq]
    split
    · exact Forall2_repeat _ _ _ _ I2F_Bit_psn
    · exact .nil

theorem I2F_poison_memory_byte : I2F_memory_byte (@poison_memory_byte PInf) (@poison_memory_byte PFin) := I2F_BYTE_Mixed (Forall2_repeat _ _ _ 8 I2F_Bit_psn)

def I2F_ser_state : (Nat × List (@memory_byte PInf)) → (Nat × List (@memory_byte PFin)) → Prop := fun x y ↦ x.1 = y.1 ∧ List.Forall₂ I2F_memory_byte x.2 y.2

theorem I2F_accumulate_poison_bytes : ∀ n {bs bs'}, List.Forall₂ I2F_memory_byte bs bs' → List.Forall₂ I2F_memory_byte (@accumulate_poison_bytes PInf n bs) (@accumulate_poison_bytes PFin n bs') := fun _ _ _ h ↦ Forall2_rev_loop_acc _ _ _ (fun _ ↦ I2F_poison_memory_byte) _ _ _ _ h

theorem I2F_accumulate_padding_bytes : ∀ o n {bs bs'}, List.Forall₂ I2F_memory_byte bs bs' → I2F_ser_state (@accumulate_padding_bytes PInf o n bs) (@accumulate_padding_bytes PFin o n bs') := fun _ n _ _ h ↦ ⟨rfl, I2F_accumulate_poison_bytes n h⟩

theorem I2F_accumulate_padding : ∀ o ta {bs bs'}, List.Forall₂ I2F_memory_byte bs bs' → I2F_ser_state (@accumulate_padding PInf o ta bs) (@accumulate_padding PFin o ta bs') := by
  intro o ta _ _ h
  cases ta with
  | none => exact ⟨rfl,h⟩
  | some a => exact I2F_accumulate_padding_bytes o _ h

theorem I2F_acc_memory_bytes_of_dvalue_base : ∀ t {b c}, I2F_dvalue_base b c → ∀ o {xs ys}, List.Forall₂ I2F_memory_byte xs ys →
    I2F_ser_state (@acc_memory_bytes_of_dvalue_base PInf t b o xs) (@acc_memory_bytes_of_dvalue_base PFin t c o ys) := by
  intro t b c h o xs ys hxy
  refine ⟨rfl, Forall2_rev_loop_acc _ _ _ ?_ _ _ _ _ hxy⟩
  intro i
  cases h with
  | I2F_dvalue_Pointer _ _ hp => exact I2F_BYTE_Pointer _ _ _ hp
  | I2F_dvalue_Int => exact I2F_BYTE_I _
  | I2F_dvalue_Ptr hp => unfold I2F_Iptr at hp; cases hp; exact I2F_BYTE_I _
  | I2F_dvalue_Double | I2F_dvalue_Float => exact I2F_BYTE_I _
  | I2F_dvalue_Poison | I2F_dvalue_None => exact I2F_poison_memory_byte
  | I2F_dvalue_B hb => exact I2F_memory_byte_of_dvalue_bv i hb

end Vellvm.Theory.I2F.I2F_exp
