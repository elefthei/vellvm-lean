import Vellvm.Theory.I2F.I2F_exp.MemoryByte
import Vellvm.Semantics.MemoryBytes.Scalar

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers

theorem I2F_is_poison_bit : ∀ {b b'}, I2F_memory_bit b b' → @is_poison_bit PInf b = @is_poison_bit PFin b' := by intro _ _ h; cases h <;> rfl

theorem I2F_all_poison_bits : ∀ {bs bs'}, List.Forall₂ I2F_memory_bit bs bs' → @all_poison_bits PInf bs = @all_poison_bits PFin bs' := by
  intro _ _ h
  unfold all_poison_bits
  induction h with
  | nil => rfl
  | cons hb _ ih => simp only [List.all_cons, I2F_is_poison_bit hb, ih]

theorem I2F_is_all_poison_byte : ∀ {b b'}, I2F_memory_byte b b' → @is_all_poison_byte PInf b = @is_all_poison_byte PFin b' := by
  intro _ _ h
  cases h with
  | I2F_BYTE_Mixed hb => exact I2F_all_poison_bits hb
  | _ => rfl

theorem I2F_poison_split : ∀ {bs bs'}, List.Forall₂ I2F_memory_byte bs bs' →
    (@poison_split PInf bs).1 = (@poison_split PFin bs').1 ∧
    List.Forall₂ I2F_memory_byte (@poison_split PInf bs).2 (@poison_split PFin bs').2 := by
  intro _ _ h
  induction h with
  | nil => exact ⟨rfl, .nil⟩
  | cons hb ht ih =>
    simp only [poison_split, I2F_is_all_poison_byte hb]
    split
    · exact ⟨congrArg (1 + ·) ih.1, ih.2⟩
    · exact ⟨rfl, .cons hb ht⟩

theorem I2F_all_poison_bytes : ∀ {bs bs'}, List.Forall₂ I2F_memory_byte bs bs' → @all_poison_bytes PInf bs = @all_poison_bytes PFin bs' := by
  intro _ _ h
  unfold all_poison_bytes
  have empty {xs ys} (hr : List.Forall₂ I2F_memory_byte xs ys) : xs.isEmpty = ys.isEmpty := by
    cases hr <;> rfl
  exact empty (I2F_poison_split h).2

theorem I2F_is_ptr_bit : ∀ {b b'}, I2F_memory_bit b b' → @is_ptr_bit PInf b = @is_ptr_bit PFin b' := by intro _ _ h; cases h <;> rfl

end Vellvm.Theory.I2F.I2F_exp
