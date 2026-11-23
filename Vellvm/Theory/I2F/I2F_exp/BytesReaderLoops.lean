import Vellvm.Theory.I2F.I2F_exp.BytesBasic
import Vellvm.Theory.MemoryBytesFacts.Aggregate
import Vellvm.Theory.I2F.I2F_exp.Values

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.EOU
open Vellvm.Semantics.MemoryBytes Vellvm.Semantics.DynamicValues Vellvm.Utils.ListUtil
open Vellvm.Theory.I2F.Refinement Vellvm.Syntax.DynamicTypes Vellvm.Numeric.Integers
universe u
open Vellvm.Semantics.Interfaces.Sizeof
abbrev ReadRel (t : dtyp) := ∀ {bs cs}, List.Forall₂ I2F_memory_byte bs cs →
  I2F_EOU I2F_dvalue (@memory_bytes_to_dvalue PInf bs t) (@memory_bytes_to_dvalue PFin cs t)

theorem readStructRel (ts : List dtyp) (ih : ∀ t ∈ ts, ReadRel t) (np : Nat)
    (pad : Option Nat) (off : Nat) {bs cs} (h : List.Forall₂ I2F_memory_byte bs cs) :
    I2F_EOU (List.Forall₂ I2F_dvalue)
      (@Theory.MemoryBytesFacts.read_struct_loop PInf (@memory_bytes_to_dvalue PInf) np pad off ts bs)
      (@Theory.MemoryBytesFacts.read_struct_loop PFin (@memory_bytes_to_dvalue PFin) np pad off ts cs) := by
  induction ts generalizing off bs cs with
  | nil => exact .I2F_EOU_ret _ _ .nil
  | cons t ts loop =>
    simp only [Theory.MemoryBytesFacts.read_struct_loop_cons]
    apply I2F_EOU_bind (R := I2F_dvalue)
    · let n := if pad.isSome then pad_amount (@dtyp_alignment PInf.SIZE t).preferred_alignment off else 0
      by_cases hn : off + n + @store_size_dtyp PInf.SIZE t ≤ np
      · simp only [n] at hn; simp only [if_pos hn]; exact .I2F_EOU_ret _ _ (I2F_poison_of_dtyp t)
      · simp only [n] at hn; simp only [if_neg hn]; exact ih t List.mem_cons_self (List.forall₂_take _ (List.forall₂_drop _ h))
    · intro x y hxy
      exact I2F_EOU_bind _ _ (loop (fun u hu ↦ ih u (List.mem_cons_of_mem _ hu)) _
        (List.forall₂_drop _ (List.forall₂_drop _ h))) fun _ _ hr ↦ .I2F_EOU_ret _ _ (.cons hxy hr)

theorem readArrayRel (t : dtyp) (ih : ReadRel t) (np stride n off : Nat) {bs cs}
    (h : List.Forall₂ I2F_memory_byte bs cs) : I2F_EOU (List.Forall₂ I2F_dvalue)
      (@Theory.MemoryBytesFacts.read_array_loop PInf (@memory_bytes_to_dvalue PInf) np stride t n off bs)
      (@Theory.MemoryBytesFacts.read_array_loop PFin (@memory_bytes_to_dvalue PFin) np stride t n off cs) := by
  induction n generalizing off bs cs with
  | zero => exact .I2F_EOU_ret _ _ .nil
  | succ n loop =>
    simp only [Theory.MemoryBytesFacts.read_array_loop_cons]
    apply I2F_EOU_bind (R := I2F_dvalue)
    · split
      · exact .I2F_EOU_ret _ _ (I2F_poison_of_dtyp t)
      · exact ih (List.forall₂_take _ h)
    · intro x y hxy
      exact I2F_EOU_bind _ _ (loop _ (List.forall₂_drop _ h)) fun _ _ hr ↦ .I2F_EOU_ret _ _ (.cons hxy hr)


end Vellvm.Theory.I2F.I2F_exp
