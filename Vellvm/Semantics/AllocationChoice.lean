module

public import Vellvm.Semantics.Handlers.Memory.Allocation
public import Mathlib.Order.Basic

@[expose] public section
namespace Vellvm.Semantics
open Utils.IntMaps Handlers.Memory

/-- The entire half-open byte interval must be free. A raw answer need not fit the pointer type. -/
def AllocationLegal (m : IntMap A) (size align : Nat) (k : Int) : Prop :=
  0 < k ∧ (align = 0 ∨ k % (align : Int) = 0) ∧
    ∀ i : Int, 0 ≤ i → i < (size : Int) → ¬ IM.In (k + i) m

theorem pad_to_mod {align : Nat} (ha : 0 < align) (n : Nat) : pad_to align n % align = 0 := by
  have bound := Nat.mod_lt n ha
  simp only [pad_to, pad_amount, Nat.add_mod_mod]
  rw [← Nat.mod_add_mod, Nat.add_sub_of_le (Nat.le_of_lt bound), Nat.mod_self]

theorem next_key_with_alignment_legal (m : IntMap A) (size align : Nat) :
    AllocationLegal m size align (next_key_with_alignment m align) := by
  let n := (IM_greatest_key m).elim 1 (fun k ↦ 1 + k.toNat)
  have addr : next_key_with_alignment m align = (pad_to align n : Nat) := by
    unfold next_key_with_alignment n; cases IM_greatest_key m <;> rfl
  have low : n ≤ pad_to align n := Nat.le_add_right _ _
  have pos : 0 < n := by unfold n; cases IM_greatest_key m <;> simp <;> omega
  rw [addr]
  refine ⟨by omega, ?_, ?_⟩
  · by_cases h : align = 0
    · exact .inl h
    · apply Or.inr
      exact Int.emod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mpr
        (Nat.dvd_of_mod_eq_zero (pad_to_mod (by omega) n)))
  · intro i hi _ occupied
    obtain ⟨bound, hb⟩ := IM_greatest_key_In' _ _ occupied
    have hkey := next_key_correct _ _ occupied
    have hn : n = 1 + bound.toNat := by simp [n, hb]
    simp only [next_key, hb] at hkey
    omega

end Vellvm.Semantics
