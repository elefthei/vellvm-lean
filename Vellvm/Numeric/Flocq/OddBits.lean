/-
The Compcert verified compiler.
Xavier Leroy and Jacques-Henri Jourdan, INRIA Paris-Rocquencourt.
Copyright Institut National de Recherche en Informatique et en Automatique. All rights
reserved. This file is distributed under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation, either version 2.1 of the License,
or (at your option) any later version. This file is also distributed under the terms
of the INRIA Non-Commercial License Agreement.
-/
import Vellvm.Numeric.Flocq.Normalize
import Vellvm.Numeric.Zbits

namespace Vellvm.Numeric.Flocq

def oddInt (x k : Int) : Int :=
  (if x % pow2 k = 0 ∨ (x / pow2 k) % 2 = 1 then x / pow2 k else x / pow2 k + 1) * pow2 k

theorem odd_scaled_int (n k : Int) (hk : 0 ≤ k) :
    Zrnd_odd ((n : ℝ) * (2 : ℝ) ^ (-k)) * pow2 k = oddInt n k := by
  rw [zpow_neg, ← div_eq_mul_inv, ← pow2_cast hk]
  let d := pow2 k
  have hd : 0 < d := pow2_pos hk
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hf : ⌊(n : ℝ) / d⌋ = n / d := by simp [Int.floor_div_cast_of_nonneg hd.le]
  have he : ((n / d : Int) : ℝ) = n / (d : ℝ) ↔ n % d = 0 := by
    rw [eq_div_iff hd']
    norm_cast
    have h := Int.emod_add_mul_ediv n d
    rw [mul_comm d] at h
    omega
  change Zrnd_odd ((n : ℝ) / d) * d =
    (if n % d = 0 ∨ n / d % 2 = 1 then n / d else n / d + 1) * d
  apply congrArg (· * d)
  unfold Zrnd_odd
  simp only [hf, he]
  split
  · rfl
  · next h =>
      have hl := Int.floor_le ((n : ℝ) / d)
      have hu := Int.lt_floor_add_one ((n : ℝ) / d)
      rw [hf] at hl hu
      apply Int.ceil_eq_iff.mpr
      push_cast
      exact ⟨by simpa using hl.lt_of_ne (he.not.mpr fun hr ↦ h (Or.inl hr)), hu.le⟩

private theorem force_odd (q : Int) :
    (if q % 2 = 1 then q else q + 1) = Int.lor q 1 := by
  induction q using Int.bitCasesOn with
  | h b t =>
    have hz : Int.lor t 0 = t := by
      apply Zbits.equal_same_bits
      intro i hi
      simp [Zbits.testbit, Int.testBit_lor, show (0 : Int).testBit i.toNat = false by
        change (0 : Nat).testBit i.toNat = false; simp]
    rw [show Int.lor (Int.bit b t) 1 = Int.bit true t by
      change Int.lor (Int.bit b t) (Int.bit true 0) = _
      rw [Int.lor_bit, Bool.or_true, hz]]
    cases b <;> simp [Int.bit]

private theorem shiftl_of_nonneg (x k : Int) (hk : 0 ≤ k) : shiftl x k = x * pow2 k := by
  rcases hk.eq_or_lt with h | h
  · subst k; simp [shiftl, shiftr, pow2, zpowNat]
  · simp [shiftl, shiftr, h]

theorem odd_shifts (x k : Int) (hk : 0 ≤ k) :
    oddInt x k = shiftl (if x % pow2 k = 0 then shiftr x k else Int.lor (shiftr x k) 1) k := by
  rw [shiftl_of_nonneg _ _ hk]
  by_cases h : x % pow2 k = 0 <;> simp [oddInt, shiftr, not_lt.mpr hk, h, force_odd]

private theorem bit_mul_pow (x : Int) (k i : Nat) :
    (x * 2 ^ k).testBit i = (decide (k ≤ i) && x.testBit (i - k)) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, show x * 2 ^ k * 2 = Int.bit false (x * 2 ^ k) by
      simp [Int.bit, mul_comm]]
    cases i <;> simp [ih]

private theorem bit_div_pow (x : Int) (k i : Nat) :
    (x / 2 ^ k).testBit i = x.testBit (k + i) := by
  rw [show (2 : Int) ^ k = ((2 ^ k : Nat) : Int) by simp,
    ← Int.shiftRight_eq_div_pow, ← Int.shiftRight_natCast_right]
  cases x with
  | ofNat n =>
    change ((n : Int) >>> (k : Int)).testBit i = _
    rw [Int.shiftRight_natCast]
    exact Nat.testBit_shiftRight _
  | negSucc n =>
    rw [Int.shiftRight_negSucc]
    exact congrArg Bool.not (Nat.testBit_shiftRight n)

theorem odd_bits (x y k : Int) (hk : 0 ≤ k)
    (below : ∀ i, (0 ≤ i ∧ i < k) → testbit y i = false)
    (atBit : testbit y k = (if x % pow2 k = 0 then testbit x k else true))
    (above : ∀ i, k < i → testbit y i = testbit x i) : oddInt x k = y := by
  rw [odd_shifts _ _ hk, shiftl_of_nonneg _ _ hk]
  lift k to Nat using hk
  simp only [pow2, zpowNat, Int.natCast_nonneg, not_lt.mpr, ite_false, Int.toNat_natCast,
    shiftr] at atBit ⊢
  apply Zbits.equal_same_bits
  intro i hi
  lift i to Nat using hi
  change Int.testBit (_ * 2 ^ k) i = y.testBit i
  rw [bit_mul_pow]
  rcases lt_trichotomy i k with h | rfl | h
  · simpa [not_le.mpr h, testbit] using (below i ⟨by omega, by omega⟩).symm
  · simp only [testbit, Int.natCast_nonneg, decide_true, Bool.true_and, Int.toNat_natCast] at atBit
    rw [atBit]
    split <;> simp [bit_div_pow, Int.testBit_lor, show (1 : Int).testBit 0 = true by rfl]
  · have hy : y.testBit i = x.testBit i := above i (by exact_mod_cast h)
    have hone : (1 : Int).testBit (i - k) = false := by
      change (1 : Nat).testBit (i - k) = false
      apply Bool.eq_false_iff.mpr
      simp [Nat.testBit_one_eq_true_iff_self_eq_zero, show i - k ≠ 0 by omega]
    rw [hy]
    split <;> simp [h.le, bit_div_pow, Int.testBit_lor, hone, Nat.add_sub_of_le h.le]

end Vellvm.Numeric.Flocq
