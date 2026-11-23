import Vellvm.Numeric.Integers.Bitwise
import Vellvm.Semantics.VellvmIntegers

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Numeric Vellvm.Numeric.Integers
open Vellvm.Semantics.VellvmIntegers (mcmpu_Z mcmp_Z msamesign_Z)

theorem unsigned_add_bounded : ∀ {sz : Positive} (x y : bit_int sz), unsigned x + unsigned y < @modulus sz →
    unsigned (add x y) = unsigned x + unsigned y := by
  intro sz x y h
  apply unsigned_repr
  have := unsigned_range x
  have := unsigned_range y
  unfold max_unsigned
  omega

theorem unsigned_sub_bounded : ∀ {sz : Positive} (x y : bit_int sz), unsigned y ≤ unsigned x →
    unsigned (sub x y) = unsigned x - unsigned y := by
  intro sz x y h
  apply unsigned_repr
  have := unsigned_range x
  have := unsigned_range y
  unfold max_unsigned
  omega

theorem unsigned_divu : ∀ {sz : Positive} (x y : bit_int sz), unsigned y ≠ 0 →
    unsigned (divu x y) = (unsigned x).fdiv (unsigned y) := by
  intro sz x y h
  apply unsigned_repr
  have hx := unsigned_range_2 x
  have hy := (unsigned_range y).1
  rw [Int.fdiv_eq_ediv_of_nonneg _ hy]
  exact ⟨Int.ediv_nonneg hx.1 hy, (Int.ediv_le_self _ hx.1).trans hx.2⟩

theorem unsigned_modu : ∀ {sz : Positive} (x y : bit_int sz), unsigned y ≠ 0 →
    unsigned (modu x y) = (unsigned x).fmod (unsigned y) := by
  intro sz x y h
  apply unsigned_repr
  have hy := unsigned_range y
  exact ⟨Int.fmod_nonneg_of_pos _ (by omega),
    le_trans (Int.fmod_lt_of_pos _ (by omega)).le (unsigned_range_2 y).2⟩

theorem unsigned_shru : ∀ {sz : Positive} (x y : bit_int sz),
    unsigned (shru x y) = unsigned x >>> unsigned y := by
  intro sz x y
  simp [unsigned, intval, shru, Int.shiftRight_natCast_right]

theorem unsigned_testbit_above : ∀ {sz : Positive} (x : bit_int sz) (i : Int), (sz.val : Int) ≤ i →
    Zbits.testbit (unsigned x) i = false := by
  exact bits_above

theorem max_unsigned_ones : ∀ {sz : Positive}, @max_unsigned sz = Int.ofNat (2 ^ sz.val - 1) := by
  intro sz
  change @modulus sz - 1 = _
  rw [modulus_def]
  change Int.ofNat (2 ^ sz.val) - 1 = _
  simp only [Int.ofNat_eq_natCast, Nat.cast_sub (Nat.two_pow_pos _), Nat.cast_one]

theorem Z_bits_range : ∀ {sz : Positive} (z : Int), 0 ≤ z →
    (∀ i : Int, (sz.val : Int) ≤ i → Zbits.testbit z i = false) → 0 ≤ z ∧ z ≤ @max_unsigned sz := by
  intro sz z hn above
  refine ⟨hn, Zbits.Ztestbit_le _ _ (by have := @modulus_pos sz; unfold max_unsigned; omega) ?_⟩
  intro i hi bit
  have low : i < (sz.val : Int) := by
    by_contra! h
    rw [above _ h] at bit
    contradiction
  rw [max_unsigned_ones]
  simp [Zbits.testbit, hi, Int.testBit, Nat.testBit_two_pow_sub_one, show i.toNat < sz.val by omega]

theorem unsigned_and_land : ∀ {sz : Positive} (x y : bit_int sz),
    unsigned (and x y) = Int.land (unsigned x) (unsigned y) := by
  intro sz x y
  exact congrArg Int.ofNat (BitVec.toNat_and ..)

theorem unsigned_or_lor : ∀ {sz : Positive} (x y : bit_int sz),
    unsigned (or x y) = Int.lor (unsigned x) (unsigned y) := by
  intro sz x y
  exact congrArg Int.ofNat (BitVec.toNat_or ..)

theorem unsigned_xor_lxor : ∀ {sz : Positive} (x y : bit_int sz),
    unsigned (xor x y) = Int.xor (unsigned x) (unsigned y) := by
  intro sz x y
  exact congrArg Int.ofNat (BitVec.toNat_xor ..)

theorem eq_unsigned_eqb : ∀ {sz : Positive} (x y : bit_int sz), eq x y = (unsigned x == unsigned y) := by
  intro sz x y
  by_cases h : x = y
  · simp [eq, h]
  · have h' : unsigned x ≠ unsigned y := fun e ↦ h (bit_int.ext_unsigned e)
    simp [eq, h, h']

theorem eq_zero_one_false : ∀ {sz : Positive}, @eq sz zero one = false := by
  intro sz
  rw [eq_unsigned_eqb, unsigned_zero, unsigned_one]
  rfl

theorem unsigned_add_no_carry : ∀ {sz : Positive} (x y : bit_int sz), eq (add_carry x y zero) one = false →
    unsigned (add x y) = unsigned x + unsigned y := by
  intro sz x y h
  apply unsigned_add_bounded
  by_contra hn
  simp [add_carry, unsigned_zero, hn, eq] at h

theorem ltu_unsigned_ltb : ∀ {sz : Positive} (x y : bit_int sz), ltu x y = decide (unsigned x < unsigned y) := by
  intros; rfl

theorem cmpu_unsigned : ∀ {sz : Positive} (c : comparison) (x y : bit_int sz),
    cmpu c x y = mcmpu_Z c (unsigned x) (unsigned y) := by
  intro sz c x y
  cases c <;> simp only [cmpu, mcmpu_Z, mcmp_Z, eq_unsigned_eqb, ltu, bne]
  · by_cases h : unsigned y < unsigned x <;> simp [h, le_of_not_gt, not_le_of_gt] <;> omega
  · by_cases h : unsigned x < unsigned y <;> simp [h, le_of_not_gt, not_le_of_gt] <;> omega

theorem msamesign_Z_nonneg : ∀ x y : Int, 0 ≤ x → 0 ≤ y → msamesign_Z x y = true := by
  intro x y hx hy
  simp [msamesign_Z, not_lt.mpr hx, not_lt.mpr hy]

end Vellvm.Theory.I2F.I2F_exp
