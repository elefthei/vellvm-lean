/-
The Compcert verified compiler
Xavier Leroy, INRIA Paris-Rocquencourt

Copyright Institut National de Recherche en Informatique et en Automatique.
All rights reserved. This file is distributed under the terms of the GNU Lesser
General Public License as published by the Free Software Foundation, either
version 2.1 of the License, or (at your option) any later version.
This file is also distributed under the terms of the INRIA Non-Commercial
License Agreement.
-/
module

public import Vellvm.Numeric.Integers.Arithmetic
public import Vellvm.Numeric.Integers.Bitwise
public import Vellvm.Numeric.Integers.Shifts
public import Vellvm.Numeric.Integers.Powers

@[expose] public section
namespace Vellvm.Numeric.Integers
open Rocqlib

theorem negate_cmp : ∀ {w : Positive} (c : comparison) (x y : bit_int w), cmp (negate_comparison c) x y = !(cmp c x y) := by
  intro w c x y; cases c <;> simp [cmp, negate_comparison]

theorem swap_cmp : ∀ {w : Positive} (c : comparison) (x y : bit_int w), cmp (swap_comparison c) x y = cmp c y x := by
  intro w c x y; cases c <;> simp [cmp, swap_comparison, eq_sym x y]

theorem negate_cmpu : ∀ {w : Positive} (c : comparison) (x y : bit_int w), cmpu (negate_comparison c) x y = !(cmpu c x y) := by
  intro w c x y; cases c <;> simp [cmpu, negate_comparison]

theorem swap_cmpu : ∀ {w : Positive} (c : comparison) (x y : bit_int w), cmpu (swap_comparison c) x y = cmpu c y x := by
  intro w c x y; cases c <;> simp [cmpu, swap_comparison, eq_sym x y]

theorem translate_eq : ∀ {w : Positive} (x y d : bit_int w), eq (add x d) (add y d) = eq x y := by
  intro w x y d
  have cancel (a : bit_int w) : add (add a d) (neg d) = a := by
    rw [add_assoc, add_neg_zero, add_zero]
  by_cases h : x = y
  · simp [h, eq]
  · have ne : add x d ≠ add y d := fun e ↦ h <| by
      simpa only [cancel] using congrArg (fun a ↦ add a (neg d)) e
    simp [eq, ne, h]

theorem translate_ltu : ∀ {w : Positive} (x y d : bit_int w),
    (0 ≤ unsigned x + unsigned d ∧ unsigned x + unsigned d ≤ @max_unsigned w) →
    (0 ≤ unsigned y + unsigned d ∧ unsigned y + unsigned d ≤ @max_unsigned w) →
    ltu (add x d) (add y d) = ltu x y := by
  intro w x y d hx hy
  simp [ltu, add, unsigned_repr _ hx, unsigned_repr _ hy]

theorem translate_lt : ∀ {w : Positive} (x y d : bit_int w),
    (@min_signed w ≤ signed x + signed d ∧ signed x + signed d ≤ @max_signed w) →
    (@min_signed w ≤ signed y + signed d ∧ signed y + signed d ≤ @max_signed w) →
    lt (add x d) (add y d) = lt x y := by
  intro w x y d hx hy
  simp [lt, add_signed, signed_repr _ hx, signed_repr _ hy]

theorem translate_cmpu : ∀ {w : Positive} (c : comparison) (x y d : bit_int w),
    (0 ≤ unsigned x + unsigned d ∧ unsigned x + unsigned d ≤ @max_unsigned w) →
    (0 ≤ unsigned y + unsigned d ∧ unsigned y + unsigned d ≤ @max_unsigned w) →
    cmpu c (add x d) (add y d) = cmpu c x y := by
  intro w c x y d hx hy
  cases c <;> simp [cmpu, translate_eq, translate_ltu _ _ _ hx hy, translate_ltu _ _ _ hy hx]

theorem translate_cmp : ∀ {w : Positive} (c : comparison) (x y d : bit_int w),
    (@min_signed w ≤ signed x + signed d ∧ signed x + signed d ≤ @max_signed w) →
    (@min_signed w ≤ signed y + signed d ∧ signed y + signed d ≤ @max_signed w) →
    cmp c (add x d) (add y d) = cmp c x y := by
  intro w c x y d hx hy
  cases c <;> simp [cmp, translate_eq, translate_lt _ _ _ hx hy, translate_lt _ _ _ hy hx]

theorem notbool_isfalse_istrue : ∀ {w : Positive} (x : bit_int w), is_false x → is_true (notbool x) := by
  rintro w x (rfl : x = zero)
  simpa [is_true, notbool, eq] using (@one_not_zero w)

theorem notbool_istrue_isfalse : ∀ {w : Positive} (x : bit_int w), is_true x → is_false (notbool x) := by
  rintro w x (h : x ≠ zero)
  simp [notbool, is_false, eq, h]

theorem ltu_range_test : ∀ {w : Positive} (x y : bit_int w), ltu x y = true → unsigned y ≤ @max_signed w →
    0 ≤ signed x ∧ signed x < unsigned y := by
  intro w x y h hy
  have hxy : unsigned x < unsigned y := of_decide_eq_true h
  rw [signed_eq_unsigned x (by omega)]
  exact ⟨(unsigned_range x).1, hxy⟩

theorem lt_sub_overflow : ∀ {w : Positive} (x y : bit_int w),
    xor (sub_overflow x y zero) (negative (sub x y)) = (if lt x y then one else zero) := by
  intro w x y
  have hx := signed_range x
  have hy := signed_range y
  have hm := @half_modulus_modulus w
  have hp := @half_modulus_pos w
  simp only [min_signed, max_signed] at hx hy
  simp only [negative, sub_overflow, lt, signed_zero, sub_zero, decide_eq_true_eq,
    min_signed, max_signed, sub_signed]
  generalize signed x = a at *
  generalize signed y = b at *
  by_cases lo : a - b < -@half_modulus w
  · have hmod := Zmod_unique (a-b) (@modulus w) (-1) (a-b+@modulus w) (by omega) (by omega)
    have hs : signed (@repr w (a-b)) = a-b+@modulus w := by
      rw [signed, unsigned_repr_eq, hmod, if_pos (by omega)]
    simp [hs, show ¬(-@half_modulus w ≤ a-b) by omega, show ¬(a-b+@modulus w < 0) by omega,
      show a < b by omega, xor_zero]
  · by_cases hi : @half_modulus w ≤ a - b
    · have hmod := Zmod_unique (a-b) (@modulus w) 0 (a-b) (by omega) (by omega)
      have hs : signed (@repr w (a-b)) = a-b-@modulus w := by
        rw [signed, unsigned_repr_eq, hmod, if_neg (by omega)]
      simp [hs, show ¬(a-b ≤ @half_modulus w-1) by omega, show a-b-@modulus w < 0 by omega,
        show ¬a < b by omega, xor_idem]
    · have hr : @min_signed w ≤ a-b ∧ a-b ≤ @max_signed w := by
        change -@half_modulus w ≤ _ ∧ _ ≤ @half_modulus w - 1; omega
      rw [signed_repr _ hr, if_pos hr]
      by_cases h : a < b
      · simp [h, show a - b < 0 by omega, xor_zero_l]
      · simp [h, show ¬a - b < 0 by omega, xor_zero_l]

theorem signed_eq : ∀ {w : Positive} (x y : bit_int w), eq x y = proj_sumbool (zeq (signed x) (signed y)) := eq_signed

private theorem ordNotLt (a b : Int) :
    Bool.not (decide (b < a)) = (decide (a < b) || decide (a = b)) := by
  by_cases h₁ : b < a <;> by_cases h₂ : a < b <;> by_cases h₃ : a = b <;>
    simp_all <;> omega

private theorem wordEqDecide {w : Positive} (f : bit_int w → Int)
    (inv : ∀ x, repr (f x) = x) (x y : bit_int w) : eq x y = decide (f x = f y) := by
  by_cases h : x = y
  · simp [eq, h]
  · have h' : f x ≠ f y := fun e ↦ h <| by simpa only [inv] using congrArg (@repr w) e
    simp [eq, h, h']

theorem not_lt : ∀ {w : Positive} (x y : bit_int w), Bool.not (lt y x) = (lt x y || eq x y) := by
  intro w x y
  rw [wordEqDecide signed repr_signed]; exact ordNotLt _ _

theorem lt_not : ∀ {w : Positive} (x y : bit_int w),
    lt y x = (Bool.not (lt x y) && Bool.not (eq x y)) := by
  intro w x y
  simpa only [Bool.not_not, Bool.not_or] using congrArg Bool.not (not_lt x y)

theorem not_ltu : ∀ {w : Positive} (x y : bit_int w),
    Bool.not (ltu y x) = (ltu x y || eq x y) := by
  intro w x y
  rw [wordEqDecide unsigned repr_unsigned]; exact ordNotLt _ _

theorem ltu_not : ∀ {w : Positive} (x y : bit_int w),
    ltu y x = (Bool.not (ltu x y) && Bool.not (eq x y)) := by
  intro w x y
  simpa only [Bool.not_not, Bool.not_or] using congrArg Bool.not (not_ltu x y)

theorem no_overlap_sound : ∀ {w : Positive} (ofs1 : bit_int w) (sz1 : Int) (ofs2 : bit_int w) (sz2 : Int) (base : bit_int w),
    sz1 > 0 → sz2 > 0 → no_overlap ofs1 sz1 ofs2 sz2 = true →
    unsigned (add base ofs1) + sz1 ≤ unsigned (add base ofs2) ∨
    unsigned (add base ofs2) + sz2 ≤ unsigned (add base ofs1) := by
  intro w ofs1 sz1 ofs2 sz2 base h1 h2 h
  simp only [no_overlap, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  have := unsigned_range ofs1
  have := unsigned_range ofs2
  have := unsigned_add_either base ofs1
  have := unsigned_add_either base ofs2
  omega

theorem Zsize_pos : ∀ (x : Int), 0 ≤ Zsize x := Zbits.Zsize_pos

theorem Zsize_pos' : ∀ (x : Int), 0 < x → 0 < Zsize x := Zbits.Zsize_pos'

theorem Zsize_shiftin : ∀ (b : Bool) (x : Int), 0 < x → Zsize (Zshiftin b x) = Zsize x + 1 := Zbits.Zsize_shiftin

theorem Ztestbit_size_1 : ∀ (x : Int), 0 < x → Zbits.testbit x (Zsize x - 1) = true := Zbits.Ztestbit_size_1

theorem Ztestbit_size_2 : ∀ (x : Int), 0 ≤ x → ∀ i : Int, i ≥ Zsize x → Zbits.testbit x i = false := Zbits.Ztestbit_size_2

theorem Zsize_interval_1 : ∀ (x : Int), 0 ≤ x → 0 ≤ x ∧ x < two_p (Zsize x) := Zbits.Zsize_interval_1

theorem Zsize_interval_2 : ∀ (x n : Int), 0 ≤ n → (0 ≤ x ∧ x < two_p n) → n ≥ Zsize x := Zbits.Zsize_interval_2

theorem Zsize_monotone : ∀ (x y : Int), (0 ≤ x ∧ x ≤ y) → Zsize x ≤ Zsize y := Zbits.Zsize_monotone

theorem size_zero : ∀ {w : Positive}, size (@zero w) = 0 := by intro w; rw [size, unsigned_zero] <;> rfl

theorem bits_size_1 : ∀ {w : Positive} (x : bit_int w), x = zero ∨ testbit x (size x - 1) = true := by
  intro w x
  by_cases h : unsigned x = 0
  · exact .inl <| by rw [← repr_unsigned x, h] <;> rfl
  · exact .inr (Ztestbit_size_1 _ (by have := unsigned_range x; omega))

theorem bits_size_2 : ∀ {w : Positive} (x : bit_int w), ∀ i : Int, size x ≤ i → testbit x i = false := by
  intro w x i hi; exact Ztestbit_size_2 _ (unsigned_range x).1 _ hi

theorem size_range : ∀ {w : Positive} (x : bit_int w), 0 ≤ size x ∧ size x ≤ @zwordsize w := by
  intro w x
  exact ⟨Zsize_pos _, Zsize_interval_2 _ _ (Int.le_of_lt (@wordsize_pos w))
    (by simpa only [← modulus_power] using unsigned_range x)⟩

theorem bits_size_3 : ∀ {w : Positive} (x : bit_int w) (n : Int), 0 ≤ n →
    (∀ i : Int, (n ≤ i ∧ i < @zwordsize w) → testbit x i = false) → size x ≤ n := by
  intro w x n hn h
  by_contra bad
  rcases bits_size_1 x with rfl | hb
  · rw [size_zero] at bad; omega
  · have := h (size x - 1) (by have := size_range x; omega)
    simp_all

theorem bits_size_4 : ∀ {w : Positive} (x : bit_int w) (n : Int), 0 ≤ n →
    testbit x (n - 1) = true →
    (∀ i : Int, (n ≤ i ∧ i < @zwordsize w) → testbit x i = false) → size x = n := by
  intro w x n hn hb h
  have := bits_size_3 x n hn h
  by_contra bad
  have := bits_size_2 x (n-1) (by omega)
  simp_all

theorem size_interval_1 : ∀ {w : Positive} (x : bit_int w), 0 ≤ unsigned x ∧ unsigned x < two_p (size x) := by
  intro w x; exact Zsize_interval_1 _ (unsigned_range x).1

theorem size_interval_2 : ∀ {w : Positive} (x : bit_int w), ∀ n : Int, 0 ≤ n → (0 ≤ unsigned x ∧ unsigned x < two_p n) → n ≥ size x := by
  intro w x; exact Zsize_interval_2 (unsigned x)

theorem size_and : ∀ {w : Positive} (a b : bit_int w), size (and a b) ≤ min (size a) (size b) := by
  intro w a b
  have ha := size_range a
  have hb := size_range b
  apply bits_size_3 _ _ (by omega)
  intro i hi
  rw [bits_and _ _ _ (by omega)]
  by_cases h : size a ≤ i
  · simp [bits_size_2 _ _ h]
  · simp [bits_size_2 b i (by omega)]

theorem and_interval : ∀ {w : Positive} (a b : bit_int w),
    0 ≤ unsigned (and a b) ∧ unsigned (and a b) < two_p (min (size a) (size b)) := by
  intro w a b
  obtain ⟨h₀, h₁⟩ := size_interval_1 (and a b)
  exact ⟨h₀, Int.lt_of_lt_of_le h₁ (two_p_monotone _ _ ⟨(size_range _).1, size_and a b⟩)⟩

theorem size_or : ∀ {w : Positive} (a b : bit_int w), size (or a b) = max (size a) (size b) := by
  intro w a b
  have ha := size_range a
  have hb := size_range b
  apply Int.le_antisymm
  · apply bits_size_3 _ _ (by omega)
    intro i hi
    rw [bits_or _ _ _ (by omega), bits_size_2 a i (by omega), bits_size_2 b i (by omega)] <;> rfl
  · apply Int.max_le.mpr; constructor <;> apply Zsize_monotone _ _
    · refine ⟨(unsigned_range a).1, bits_le _ _ ?_⟩
      intro i hi h; simp [bits_or _ _ _ hi, h]
    · refine ⟨(unsigned_range b).1, bits_le _ _ ?_⟩
      intro i hi h; simp [bits_or _ _ _ hi, h]

theorem or_interval : ∀ {w : Positive} (a b : bit_int w),
    0 ≤ unsigned (or a b) ∧ unsigned (or a b) < two_p (max (size a) (size b)) := by
  intro w a b; rw [← size_or]; exact size_interval_1 _

theorem size_xor : ∀ {w : Positive} (a b : bit_int w), size (xor a b) ≤ max (size a) (size b) := by
  intro w a b
  have ha := size_range a
  have hb := size_range b
  apply bits_size_3 _ _ (by omega)
  intro i hi
  rw [bits_xor _ _ _ (by omega), bits_size_2 a i (by omega), bits_size_2 b i (by omega)] <;> rfl

theorem xor_interval : ∀ {w : Positive} (a b : bit_int w),
    0 ≤ unsigned (xor a b) ∧ unsigned (xor a b) < two_p (max (size a) (size b)) := by
  intro w a b
  obtain ⟨h₀, h₁⟩ := size_interval_1 (xor a b)
  exact ⟨h₀, Int.lt_of_lt_of_le h₁ (two_p_monotone _ _ ⟨(size_range _).1, size_xor a b⟩)⟩

theorem bits_loword : ∀ (n : bit_int w64) (i : Int), (0 ≤ i ∧ i < 32) → testbit (loword n) i = testbit n i := by
  intro n i hi; exact testbit_repr _ _ hi

theorem bits_hiword : ∀ (n : bit_int w64) (i : Int), (0 ≤ i ∧ i < 32) → testbit (hiword n) i = testbit n (i + 32) := by
  intro n i hi
  rw [hiword, @testbit_repr w32 _ _ hi]
  change testbit (shru n (repr 32)) i = _
  have h : 0 ≤ i ∧ i < @zwordsize w64 := by change 0 ≤ i ∧ i < 64; omega
  rw [bits_shru _ _ _ h]
  change chooseSide (zlt (i+32) 64) (testbit n (i+32)) false = _
  exact zlt_true _ _ _ _ _ (by omega)

theorem bits_ofwords : ∀ (hi lo : bit_int w32) (i : Int), (0 ≤ i ∧ i < 64) →
    testbit (ofwords hi lo) i = chooseSide (zlt i 32) (testbit lo i) (testbit hi (i - 32)) := by
  intro hi lo i h
  rw [ofwords, bits_or _ _ _ h, bits_shl _ _ _ h, @testbit_repr w64 (unsigned lo) i h]
  change (chooseSide (zlt i 32) false (testbit (@repr w64 (unsigned hi)) (i-32)) ||
    testbit lo i) = _
  by_cases small : i < 32
  · simp only [zlt_true _ _ _ _ _ small, Bool.false_or]
  · have ge : i ≥ 32 := by omega
    rw [zlt_false _ _ _ _ _ ge, zlt_false _ _ _ _ _ ge, bits_above lo i ge, Bool.or_false]
    apply testbit_repr
    change 0 ≤ i - 32 ∧ i - 32 < 64; omega

theorem lo_ofwords : ∀ (hi lo : bit_int w32), loword (ofwords hi lo) = lo := by
  intro hi lo; apply same_bits_eq; intro i h
  change 0 ≤ i ∧ i < 32 at h
  rw [bits_loword _ _ h, bits_ofwords _ _ _ (by omega), zlt_true _ _ _ _ _ h.2]

theorem hi_ofwords : ∀ (hi lo : bit_int w32), hiword (ofwords hi lo) = hi := by
  intro hi lo; apply same_bits_eq; intro i h
  change 0 ≤ i ∧ i < 32 at h
  rw [bits_hiword _ _ h, bits_ofwords _ _ _ (by omega), zlt_false _ _ _ _ _ (by omega)] <;> simp

theorem ofwords_recompose : ∀ (n : bit_int w64), ofwords (hiword n) (loword n) = n := by
  intro n; apply same_bits_eq; intro i h
  change 0 ≤ i ∧ i < 64 at h
  rw [bits_ofwords _ _ _ h]
  by_cases small : i < 32
  · rw [zlt_true _ _ _ _ _ small, bits_loword _ _ ⟨h.1, small⟩]
  · rw [zlt_false _ _ _ _ _ (by omega), bits_hiword _ _ (by omega), sub_add_cancel]

private theorem widenUnsigned (x : bit_int w32) : unsigned (@repr w64 (unsigned x)) = unsigned x := by
  apply unsigned_repr
  have h := unsigned_range x
  change 0 ≤ unsigned x ∧ unsigned x < 4294967296 at h
  change 0 ≤ unsigned x ∧ unsigned x ≤ 18446744073709551615
  omega

theorem ofwords_add : ∀ (lo hi : bit_int w32), ofwords hi lo = repr (unsigned hi * two_p 32 + unsigned lo) := by
  intro lo hi
  rw [ofwords, shifted_or_is_add _ _ _ (by decide) (by
    rw [widenUnsigned]; exact (unsigned_range lo).2), widenUnsigned, widenUnsigned]

theorem ofwords_add' : ∀ (lo hi : bit_int w32), unsigned (ofwords hi lo) = unsigned hi * two_p 32 + unsigned lo := by
  intro lo hi; rw [ofwords_add]; apply unsigned_repr
  have hlo := unsigned_range lo
  have hhi := unsigned_range hi
  change 0 ≤ unsigned lo ∧ unsigned lo < 4294967296 at hlo
  change 0 ≤ unsigned hi ∧ unsigned hi < 4294967296 at hhi
  change 0 ≤ unsigned hi * 4294967296 + unsigned lo ∧
    unsigned hi * 4294967296 + unsigned lo ≤ 18446744073709551615
  omega

theorem eqm_mul_2p32 : ∀ (x y : Int), @eqm w32 x y → @eqm w64 (x * two_p 32) (y * two_p 32) := by
  rintro x y ⟨k, h⟩
  refine ⟨k, ?_⟩
  change x = k * 4294967296 + y at h
  change x * 4294967296 = k * 18446744073709551616 + y * 4294967296
  omega

theorem ofwords_add'' : ∀ (lo hi : bit_int w32), signed (ofwords hi lo) = signed hi * two_p 32 + unsigned lo := by
  intro lo hi
  have hlo := unsigned_range lo
  change 0 ≤ unsigned lo ∧ unsigned lo < 4294967296 at hlo
  simp only [signed, ofwords_add']
  change (if unsigned hi * 4294967296 + unsigned lo < 9223372036854775808 then
    unsigned hi * 4294967296 + unsigned lo else
    unsigned hi * 4294967296 + unsigned lo - 18446744073709551616) =
    (if unsigned hi < 2147483648 then unsigned hi else unsigned hi - 4294967296) *
      4294967296 + unsigned lo
  split <;> split <;> omega

end Vellvm.Numeric.Integers
