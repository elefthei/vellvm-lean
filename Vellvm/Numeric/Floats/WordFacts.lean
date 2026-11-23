/-
The Compcert verified compiler.
Xavier Leroy and Jacques-Henri Jourdan, INRIA Paris-Rocquencourt.
Copyright Institut National de Recherche en Informatique et en Automatique. All rights
reserved. This file is distributed under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation, either version 2.1 of the License,
or (at your option) any later version. This file is also distributed under the terms
of the INRIA Non-Commercial License Agreement.
-/
import Vellvm.Numeric.Floats.Basic
import Vellvm.Numeric.Integers.ComparisonWords

namespace Vellvm.Numeric.Floats.Float
open Flocq IEEE754_extra Rocqlib
open Integers (bit_int w32 w64 unsigned loword hiword ofwords)

private abbrev intFloat := BofZ 53 1024 (by decide) (by decide)
private abbrev fits := integer_representable 53 1024

private theorem word_range (x : bit_int w32) : 0 ≤ unsigned x ∧ unsigned x < 4294967296 :=
  Integers.unsigned_range x

private theorem signed_word_range (x : bit_int w32) :
    -2147483648 ≤ Integers.signed x ∧ Integers.signed x ≤ 2147483647 :=
  Integers.signed_range x

private theorem fits_small {n : Int} (h : -9007199254740992 ≤ n ∧ n ≤ 9007199254740992) :
    fits n := integer_representable_n n h

private theorem fits_scaled {n : Int} (h : -9007199254740992 < n ∧ n < 9007199254740992) :
    fits (n * 2^32) :=
  integer_representable_n2p 53 1024 (by decide) (by decide) n 32 h (by decide) (by decide)

private theorem fits_low (x : bit_int w32) : fits (2^52 + unsigned x) := by
  have := word_range x
  apply fits_small
  change -9007199254740992 ≤ 4503599627370496 + unsigned x ∧
    4503599627370496 + unsigned x ≤ 9007199254740992
  omega

private theorem fits_high (x : bit_int w32) : fits (2^84 + unsigned x * 2^32) := by
  rw [show (2^84 + unsigned x * 2^32) = (2^52 + unsigned x) * 2^32 by ring]
  have := word_range x
  apply fits_scaled
  change -9007199254740992 < 4503599627370496 + unsigned x ∧
    4503599627370496 + unsigned x < 9007199254740992
  omega

private theorem split_word (hi lo : bit_int w32) (k : Int)
    (hhi : unsigned hi * two_p 32 = k * 2^52) (hk : 0 ≤ k ∧ k < 2^11) :
    split_bits 52 11 (unsigned (ofwords hi lo)) = ((false, unsigned lo), k) := by
  rw [Integers.ofwords_add', hhi]
  have h : k * 2^52 + unsigned lo = join_bits 52 11 false (unsigned lo) k := by
    simp [join_bits, add_comm]
  rw [h]
  refine split_join_bits 52 11 false (unsigned lo) k ?_ hk
  have := word_range lo
  change 0 ≤ unsigned lo ∧ unsigned lo < 4503599627370496
  omega

theorem split_bits_or (x : bit_int w32) :
    split_bits 52 11 (unsigned (ofwords ox4330_0000 x)) = ((false, unsigned x), 1075) :=
  split_word _ _ _ (by decide) (by decide)

theorem split_bits_or' (x : bit_int w32) :
    split_bits 52 11 (unsigned (ofwords ox4530_0000 x)) = ((false, unsigned x), 1107) :=
  split_word _ _ _ (by decide) (by decide)

private theorem normal_word_value {hi lo : bit_int w32} {k : Int}
    (h : split_bits 52 11 (unsigned (ofwords hi lo)) = ((false, unsigned lo), k))
    (hk : 0 < k ∧ k < 2047) :
    B2R (from_words hi lo) = ((unsigned lo : ℝ) + 2^52) * (2 : ℝ) ^ (k - 1075) ∧
    is_finite (from_words hi lo) = true ∧ Bsign (from_words hi lo) = false := by
  obtain ⟨v, hv, hm, hf⟩ := b64_of_bits_normal h hk
  unfold from_words of_bits
  rw [hf]
  refine ⟨?_, rfl, rfl⟩
  change (v.val : ℝ) * _ = _
  have hm' : (v.val : ℝ) = (unsigned lo : ℝ) + 2^52 := by exact_mod_cast hm
  rw [hm']

theorem from_words_value (x : bit_int w32) :
    B2R (from_words ox4330_0000 x) = (2 : ℝ) ^ (52 : Int) + (unsigned x : ℝ) ∧
    is_finite (from_words ox4330_0000 x) = true ∧ Bsign (from_words ox4330_0000 x) = false := by
  obtain ⟨hr, hf, hs⟩ := normal_word_value (split_bits_or x) (by decide)
  refine ⟨?_, hf, hs⟩
  rw [hr]; norm_num; ring

theorem from_words_value' (x : bit_int w32) :
    B2R (from_words ox4530_0000 x) = (2 : ℝ) ^ (84 : Int) + ((unsigned x * two_p 32 : Int) : ℝ) ∧
    is_finite (from_words ox4530_0000 x) = true ∧ Bsign (from_words ox4530_0000 x) = false := by
  obtain ⟨hr, hf, hs⟩ := normal_word_value (split_bits_or' x) (by decide)
  refine ⟨?_, hf, hs⟩
  rw [hr, show two_p 32 = 4294967296 by rfl, Int.cast_mul]; norm_num; ring

private theorem eq_intFloat {f : float} {n : Int} (h : fits n) (hn : 0 ≤ n)
    (hf : is_finite f = true) (hs : Bsign f = false) (hr : B2R f = (n : ℝ)) : f = intFloat n := by
  have pos0 (x : float) (hx : is_finite x = true) (sx : Bsign x = false) :
      is_finite_pos0 53 1024 x = true := by
    cases x <;> simp_all [is_finite_pos0, is_finite, Bsign]
  obtain ⟨vr, vf, vs⟩ := BofZ_representable 53 1024 (by decide) (by decide) n h
  exact B2R_inj_pos0 53 1024 _ _ (pos0 _ hf hs)
    (pos0 _ vf (by simpa [not_lt.mpr hn] using vs)) (hr.trans vr.symm)

theorem from_words_eq (x : bit_int w32) : from_words ox4330_0000 x =
    BofZ 53 1024 (by decide) (by decide) (2^52 + unsigned x) := by
  obtain ⟨hr, hf, hs⟩ := from_words_value x
  have hx := (word_range x).1
  apply eq_intFloat (fits_low x) (by positivity) hf hs
  rw [hr]; norm_num [Int.cast_add, Int.cast_pow]

theorem from_words_eq' (x : bit_int w32) : from_words ox4530_0000 x =
    BofZ 53 1024 (by decide) (by decide) (2^84 + unsigned x * 2^32) := by
  obtain ⟨hr, hf, hs⟩ := from_words_value' x
  have hx := (word_range x).1
  apply eq_intFloat (fits_high x) (by positivity) hf hs
  rw [hr, show two_p 32 = (2 : Int)^32 by rfl]; norm_num [Int.cast_add, Int.cast_pow]

private theorem sub_low_words (x y : bit_int w32) :
    sub (from_words ox4330_0000 x) (from_words ox4330_0000 y) = intFloat (unsigned x - unsigned y) := by
  rw [from_words_eq x, from_words_eq y, sub,
    BofZ_minus _ _ _ _ _ _ _ (fits_low x) (fits_low y)]
  apply congrArg intFloat
  ring

theorem of_intu_from_words (x : bit_int w32) :
    of_intu x = sub (from_words ox4330_0000 x) (from_words ox4330_0000 (@Integers.zero w32)) := by
  simp only [sub_low_words, Integers.unsigned_zero, sub_zero, of_intu, intFloat]

theorem ox8000_0000_signed_unsigned (x : bit_int w32) :
    unsigned (Integers.add x ox8000_0000) = Integers.signed x + @Integers.half_modulus w32 := by
  have := word_range x
  rw [Integers.add, Integers.unsigned_repr_eq,
    Int.fmod_eq_emod_of_nonneg _ (show 0 ≤ @Integers.modulus w32 by decide)]
  change (unsigned x + 2147483648) % 4294967296 =
    (if unsigned x < 2147483648 then unsigned x else unsigned x - 4294967296) + 2147483648
  split <;> omega

theorem of_int_from_words (x : bit_int w32) :
    of_int x = sub (from_words ox4330_0000 (Integers.add x ox8000_0000))
      (from_words ox4330_0000 ox8000_0000) := by
  rw [sub_low_words, ox8000_0000_signed_unsigned]
  apply congrArg intFloat
  change Integers.signed x = Integers.signed x + 2147483648 - 2147483648
  omega

private theorem unsigned_parts (l : bit_int w64) :
    unsigned l = unsigned (hiword l) * 2^32 + unsigned (loword l) := by
  simpa only [Integers.ofwords_recompose, show two_p 32 = (2 : Int)^32 by rfl] using
    Integers.ofwords_add' (loword l) (hiword l)

private theorem signed_parts (l : bit_int w64) :
    Integers.signed l = Integers.signed (hiword l) * 2^32 + unsigned (loword l) := by
  simpa only [Integers.ofwords_recompose, show two_p 32 = (2 : Int)^32 by rfl] using
    Integers.ofwords_add'' (loword l) (hiword l)

private theorem add_biased_words (hi bias lo : bit_int w32) :
    add (sub (from_words ox4530_0000 hi) (from_words ox4530_0000 bias))
        (from_words ox4330_0000 lo) =
    intFloat ((unsigned hi - unsigned bias) * 2^32 + (2^52 + unsigned lo)) := by
  rw [from_words_eq' hi, from_words_eq' bias, from_words_eq lo, sub,
    BofZ_minus _ _ _ _ _ _ _ (fits_high hi) (fits_high bias)]
  rw [show (2^84 + unsigned hi * 2^32) - (2^84 + unsigned bias * 2^32) =
    (unsigned hi - unsigned bias) * 2^32 by ring]
  have hh := word_range hi
  have hb := word_range bias
  exact BofZ_plus _ _ _ _ _ _ _ (fits_scaled (by omega)) (fits_low lo)

theorem of_longu_from_words (l : bit_int w64) : of_longu l =
    add (sub (from_words ox4530_0000 (hiword l))
             (from_words ox4530_0000 (@Integers.repr w32 (two_p 20))))
        (from_words ox4330_0000 (loword l)) := by
  rw [add_biased_words]
  apply congrArg intFloat
  rw [unsigned_parts]
  change unsigned (hiword l) * 2^32 + unsigned (loword l) =
    (unsigned (hiword l) - 1048576) * 2^32 + (2^52 + unsigned (loword l))
  ring

theorem of_long_from_words (l : bit_int w64) : of_long l =
    add (sub (from_words ox4530_0000 (Integers.add (hiword l) ox8000_0000))
             (from_words ox4530_0000 (@Integers.repr w32 (two_p 20 + two_p 31))))
        (from_words ox4330_0000 (loword l)) := by
  rw [add_biased_words, ox8000_0000_signed_unsigned]
  apply congrArg intFloat
  rw [signed_parts]
  change Integers.signed (hiword l) * 2^32 + unsigned (loword l) =
    (Integers.signed (hiword l) + 2147483648 - 2148532224) * 2^32 + (2^52 + unsigned (loword l))
  ring

private theorem mul_add_parts (hi : Int) (lo : bit_int w32) (h : -4294967296 ≤ hi ∧ hi ≤ 4294967296) :
    add (mul (intFloat hi) (intFloat (2^32))) (intFloat (unsigned lo)) =
    intFloat (hi * 2^32 + unsigned lo) := by
  have hl := word_range lo
  rw [mul, BofZ_mult 53 1024 (by decide) (by decide) binop_nan hi (2^32)
    (fits_small (by omega)) (fits_small (by decide)) (by decide)]
  exact BofZ_plus 53 1024 (by decide) (by decide) binop_nan (hi * 2^32) (unsigned lo)
    (fits_scaled (by omega)) (fits_small (by omega))

theorem of_longu_decomp (l : bit_int w64) : of_longu l =
    add (mul (of_intu (hiword l)) (BofZ 53 1024 (by decide) (by decide) (2^32)))
        (of_intu (loword l)) := by
  have hh := word_range (hiword l)
  exact (congrArg intFloat (unsigned_parts l)).trans
    (mul_add_parts (unsigned (hiword l)) (loword l) (by omega)).symm

theorem of_long_decomp (l : bit_int w64) : of_long l =
    add (mul (of_int (hiword l)) (BofZ 53 1024 (by decide) (by decide) (2^32)))
        (of_intu (loword l)) := by
  have hh := signed_word_range (hiword l)
  exact (congrArg intFloat (signed_parts l)).trans
    (mul_add_parts (Integers.signed (hiword l)) (loword l) (by omega)).symm

end Vellvm.Numeric.Floats.Float
