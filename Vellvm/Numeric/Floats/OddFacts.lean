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
import Vellvm.Numeric.Integers.Bitwise

namespace Vellvm.Numeric.Floats.Float32
open Flocq IEEE754_extra Rocqlib

/-- Adding the low-bit mask produces a carry precisely when a discarded bit is set. -/
theorem int_round_odd_plus (p n : Int) (hp : 0 ≤ p) : int_round_odd n p =
    Int.land (Int.lor n (Int.land n (pow2 p - 1) + (pow2 p - 1))) (-pow2 p) := by
  lift p to Nat using hp
  let d := two_power_nat p
  have hd : 0 < d := two_power_nat_pos p
  have hpow : pow2 (p : Int) = d := by simp [d, pow2, zpowNat]
  have hmask : Int.land n (d - 1) = n % d := by
    change Zbits.Zzero_ext (p : Int) n = n % d
    rw [Zbits.Zzero_ext_mod _ _ (by omega)]
    exact Int.fmod_eq_emod_of_nonneg _ hd.le
  rw [hpow, hmask]
  let carry := n % d + (d - 1)
  have hlo := Int.emod_nonneg n hd.ne'
  have hhi := Int.emod_lt_of_pos n hd
  have hnext : two_power_nat (p + 1) = 2 * d := by simp [d, two_power_nat, pow_succ, mul_comm]
  have hc : 0 ≤ carry ∧ carry < two_power_nat (p + 1) := by rw [hnext]; dsimp only [carry]; omega
  have negBit (i : Int) (hi : 0 ≤ i) :
      (-d).testBit i.toNat = decide (↑p ≤ i) := by
    have h := Zbits.Ztestbit_neg_two_p (p : Int) i (by omega) hi
    change Zbits.testbit (-d) i = _ at h
    by_cases hlt : i < (p : Int)
    · simpa [Zbits.testbit, hi, zlt, chooseSide, hlt, not_le.mpr hlt] using h
    · simpa [Zbits.testbit, hi, zlt, chooseSide, hlt, le_of_not_gt hlt] using h
  have cp := Zbits.Zsign_bit p carry hc
  change Zbits.testbit carry (p : Int) = chooseSide (zlt carry d) false true at cp
  have cz : carry < d ↔ n % d = 0 := by dsimp [carry]; omega
  apply int_round_odd_bits _ _ _ (by omega)
  · intro i hi
    simp [testbit, hi.1, Int.testBit_land, negBit i hi.1, not_le.mpr hi.2]
  · rw [hpow]
    change testbit (Int.land (Int.lor n carry) (-d)) (p : Int) = _
    have atMask := negBit (p : Int) (by omega)
    simp only [Int.toNat_natCast, le_refl, decide_true] at atMask
    by_cases hz : n % d = 0 <;>
      simp_all [testbit, Zbits.testbit, Int.testBit_land, Int.testBit_lor, zlt, chooseSide]
  · intro i hi
    have hi' : 0 ≤ i := by omega
    have ca := Zbits.Ztestbit_above (p + 1) carry i hc (by omega)
    change testbit (Int.land (Int.lor n carry) (-d)) i = testbit n i
    simpa [testbit, Zbits.testbit, hi', Int.testBit_land, Int.testBit_lor, negBit i hi', hi.le]
      using congrArg (fun b ↦ n.testBit i.toNat || b) ca

private abbrev maskedInteger (n : Int) := Int.land (Int.lor n (Int.land n 2047 + 2047)) (-2048)

private theorem masked_eq_odd (n : Int) : maskedInteger n = int_round_odd n 11 :=
  (int_round_odd_plus 11 n (by decide)).symm

/-- Double precision represents the 53 retained bits before the final narrowing. -/
theorem of_long_round_odd (n : Int) (conv_nan : ConvNaN 53 1024 24 128)
    (hn : 2 ^ 36 ≤ |n| ∧ |n| < 2 ^ 64) :
    BofZ 24 128 (by decide) (by decide) n =
      Bconv 53 1024 24 128 (by decide) (by decide) conv_nan .mode_NE
        (BofZ 53 1024 (by decide) (by decide)
          (Int.land (Int.lor n (Int.land n 2047 + 2047)) (-2048))) := by
  rw [show Int.land (Int.lor n (Int.land n 2047 + 2047)) (-2048) = int_round_odd n 11
    from masked_eq_odd n]
  have hbounds := abs_lt.mp hn.2
  have hl := int_round_odd_le 11 (-(2 ^ 64)) n (by decide) hbounds.1.le
  have hu := int_round_odd_le 11 n (2 ^ 64) (by decide) hbounds.2.le
  change -(2 ^ 64) ≤ int_round_odd n 11 at hl
  change int_round_odd n 11 ≤ 2 ^ 64 at hu
  rw [Bconv_BofZ 53 1024 24 128 (by decide) (by decide) (by decide) (by decide)]
  · exact BofZ_round_odd _ _ _ _ n 11 (by decide)
      (hn.2.le.trans (by decide)) (by decide) hn.1
  · unfold int_round_odd oddInt at hl hu ⊢
    apply integer_representable_n2p_wide 53 1024 (by decide) (by decide) _ 11 _ (by decide) (by decide)
    change -9007199254740992 ≤ _ ∧ _ ≤ 9007199254740992
    change -(18446744073709551616 : Int) ≤ _ * 2048 at hl
    change _ * 2048 ≤ (18446744073709551616 : Int) at hu
    omega

open Integers (bit_int w64)

private abbrev maskedWord (n : bit_int w64) :=
  Integers.and (Integers.or n (Integers.add (Integers.and n (Integers.repr 2047))
    (Integers.repr 2047))) (Integers.repr (-2048))

private theorem maskedWord_repr (x : Int) :
    maskedWord (Integers.repr x) = Integers.repr (maskedInteger x) := by
  have land (a b : Int) : Integers.and (Integers.repr a) (Integers.repr b) =
      @Integers.repr w64 (Int.land a b) := by
    apply Integers.same_bits_eq
    intro i hi
    simp only [Integers.bits_and _ _ _ hi, Integers.testbit_repr _ _ hi,
      Zbits.testbit, hi.1, decide_true, Bool.true_and, Int.testBit_land]
  have lor (a b : Int) : Integers.or (Integers.repr a) (Integers.repr b) =
      @Integers.repr w64 (Int.lor a b) := by
    apply Integers.same_bits_eq
    intro i hi
    simp only [Integers.bits_or _ _ _ hi, Integers.testbit_repr _ _ hi,
      Zbits.testbit, hi.1, decide_true, Bool.true_and, Int.testBit_lor]
  have add (a b : Int) : Integers.add (Integers.repr a) (Integers.repr b) =
      @Integers.repr w64 (a + b) := by
    apply Integers.eqm_samerepr
    apply Integers.eqm_add <;> apply Integers.eqm_sym <;> apply Integers.eqm_unsigned_repr
  simp only [maskedWord, maskedInteger, land, lor, add]

private theorem unsigned_maskedWord (n : bit_int w64) :
    Integers.unsigned (maskedWord n) = maskedInteger (Integers.unsigned n) := by
  have hw := maskedWord_repr (Integers.unsigned n)
  rw [Integers.repr_unsigned] at hw
  rw [hw, masked_eq_odd]
  apply Integers.unsigned_repr
  obtain ⟨hl, hu⟩ := Integers.unsigned_range_2 n
  exact ⟨int_round_odd_le 11 0 _ (by decide) hl,
    (int_round_odd_le 11 _ _ (by decide) hu).trans (by decide)⟩

private theorem signed_maskedWord (n : bit_int w64) :
    Integers.signed (maskedWord n) = maskedInteger (Integers.signed n) := by
  have hw := maskedWord_repr (Integers.signed n)
  rw [Integers.repr_signed] at hw
  rw [hw, masked_eq_odd]
  apply Integers.signed_repr
  obtain ⟨hl, hu⟩ := Integers.signed_range n
  have low := int_round_odd_le 11 _ _ (by decide) hl
  have high := int_round_odd_le 11 _ _ (by decide) hu
  exact ⟨(show @Integers.min_signed w64 ≤ int_round_odd (@Integers.min_signed w64) 11
      from by decide).trans low, high.trans (by decide)⟩

theorem of_longu_double_2 (n : bit_int w64) (hn : 2 ^ 36 ≤ Integers.unsigned n) :
    of_longu n = of_double (Float.of_longu
      (Integers.and (Integers.or n (Integers.add (Integers.and n (Integers.repr 2047))
        (Integers.repr 2047))) (Integers.repr (-2048)))) := by
  change _ = of_double (BofZ 53 1024 (by decide) (by decide) (Integers.unsigned (maskedWord n)))
  rw [unsigned_maskedWord]
  exact of_long_round_odd (Integers.unsigned n) Float.to_single_nan (by
    obtain ⟨hl, hu⟩ := Integers.unsigned_range n
    rw [abs_of_nonneg hl]
    exact ⟨hn, hu⟩)

theorem of_long_double_2 (n : bit_int w64) (hn : 2 ^ 36 ≤ |Integers.signed n|) :
    of_long n = of_double (Float.of_long
      (Integers.and (Integers.or n (Integers.add (Integers.and n (Integers.repr 2047))
        (Integers.repr 2047))) (Integers.repr (-2048)))) := by
  change _ = of_double (BofZ 53 1024 (by decide) (by decide) (Integers.signed (maskedWord n)))
  rw [signed_maskedWord]
  have hs := Integers.signed_range n
  change -9223372036854775808 ≤ Integers.signed n ∧ Integers.signed n ≤ 9223372036854775807 at hs
  exact of_long_round_odd (Integers.signed n) Float.to_single_nan ⟨hn, abs_lt.mpr (by omega)⟩

end Vellvm.Numeric.Floats.Float32
