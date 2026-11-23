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
import Mathlib.Data.Nat.Bitwise

namespace Vellvm.Numeric.Floats

open IEEE754_extra Integers
open Flocq hiding signed

private theorem signed32_range (x : bit_int w32) : -2147483648 ≤ signed x ∧ signed x ≤ 2147483647 :=
  signed_range x

private theorem unsigned32_range (x : bit_int w32) : 0 ≤ unsigned x ∧ unsigned x ≤ 4294967295 :=
  unsigned_range_2 x

private theorem representable_signed32 (x : bit_int w32) : integer_representable 53 1024 (signed x) := by
  apply IEEE754_extra.integer_representable_n _ _ (by decide) (by decide)
  change -9007199254740992 ≤ _ ∧ _ ≤ 9007199254740992
  have := signed32_range x
  omega

private theorem representable_unsigned32 (x : bit_int w32) : integer_representable 53 1024 (unsigned x) := by
  apply IEEE754_extra.integer_representable_n _ _ (by decide) (by decide)
  change -9007199254740992 ≤ _ ∧ _ ≤ 9007199254740992
  have := unsigned32_range x
  omega

private theorem split_at_sign (x : bit_int w32) : unsigned x =
    signed (Integers.and x (Integers.repr 2147483647)) - signed (Integers.and x (Integers.repr 2147483648)) := by
  let n := x.bits.toNat
  have hn : n < 4294967296 := x.bits.isLt
  have lo : unsigned (Integers.and x (Integers.repr 2147483647)) = (n % 2147483648 : Nat) := by
    unfold unsigned intval Integers.and
    rw [BitVec.toNat_and]
    exact congrArg Int.ofNat (Nat.and_two_pow_sub_one_eq_mod n 31)
  have hi : unsigned (Integers.and x (Integers.repr 2147483648)) =
      if n / 2147483648 % 2 = 1 then 2147483648 else 0 := by
    unfold unsigned intval Integers.and
    rw [BitVec.toNat_and]
    change ((n &&& 2^31 : Nat) : Int) = _
    rw [Nat.and_two_pow, Nat.testBit_eq_decide_div_mod_eq]
    by_cases h : n / 2147483648 % 2 = 1 <;> simp [show (2:Nat)^31 = 2147483648 by decide, h]
  simp only [signed, lo, hi]
  change (n : Int) = (if _ < (2147483648 : Int) then _ else _ - 4294967296) -
    (if _ < (2147483648 : Int) then _ else _ - 4294967296)
  split_ifs <;> omega

private theorem sticky_half (x : bit_int w64) :
    signed (Integers.or (shru x one) (Integers.and x one)) * 2 = int_round_odd (unsigned x) 1 := by
  let n := x.bits.toNat
  have hn : n < 18446744073709551616 := x.bits.isLt
  let q := n / 2 ||| n % 2
  have hq : unsigned (Integers.or (shru x one) (Integers.and x one)) = (q : Int) := by
    unfold unsigned intval Integers.or shru Integers.and
    rw [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_ushiftRight]
    change ((n >>> 1 ||| n &&& 1 : Nat) : Int) = _
    rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  have div : q / 2 = n / 2 / 2 := by
    rw [show q / 2 = n / 2 / 2 ||| n % 2 / 2 from Nat.or_div_two, show n % 2 / 2 = 0 by omega,
      Nat.or_zero]
  have rem : q % 2 = n / 2 % 2 ||| n % 2 := by simpa [q] using (Nat.or_mod_two (a := n/2) (b := n%2))
  have qlt : (q : Int) < @half_modulus w64 := by change (q : Int) < 9223372036854775808; omega
  simp only [signed, hq, qlt, ↓reduceIte]
  change (q : Int) * 2 = (if (n : Int) % 2 = 0 ∨ (n : Int) / 2 % 2 = 1
    then (n : Int) / 2 else (n : Int) / 2 + 1) * 2
  rcases (show n % 2 = 0 ∨ n % 2 = 1 by omega) with h | h <;>
    rcases (show n / 2 % 2 = 0 ∨ n / 2 % 2 = 1 by omega) with h' | h' <;>
    simp only [h, h', Nat.reduceOr] at rem <;> split_ifs <;> omega

private theorem finite_compare_lt {x y : binary_float 53 1024} (hx : is_finite x = true)
    (hy : is_finite y = true) : Bcompare x y = some .lt ↔ B2R x < B2R y := by
  have h : Bcompare x y = some (Ord.compare (B2Q x) (B2Q y)) := by
    cases x <;> cases y <;> first | rfl | contradiction
  rw [h, Option.some.injEq, ← cast_B2Q x, ← cast_B2Q y, Rat.cast_lt]
  exact Std.compare_eq_lt

namespace Float

private theorem unsigned_half32 : unsigned ox8000_0000 = @half_modulus w32 :=
  unsigned_repr _ (by decide)

private theorem unsigned_half64 :
    unsigned (@Integers.repr w64 (@half_modulus w64)) = @half_modulus w64 :=
  unsigned_repr _ (by decide)

theorem of_intu_of_int_1 (x : bit_int w32) (h : ltu x ox8000_0000 = true) :
    of_intu x = of_int x := by
  rw [ltu, unsigned_half32] at h
  simp only [of_intu, of_int, signed, of_decide_eq_true h, ↓reduceIte]

theorem of_intu_of_int_2 (x : bit_int w32) (h : ltu x ox8000_0000 = false) :
    of_intu x = add (of_int (Integers.sub x ox8000_0000)) (of_intu ox8000_0000) := by
  rw [ltu, unsigned_half32] at h
  have hx := unsigned32_range x
  have hlow : ¬ unsigned x < 2147483648 := of_decide_eq_false h
  unfold add of_int of_intu
  rw [BofZ_plus _ _ _ _ _ _ _ (representable_signed32 _) (representable_unsigned32 _)]
  apply congrArg
  rw [Integers.sub, unsigned_half32]
  change unsigned x = signed (@Integers.repr w32 (unsigned x - 2147483648)) + 2147483648
  rw [signed_repr _ (by change -2147483648 ≤ _ ∧ _ ≤ 2147483647; omega)]
  omega

theorem of_intu_of_int_3 (x : bit_int w32) : of_intu x =
    sub (of_int (Integers.and x ox7FFF_FFFF)) (of_int (Integers.and x ox8000_0000)) := by
  unfold of_intu sub of_int
  rw [BofZ_minus _ _ _ _ _ _ _ (representable_signed32 _) (representable_signed32 _)]
  exact congrArg _ (split_at_sign x)

private theorem finite_of_integer {x : float} {z : Int} (hz : ZofB 53 1024 x = some z) :
    is_finite x = true := by
  cases h : is_finite x <;> simp_all [ZofB]

private theorem cmp_threshold {x : float} (hx : is_finite x = true) :
    cmp Clt x (of_intu ox8000_0000) = true ↔ B2R x < ((2147483648 : Int) : ℝ) := by
  have h := BofZ_exact 53 1024 (by decide) (by decide) 2147483648 (by decide)
  change (Bcompare x (of_intu ox8000_0000) == some .lt) = true ↔ _
  rw [beq_iff_eq, finite_compare_lt hx (show is_finite (of_intu ox8000_0000) = true from h.2.1)]
  exact Iff.of_eq (congrArg (B2R x < ·) h.1)

theorem to_intu_to_int_1 (x : float) (n : bit_int w32) (hlt : cmp Clt x (of_intu ox8000_0000) = true)
    (hn : to_intu x = some n) : to_int x = some n := by
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp hn
  obtain ⟨hz₀, _, hv⟩ := ZofB_range_inversion _ _ _ _ _ _ hz
  have hx := (cmp_threshold (finite_of_integer hv)).mp hlt
  have hu : z < 2147483648 := by
    by_cases h : 0 < z
    · have := (ZofB_range_pos _ _ (by decide) (by decide) _ _ hv h).1.trans_lt hx
      exact_mod_cast this
    · omega
  have hr : @min_signed w32 ≤ z ∧ z ≤ @max_signed w32 := by
    change -2147483648 ≤ z ∧ z ≤ 2147483647; omega
  simp [to_int, ZofB_range, hv, hr]
  exact hu

theorem to_intu_to_int_2 (x : float) (n : bit_int w32) (hge : cmp Clt x (of_intu ox8000_0000) = false)
    (hn : to_intu x = some n) : to_int (sub x (of_intu ox8000_0000)) = some (Integers.sub n ox8000_0000) := by
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp hn
  obtain ⟨hl, hu, hv⟩ := ZofB_range_inversion _ _ _ _ _ _ hz
  have hx : ((2147483648 : Int) : ℝ) ≤ B2R x := by
    apply le_of_not_gt
    intro h
    have := (cmp_threshold (finite_of_integer hv)).mpr h
    simp_all
  have hsub := ZofB_range_minus 53 1024 (by decide) (by decide) binop_nan .mode_NE
    x z 2147483648 hz (by decide) hx
  change ZofB_range 53 1024 (sub x (of_intu ox8000_0000)) (@min_signed w32) (@max_signed w32) =
    some (z - unsigned ox8000_0000) at hsub
  simp [to_int, hsub, Integers.sub, unsigned_repr z ⟨hl, hu⟩]

theorem of_longu_of_long_1 (x : bit_int w64) (h : ltu x (Integers.repr (@half_modulus w64)) = true) :
    of_longu x = of_long x := by
  rw [ltu, unsigned_half64] at h
  simp only [of_longu, of_long, signed, of_decide_eq_true h, ↓reduceIte]

theorem of_longu_of_long_2 (x : bit_int w64) (h : ltu x (Integers.repr (@half_modulus w64)) = false) :
    of_longu x = mul (of_long (Integers.or (shru x one) (Integers.and x one))) (of_int (Integers.repr 2)) := by
  let q := Integers.or (shru x one) (Integers.and x one)
  rw [ltu, unsigned_half64] at h
  have hx : 9223372036854775808 ≤ unsigned x := le_of_not_gt (of_decide_eq_false h)
  have hu : unsigned x < 18446744073709551616 := (unsigned_range x).2
  have heq : signed q * 2 = int_round_odd (unsigned x) 1 := sticky_half x
  have hround := int_round_odd_le 1 9223372036854775808 (unsigned x) (by decide) hx
  change 9223372036854775808 ≤ int_round_odd (unsigned x) 1 at hround
  rw [← heq] at hround
  have hqu : signed q ≤ 9223372036854775807 := (signed_range q).2
  have cap : (18446744073709551616 : Int) ≤ pow2 1024 - pow2 (1024 - 53) := by
    rw [int_upper_bound_eq 53 1024 (by decide) (by decide)]
    exact (pow2_mono (i := 64) (by decide) (by decide : (64 : Int) ≤ 1024 - 53)).trans
      (le_mul_of_one_le_left (pow2_pos (by decide)).le (by decide))
  unfold of_longu mul of_long of_int
  rw [@signed_repr w32 2 (by decide)]
  change BofZ 53 1024 _ _ (unsigned x) = Bmult 53 1024 _ _ binop_nan .mode_NE
    (BofZ 53 1024 _ _ (signed q)) (BofZ 53 1024 _ _ (pow2 1))
  rw [BofZ_mult_2p 53 1024 (by decide) (by decide) binop_nan (signed q) 1
    ((abs_le.mpr ⟨by omega, by omega⟩).trans cap)
    (by rw [abs_of_nonneg (by omega)]; change 9007199254740992 ≤ signed q; omega) (by decide)]
  change BofZ 53 1024 _ _ _ = BofZ 53 1024 _ _ (signed q * 2)
  rw [heq]
  exact BofZ_round_odd 53 1024 (by decide) (by decide) (unsigned x) 1 (by decide)
    ((abs_le.mpr ⟨by omega, by omega⟩).trans cap)
    (by decide) (by rw [abs_of_nonneg (by omega)]; change 36028797018963968 ≤ unsigned x; omega)

theorem ZofB_range_widen (f : float) (n min₁ max₁ min₂ max₂ : Int)
    (h : ZofB_range 53 1024 f min₁ max₁ = some n) (hl : min₂ ≤ min₁) (hu : max₁ ≤ max₂) :
    ZofB_range 53 1024 f min₂ max₂ = some n := by
  obtain ⟨a, b, hz⟩ := ZofB_range_inversion _ _ _ _ _ _ h
  simp [ZofB_range, hz, hl.trans a, b.trans hu]

private theorem widen_word {f : float} {n : bit_int w32} {lo hi lo' hi' : Int}
    {readWord : bit_int w32 → Int} (inv : ∀ z, lo ≤ z ∧ z ≤ hi → readWord (Integers.repr z) = z)
    (hl : lo' ≤ lo) (hu : hi ≤ hi')
    (hn : (ZofB_range 53 1024 f lo hi).map (@Integers.repr w32) = some n) :
    (ZofB_range 53 1024 f lo' hi').map (@Integers.repr w64) = some (Integers.repr (readWord n)) := by
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp hn
  obtain ⟨a, b, _⟩ := ZofB_range_inversion _ _ _ _ _ _ hz
  rw [ZofB_range_widen f _ _ _ _ _ hz hl hu, inv z ⟨a, b⟩]
  rfl

theorem to_int_to_long (f : float) (n : bit_int w32) :
    to_int f = some n → to_long f = some (Integers.repr (signed n)) :=
  widen_word signed_repr (by decide) (by decide)

theorem to_intu_to_longu (f : float) (n : bit_int w32) :
    to_intu f = some n → to_longu f = some (Integers.repr (unsigned n)) :=
  widen_word unsigned_repr (by decide) (by decide)

theorem to_intu_to_long (f : float) (n : bit_int w32) :
    to_intu f = some n → to_long f = some (Integers.repr (unsigned n)) :=
  widen_word unsigned_repr (by decide) (by decide)

theorem of_int_of_long (n : bit_int w32) : of_int n = of_long (Integers.repr (signed n)) := by
  unfold of_int of_long
  rw [signed_repr _ (by change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
                        have := signed32_range n; omega)]

theorem of_intu_of_longu (n : bit_int w32) : of_intu n = of_longu (Integers.repr (unsigned n)) := by
  unfold of_intu of_longu
  rw [unsigned_repr _ (by change 0 ≤ _ ∧ _ ≤ 18446744073709551615
                          have := unsigned32_range n; omega)]

theorem of_intu_of_long (n : bit_int w32) : of_intu n = of_long (Integers.repr (unsigned n)) := by
  unfold of_intu of_long
  rw [signed_repr _ (by change -9223372036854775808 ≤ _ ∧ _ ≤ 9223372036854775807
                        have := unsigned32_range n; omega)]

end Float

namespace Float32

theorem of_int_double (n : bit_int w32) : of_int n = of_double (Float.of_int n) :=
  (Bconv_BofZ 53 1024 24 128 _ _ _ _ _ _ (representable_signed32 n)).symm

theorem of_intu_double (n : bit_int w32) : of_intu n = of_double (Float.of_intu n) :=
  (Bconv_BofZ 53 1024 24 128 _ _ _ _ _ _ (representable_unsigned32 n)).symm

private theorem to_double_range {w : Positive} (f : float32) (lo hi : Int) (n : bit_int w)
    (h : (ZofB_range 24 128 f lo hi).map (@Integers.repr w) = some n) :
    (ZofB_range 53 1024 (to_double f) lo hi).map (@Integers.repr w) = some n := by
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.mp h
  apply Option.map_eq_some_iff.mpr
  exact ⟨z, ZofB_range_Bconv 24 128 53 1024 (by decide) _ _ _ _ _ _ (by decide) (by decide)
    le_rfl le_rfl Float.of_single_nan .mode_NE _ _ hz, rfl⟩

theorem to_int_double (f : float32) (n : bit_int w32) :
    to_int f = some n → Float.to_int (to_double f) = some n := to_double_range f _ _ n

theorem to_intu_double (f : float32) (n : bit_int w32) :
    to_intu f = some n → Float.to_intu (to_double f) = some n := to_double_range f _ _ n

theorem to_long_double (f : float32) (n : bit_int w64) :
    to_long f = some n → Float.to_long (to_double f) = some n := to_double_range f _ _ n

theorem to_longu_double (f : float32) (n : bit_int w64) :
    to_longu f = some n → Float.to_longu (to_double f) = some n := to_double_range f _ _ n

theorem of_longu_double_1 (n : bit_int w64) (h : unsigned n ≤ 2^53) :
    of_longu n = of_double (Float.of_longu n) := by
  symm
  apply Bconv_BofZ
  apply Floats.integer_representable_n
  have := (unsigned_range n).1
  omega

theorem of_long_double_1 (n : bit_int w64) (h : |signed n| ≤ 2^53) :
    of_long n = of_double (Float.of_long n) :=
  (Bconv_BofZ 53 1024 24 128 _ _ _ _ _ _ (Floats.integer_representable_n _ (abs_le.mp h))).symm

end Float32

end Vellvm.Numeric.Floats
