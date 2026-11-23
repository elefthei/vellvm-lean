/-
The Compcert verified compiler
Xavier Leroy, INRIA Paris-Rocquencourt

Copyright Institut National de Recherche en Informatique et en Automatique.
All rights reserved. This file is distributed under the terms of the GNU
Lesser General Public License as published by the Free Software Foundation,
either version 2.1 of the License, or (at your option) any later version.
This file is also distributed under the terms of the INRIA Non-Commercial License Agreement.
-/
module

public import Vellvm.Numeric.Integers.Basic
import Mathlib.Tactic.Ring

@[expose] public section
namespace Vellvm.Numeric.Integers
open Vellvm.Numeric.Rocqlib
variable {w : Positive}

theorem Z_one_bits_powerserie (x : Int) (hx : 0 ≤ x ∧ x < @modulus w) :
    x = powerserie (Z_one_bits (@natwordsize w) x 0) :=
  Zbits.Z_one_bits_powerserie _ _ (modulus_two_power_nat (w := w) ▸ hx)

theorem Z_one_bits_range (x i : Int) (h : i ∈ Z_one_bits (@natwordsize w) x 0) :
    0 ≤ i ∧ i < @zwordsize w := Zbits.Z_one_bits_range _ x i h

private theorem index_repr (i : Int) (h : 0 ≤ i ∧ i ≤ @zwordsize w) :
    unsigned (@repr w i) = i := unsigned_repr _ ⟨h.1, h.2.trans (@wordsize_max_unsigned w)⟩

private theorem singleton_power (n k : bit_int w) (h : is_power2 n = some k) :
    ∃ i, Z_one_bits w.val (unsigned n) 0 = [i] ∧ k = repr i := by
  cases he : Z_one_bits w.val (unsigned n) 0 with
  | nil => simp [is_power2, he] at h
  | cons i l =>
    cases l with
    | nil => exact ⟨i, rfl, (Option.some.inj (by simpa [is_power2, he] using h)).symm⟩
    | cons j l => simp [is_power2, he] at h

theorem is_power2_rng (n logn : bit_int w) (h : is_power2 n = some logn) :
    0 ≤ unsigned logn ∧ unsigned logn < @zwordsize w := by
  obtain ⟨i, he, rfl⟩ := singleton_power n logn h
  have hi := @Z_one_bits_range w (unsigned n) i (by simp [natwordsize_def, he])
  rwa [index_repr i ⟨hi.1, hi.2.le⟩]

theorem is_power2_range (n logn : bit_int w) (h : is_power2 n = some logn) :
    ltu logn iwordsize = true := by
  simpa [ltu, unsigned_repr_wordsize] using (is_power2_rng n logn h).2

theorem is_power2_correct (n logn : bit_int w) (h : is_power2 n = some logn) :
    unsigned n = two_p (unsigned logn) := by
  obtain ⟨i, he, rfl⟩ := singleton_power n logn h
  have hi := @Z_one_bits_range w (unsigned n) i (by simp [natwordsize_def, he])
  rw [index_repr i ⟨hi.1, hi.2.le⟩]
  simpa [natwordsize_def, he, powerserie, Zbits.powerserie] using
    @Z_one_bits_powerserie w (unsigned n) (unsigned_range n)

theorem two_p_range (n : Int) (hn : 0 ≤ n ∧ n < @zwordsize w) :
    0 ≤ two_p n ∧ two_p n ≤ @max_unsigned w := by
  have lo := two_p_strict n hn.1
  have hi := two_p_monotone_strict n _ hn
  rw [← modulus_power] at hi
  unfold max_unsigned; omega

theorem Z_one_bits_zero (n : Nat) (i : Int) : Z_one_bits n 0 i = [] :=
  Zbits.Z_one_bits_zero n i

theorem Z_one_bits_two_p (n : Nat) (x i : Int) (h : 0 ≤ x ∧ x < n) :
    Z_one_bits n (two_p x) i = [i+x] := Zbits.Z_one_bits_two_p n x i h

theorem is_power2_two_p (n : Int) (hn : 0 ≤ n ∧ n < @zwordsize w) :
    @is_power2 w (repr (two_p n)) = some (repr n) := by
  simp [is_power2, unsigned_repr _ (two_p_range n hn), Z_one_bits_two_p w.val n 0 hn]

theorem Zshiftl_mul_two_p (x n : Int) (hn : 0 ≤ n) : x <<< n = x * two_p n :=
  Zbits.Zshiftl_mul_two_p x n hn

private theorem shl_value (x y : bit_int w) :
    shl x y = repr (unsigned x * two_p (unsigned y)) := by
  apply bit_int.ext_bits
  change BitVec.ofNat _ (x.bits.toNat <<< y.bits.toNat) =
    BitVec.ofInt _ ((x.bits.toNat : Int) * ((2 ^ y.bits.toNat : Nat) : Int))
  rw [Nat.shiftLeft_eq, ← Int.natCast_mul, BitVec.ofInt_natCast]

theorem shl_mul_two_p (x y : bit_int w) : shl x y = mul x (repr (two_p (unsigned y))) := by
  rw [shl_value, mul]; apply eqm_samerepr
  exact eqm_mult _ _ _ _ (eqm_refl _) (eqm_unsigned_repr _)

private theorem shl_one_value (y : bit_int w) : shl one y = repr (two_p (unsigned y)) := by
  rw [shl_value, unsigned_one, one_mul]

theorem shl_mul (x y : bit_int w) : shl x y = mul x (shl one y) := by
  rw [shl_one_value, shl_mul_two_p]

theorem mul_pow2 (x n logn : bit_int w) (h : is_power2 n = some logn) : mul x n = shl x logn := by
  rw [shl_mul_two_p, ← is_power2_correct _ _ h, repr_unsigned]

theorem shifted_or_is_add (x y : bit_int w) (n : Int) (hn : 0 ≤ n ∧ n < @zwordsize w)
    (hy : unsigned y < two_p n) : or (shl x (repr n)) y = repr (unsigned x * two_p n + unsigned y) := by
  cases n with
  | negSucc n => omega
  | ofNat n =>
    have hs := congrArg Int.toNat (index_repr _ ⟨hn.1, hn.2.le⟩)
    change (@repr w n).bits.toNat = n at hs
    have hb := Int.ofNat_lt.mp hy
    apply bit_int.ext_bits
    change (x.bits <<< (@repr w n).bits.toNat) ||| y.bits =
      BitVec.ofInt _ ((x.bits.toNat : Int) * ((2^n : Nat) : Int) + (y.bits.toNat : Int))
    rw [hs, ← Int.natCast_mul, ← Int.natCast_add, BitVec.ofInt_natCast, ← Nat.shiftLeft_eq,
      Nat.shiftLeft_add_eq_or_of_lt hb, BitVec.ofNat_or]
    change _ = (x.bits <<< n) ||| BitVec.ofNat _ y.bits.toNat
    simp

theorem Zshiftr_div_two_p (x n : Int) (hn : 0 ≤ n) : x >>> n = x.fdiv (two_p n) :=
  Zbits.Zshiftr_div_two_p x n hn

theorem shru_div_two_p (x y : bit_int w) : shru x y = repr ((unsigned x).fdiv (two_p (unsigned y))) := by
  rw [← repr_unsigned (shru x y)]; apply congrArg repr
  change (((x.bits >>> y.bits.toNat).toNat : Nat) : Int) =
    (x.bits.toNat : Int).fdiv ((2^y.bits.toNat : Nat) : Int)
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Int.natCast_ediv,
    Int.fdiv_eq_ediv_of_nonneg _ (Int.natCast_nonneg _)]

theorem divu_pow2 (x n logn : bit_int w) (h : is_power2 n = some logn) : divu x n = shru x logn := by
  rw [divu, shru_div_two_p, is_power2_correct _ _ h]

theorem shr_div_two_p (x y : bit_int w) : shr x y = repr ((signed x).fdiv (two_p (unsigned y))) := by
  rw [← Zshiftr_div_two_p _ _ (unsigned_range y).1, signed_eq_toInt]
  change repr (x.bits.toInt >>> y.bits.toNat) = repr (x.bits.toInt >>> (y.bits.toNat : Int))
  rw [Int.shiftRight_natCast_right]

theorem divs_pow2 (x n logn : bit_int w) (h : is_power2 n = some logn) : divs x n = shrx x logn := by
  rw [shrx, shl_one_value, ← is_power2_correct _ _ h, repr_unsigned]

theorem Ztestbit_mod_two_p (n x i : Int) (hn : 0 ≤ n) (hi : 0 ≤ i) :
    Zbits.testbit (x.fmod (two_p n)) i = chooseSide (zlt i n) (Zbits.testbit x i) false :=
  Zbits.Ztestbit_mod_two_p n x i hn hi

theorem Ztestbit_two_p_m1 (n i : Int) (hn : 0 ≤ n) (hi : 0 ≤ i) :
    Zbits.testbit (two_p n-1) i = chooseSide (zlt i n) true false := Zbits.Ztestbit_two_p_m1 n i hn hi

theorem modu_and (x n logn : bit_int w) (h : is_power2 n = some logn) : modu x n = and x (sub n one) := by
  let p := two_p (unsigned logn)
  have hp : 0 < p := two_power_nat_pos logn.bits.toNat
  have bound := (two_p_range _ (is_power2_rng _ _ h)).2
  change p ≤ @max_unsigned w at bound
  have hov : unsigned n = p := is_power2_correct _ _ h
  have hm : unsigned (sub n one) = p - 1 := by
    rw [sub, hov, unsigned_one]; apply unsigned_repr; omega
  have mask : (sub n one).bits.toNat = 2^logn.bits.toNat - 1 := by
    change ((sub n one).bits.toNat : Int) = ((2^logn.bits.toNat : Nat) : Int) - 1 at hm
    omega
  rw [← repr_unsigned (and x (sub n one)), modu, hov]; apply congrArg repr
  change (x.bits.toNat : Int).fmod ((2^logn.bits.toNat : Nat) : Int) =
    (((x.bits &&& (sub n one).bits).toNat : Nat) : Int)
  rw [BitVec.toNat_and, mask, Nat.and_two_pow_sub_one_eq_mod, Int.natCast_emod,
    Int.fmod_eq_emod_of_nonneg _ (Int.natCast_nonneg _)]

theorem Zquot_Zdiv (x y : Int) (hy : 0 < y) : x.tdiv y =
    chooseSide (zlt x 0) ((x+y-1).fdiv y) (x.fdiv y) := Zbits.Zquot_Zdiv x y hy

theorem shrx_zero (x : bit_int w) (hw : 1 < @zwordsize w) : shrx x zero = x := by
  rw [shrx, shl_one_value, unsigned_zero]; change divs x one = x
  rw [divs, signed_one hw, Int.tdiv_one, repr_signed]

private theorem bias_range (y : bit_int w) (hy : ltu y (repr (@zwordsize w-1)) = true) :
    0 ≤ unsigned y ∧ unsigned y < @zwordsize w-1 := by
  have hw := @wordsize_pos w
  have e := of_decide_eq_true hy
  rw [index_repr (@zwordsize w-1) (by omega)] at e
  exact ⟨(unsigned_range y).1, e⟩

private theorem bias_bounds (y : bit_int w) (hy : ltu y (repr (@zwordsize w-1)) = true) :
    0 < two_p (unsigned y) ∧ two_p (unsigned y) < @half_modulus w := by
  rw [half_modulus_power]
  exact ⟨two_power_nat_pos y.bits.toNat, two_p_monotone_strict _ _ (bias_range _ hy)⟩

private theorem bias_mask (y : bit_int w) (hy : ltu y (repr (@zwordsize w-1)) = true) :
    sub (shl one y) one = repr (two_p (unsigned y)-1) := by
  rw [sub, shl_one_value, unsigned_one, unsigned_repr]
  apply two_p_range; have := bias_range _ hy; omega

private theorem signed_shl_one (y : bit_int w) (hy : ltu y (repr (@zwordsize w-1)) = true) :
    signed (shl one y) = two_p (unsigned y) := by
  rw [shl_one_value]; apply signed_repr
  have := bias_bounds _ hy; unfold min_signed max_signed; omega

private theorem add_reprs (a b : Int) : add (@repr w a) (repr b) = repr (a+b) := by
  apply eqm_samerepr
  exact eqm_add _ _ _ _ (eqm_sym _ _ (eqm_unsigned_repr a)) (eqm_sym _ _ (eqm_unsigned_repr b))

theorem shrx_shr (x y : bit_int w) (hy : ltu y (repr (@zwordsize w-1)) = true) :
    shrx x y = shr (if lt x zero then add x (sub (shl one y) one) else x) y := by
  rw [shrx, divs, signed_shl_one _ hy, Zquot_Zdiv _ _ (bias_bounds _ hy).1, shr_div_two_p, lt,
    signed_zero, bias_mask _ hy]
  by_cases hx : signed x < 0
  · simp only [hx, decide_true, ite_true, zlt_true Int _ _ _ _ hx]
    have e : add x (repr (two_p (unsigned y)-1)) = repr (signed x+(two_p (unsigned y)-1)) := by
      simpa only [repr_signed] using @add_reprs w (signed x) (two_p (unsigned y)-1)
    rw [e, signed_repr, ← add_sub_assoc]
    have := signed_range x; have := bias_bounds _ hy; unfold max_signed at *; omega
  · simp [hx, zlt, chooseSide]

private theorem power_split (y : bit_int w) (hy : unsigned y ≤ @zwordsize w) :
    @modulus w = two_p (unsigned y) * two_p (@zwordsize w - unsigned y) := by
  change (y.bits.toNat : Int) ≤ (w.val : Int) at hy
  have diff : @zwordsize w - unsigned y = ((w.val-y.bits.toNat : Nat) : Int) :=
    (Int.natCast_sub (by omega)).symm
  rw [diff, modulus_def]
  change ((2^w.val : Nat) : Int) = ((2^y.bits.toNat : Nat) : Int) * ((2^(w.val-y.bits.toNat) : Nat) : Int)
  rw [← Int.natCast_mul, ← Nat.pow_add, Nat.add_sub_of_le (Int.ofNat_le.mp hy)]

theorem shrx_shr_2 (x y : bit_int w) (hy : ltu y (repr (@zwordsize w-1)) = true) :
    shrx x y = shr (add x (shru (shr x (repr (@zwordsize w-1))) (sub iwordsize y))) y := by
  have hy' := bias_range _ hy
  have hw := @wordsize_pos w
  have hsub : unsigned (sub iwordsize y) = @zwordsize w - unsigned y := by
    rw [sub, unsigned_repr_wordsize]; apply index_repr; omega
  have hs := signed_range x
  have hp := @half_modulus_pos w
  unfold min_signed max_signed at hs
  rw [shrx_shr _ _ hy, shr_div_two_p x (repr _), index_repr _ (by omega), ← half_modulus_power,
    shru_div_two_p, hsub, lt, signed_zero]
  by_cases hx : signed x < 0
  · simp only [hx, decide_true, ite_true]
    rw [Int.fdiv_eq_ediv_of_nonneg _ hp.le, Int.ediv_eq_neg_one_of_neg_of_le hx (by omega)]
    change _ = shr (add x (repr ((unsigned (@mone w)).fdiv _))) y
    rw [bias_mask _ hy, unsigned_mone]
    have hd : 0 < two_p (@zwordsize w - unsigned y) :=
      lt_of_le_of_lt (by omega) (two_p_strict _ (by omega))
    rw [Zdiv_unique _ _ (two_p (unsigned y)-1) (two_p (@zwordsize w-unsigned y)-1) _ (by omega)]
    rw [power_split y (by omega)]; ring
  · simp only [hx, decide_false, Bool.false_eq_true, ite_false]
    rw [Zdiv_small (signed x) (@half_modulus w) (by omega)]
    change _ = shr (add x (repr ((unsigned (@zero w)).fdiv _))) y
    rw [unsigned_zero, Int.zero_fdiv]
    change shr x y = shr (add x zero) y
    rw [add, unsigned_zero, add_zero, repr_unsigned]

theorem Zdiv_shift (x y : Int) (hy : 0 < y) : (x+(y-1)).fdiv y =
    x.fdiv y + chooseSide (zeq (x.fmod y) 0) 0 1 := Zbits.Zdiv_shift x y hy

theorem shrx_carry (x y : bit_int w) (hy : ltu y (repr (@zwordsize w-1)) = true) :
    shrx x y = add (shr x y) (shr_carry x y) := by
  let p := two_p (unsigned y)
  have hb := bias_bounds y hy
  have hp : 0 < p := hb.1
  have hn := bias_range y hy
  have hm := (two_p_range (unsigned y) ⟨hn.1, by omega⟩).2
  change p ≤ @max_unsigned w at hm
  have hpow : is_power2 (shl one y) = some y := by
    rw [shl_one_value, is_power2_two_p _ ⟨hn.1, by omega⟩, repr_unsigned]
  have hu : unsigned (shl one y) = p := by
    rw [shl_one_value]; exact unsigned_repr _ ⟨hp.le, hm⟩
  have hd : p ∣ @modulus w := ⟨_, power_split y (by omega)⟩
  have hrem := Zbits.eqmod_mod_eq p hp _ _
    (Zbits.eqmod_divides _ _ _ _ (eqm_signed_unsigned x) hd)
  have mask : and x (sub (shl one y) one) = repr ((signed x).fmod p) := by
    rw [← modu_and _ _ _ hpow, modu, hu, hrem]
  have hr : 0 ≤ (signed x).fmod p ∧ (signed x).fmod p < p :=
    ⟨Int.fmod_nonneg_of_pos _ hp, Int.fmod_lt_of_pos _ hp⟩
  have zr : (@repr w ((signed x).fmod p) = zero) ↔ (signed x).fmod p = 0 := by
    constructor
    · intro e; have he := congrArg unsigned e
      rwa [unsigned_repr _ (by omega), unsigned_zero] at he
    · intro e; rw [e]; rfl
  rw [shrx, divs, signed_shl_one _ hy, shr_div_two_p, shr_carry, mask, lt, signed_zero, eq]
  change repr ((signed x).tdiv p) = add (repr ((signed x).fdiv p))
    (if decide (signed x < 0) && !decide (@repr w ((signed x).fmod p) = zero) then one else zero)
  simp only [zr]
  rw [Zquot_Zdiv _ _ hp]
  by_cases hx : signed x < 0
  · rw [zlt_true Int _ _ _ _ hx, show signed x+p-1 = signed x+(p-1) by omega, Zdiv_shift _ _ hp]
    by_cases he : (signed x).fmod p = 0 <;> simp [he, hx, zeq, decideSum, chooseSide, one, zero, add_reprs]
  · simp [hx, zlt, chooseSide, zero, add_reprs]

theorem shr_shru_positive (x y : bit_int w) (hx : 0 ≤ signed x) : shr x y = shru x y := by
  rw [shr_div_two_p, shru_div_two_p, signed_eq_unsigned _ ((signed_positive _).mp hx)]

theorem and_positive (x y : bit_int w) (hy : 0 ≤ signed y) : 0 ≤ signed (and x y) := by
  apply (signed_positive _).2
  apply le_trans _ ((signed_positive _).1 hy)
  change (((x.bits &&& y.bits).toNat : Nat) : Int) ≤ (y.bits.toNat : Int)
  rw [BitVec.toNat_and]; exact Int.ofNat_le.mpr Nat.and_le_right

theorem shr_and_is_shru_and (x y z : bit_int w) (hy : lt y zero = false) : shr (and x y) z = shru (and x y) z := by
  apply shr_shru_positive; apply and_positive; simpa [lt, signed_zero] using hy

end Vellvm.Numeric.Integers
