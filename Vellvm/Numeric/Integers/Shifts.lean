/-
The Compcert verified compiler
Xavier Leroy, INRIA Paris-Rocquencourt

Copyright Institut National de Recherche en Informatique et en Automatique.
All rights reserved. This file is distributed under the terms of the GNU Lesser General
Public License as published by the Free Software Foundation, either version 2.1 of the License,
or (at your option) any later version. This file is also distributed under the terms of the
INRIA Non-Commercial License Agreement.
-/
module

public import Vellvm.Numeric.Integers.Bitwise

@[expose] public section
namespace Vellvm.Numeric.Integers
open Vellvm.Numeric.Rocqlib

variable {w : Positive}

private theorem choose_lt {α : Type} (a b : Int) (x y : α) :
    chooseSide (zlt a b) x y = if a < b then x else y := by
  by_cases h : a < b <;> simp [zlt, chooseSide, h]

private theorem readBit (x : bit_int w) (i : Int) (hi : 0 ≤ i) :
    testbit x i = x.bits.getLsbD i.toNat := by
  simp only [testbit, Zbits.testbit, hi, decide_true, Bool.true_and]
  exact BitVec.testBit_toNat _

theorem bits_shl : ∀ (x y : bit_int w) (i : Int), 0 ≤ i ∧ i < @zwordsize w →
    testbit (shl x y) i = chooseSide (zlt i (unsigned y)) false (testbit x (i - unsigned y)) := by
  intro x y i hi
  rw [choose_lt, readBit _ _ hi.1]
  change (x.bits <<< y.bits.toNat).getLsbD _ = _
  rw [BitVec.getLsbD_shiftLeft]
  change 0 ≤ i ∧ i < (w.val : Int) at hi
  have hwidth : i.toNat < w.val := by omega
  change _ = if i < (y.bits.toNat : Int) then _ else _
  split
  · rename_i h
    have hlow : i.toNat < y.bits.toNat := by omega
    simp [hlow]
  · rename_i h
    have hhigh : ¬i.toNat < y.bits.toNat := by omega
    rw [readBit _ _ (by change 0 ≤ i - (y.bits.toNat : Int); omega)]
    simp only [hwidth, hhigh, decide_true, decide_false, Bool.not_false, Bool.true_and]
    congr 1
    change _ = (i - (y.bits.toNat : Int)).toNat
    omega

theorem bits_shru : ∀ (x y : bit_int w) (i : Int), 0 ≤ i ∧ i < @zwordsize w →
    testbit (shru x y) i = chooseSide (zlt (i + unsigned y) (@zwordsize w)) (testbit x (i + unsigned y)) false := by
  intro x y i hi
  rw [choose_lt, readBit _ _ hi.1]
  change (x.bits >>> y.bits.toNat).getLsbD _ = if i + (y.bits.toNat : Int) < (w.val : Int) then _ else _
  rw [BitVec.getLsbD_ushiftRight]
  split
  · rw [readBit _ _ (by change 0 ≤ i + (y.bits.toNat : Int); omega)]
    congr 1
    change _ = (i + (y.bits.toNat : Int)).toNat
    omega
  · apply BitVec.getLsbD_of_ge; omega

theorem bits_shr : ∀ (x y : bit_int w) (i : Int), 0 ≤ i ∧ i < @zwordsize w →
    testbit (shr x y) i = testbit x (chooseSide (zlt (i + unsigned y) (@zwordsize w)) (i + unsigned y) (@zwordsize w - 1)) := by
  intro x y i hi
  rw [choose_lt, readBit _ _ hi.1]
  change 0 ≤ i ∧ i < (w.val : Int) at hi
  change (x.bits.sshiftRight y.bits.toNat).getLsbD _ =
    testbit x (if i + (y.bits.toNat : Int) < (w.val : Int) then _ else _)
  rw [BitVec.getLsbD_sshiftRight]
  have hw := w.property
  have hwidth : ¬w.val ≤ i.toNat := by omega
  simp only [hwidth, decide_false, Bool.not_false, Bool.true_and]
  split <;> split
  · rw [readBit _ _ (by change 0 ≤ i + (y.bits.toNat : Int); omega)]
    congr 1
    change _ = (i + (y.bits.toNat : Int)).toNat
    omega
  · omega
  · omega
  · rw [BitVec.msb_eq_getLsbD_last, readBit _ _ (by change 0 ≤ (w.val : Int) - 1; omega)]
    congr 1
    change _ = ((w.val : Int) - 1).toNat
    omega

theorem shl_zero : ∀ x : bit_int w, shl x zero = x := by
  intro x
  apply same_bits_eq
  intro i hi
  rw [bits_shl _ _ _ hi, unsigned_zero, choose_lt]
  rw [if_neg (Int.not_lt_of_ge hi.1), Int.sub_zero]

theorem bitwise_binop_shl : ∀ (f : bit_int w → bit_int w → bit_int w) (g : Bool → Bool → Bool) (x y n : bit_int w),
    (∀ x y i, 0 ≤ i ∧ i < @zwordsize w → testbit (f x y) i = g (testbit x i) (testbit y i)) →
    g false false = false → f (shl x n) (shl y n) = shl (f x y) n := by
  intro f g x y n hf hfalse
  apply same_bits_eq
  intro i hi
  rw [hf _ _ _ hi, bits_shl _ _ _ hi, bits_shl _ _ _ hi, bits_shl _ _ _ hi]
  simp only [choose_lt]
  split
  · exact hfalse
  · apply (hf _ _ _ _).symm
    have := (unsigned_range n).1; omega

theorem and_shl : ∀ x y n : bit_int w, and (shl x n) (shl y n) = shl (and x y) n := fun x y n ↦ bitwise_binop_shl and Bool.and x y n bits_and rfl

theorem or_shl : ∀ x y n : bit_int w, or (shl x n) (shl y n) = shl (or x y) n := fun x y n ↦ bitwise_binop_shl or Bool.or x y n bits_or rfl

theorem xor_shl : ∀ x y n : bit_int w, xor (shl x n) (shl y n) = shl (xor x y) n := fun x y n ↦ bitwise_binop_shl xor Bool.xor x y n bits_xor rfl

theorem ltu_inv : ∀ x y : bit_int w, ltu x y = true → 0 ≤ unsigned x ∧ unsigned x < unsigned y := by
  intro x y h
  exact ⟨(unsigned_range x).1, of_decide_eq_true h⟩

theorem ltu_iwordsize_inv : ∀ x : bit_int w, ltu x iwordsize = true → 0 ≤ unsigned x ∧ unsigned x < @zwordsize w := by
  intro x h
  simpa only [unsigned_repr_wordsize] using ltu_inv _ _ h

private theorem unsigned_add_counts (y z : bit_int w) (hy : ltu y iwordsize = true)
    (hz : ltu z iwordsize = true) : unsigned (add y z) = unsigned y + unsigned z := by
  have := ltu_iwordsize_inv y hy
  have := ltu_iwordsize_inv z hz
  have := @two_wordsize_max_unsigned w
  exact unsigned_repr _ (by omega)

private theorem count_add (y z : bit_int w) (hy : ltu y iwordsize = true)
    (hz : ltu z iwordsize = true) : (add y z).bits.toNat = y.bits.toNat + z.bits.toNat :=
  Int.ofNat_inj.mp (unsigned_add_counts y z hy hz)

theorem shl_shl : ∀ x y z : bit_int w, ltu y iwordsize = true → ltu z iwordsize = true →
    ltu (add y z) iwordsize = true → shl (shl x y) z = shl x (add y z) := by
  intro x y z hy hz _
  apply bit_int.ext_bits
  change x.bits <<< y.bits.toNat <<< z.bits.toNat = x.bits <<< (add y z).bits.toNat
  rw [count_add _ _ hy hz, BitVec.shiftLeft_add]

theorem sub_ltu : ∀ x y : bit_int w, ltu x y = true → 0 ≤ unsigned y - unsigned x ∧ unsigned y - unsigned x ≤ unsigned y := by
  intro x y h
  have := ltu_inv _ _ h
  omega

theorem shru_zero : ∀ x : bit_int w, shru x zero = x := by
  intro x
  apply same_bits_eq
  intro i hi
  rw [bits_shru _ _ _ hi, unsigned_zero, choose_lt]
  simp only [Int.add_zero, if_pos hi.2]

theorem bitwise_binop_shru : ∀ (f : bit_int w → bit_int w → bit_int w) (g : Bool → Bool → Bool) (x y n : bit_int w),
    (∀ x y i, 0 ≤ i ∧ i < @zwordsize w → testbit (f x y) i = g (testbit x i) (testbit y i)) →
    g false false = false → f (shru x n) (shru y n) = shru (f x y) n := by
  intro f g x y n hf hfalse
  apply same_bits_eq
  intro i hi
  rw [hf _ _ _ hi, bits_shru _ _ _ hi, bits_shru _ _ _ hi, bits_shru _ _ _ hi]
  simp only [choose_lt]
  split
  · apply (hf _ _ _ _).symm
    have := (unsigned_range n).1; omega
  · exact hfalse

theorem and_shru : ∀ x y n : bit_int w, and (shru x n) (shru y n) = shru (and x y) n := fun x y n ↦ bitwise_binop_shru and Bool.and x y n bits_and rfl

theorem or_shru : ∀ x y n : bit_int w, or (shru x n) (shru y n) = shru (or x y) n := fun x y n ↦ bitwise_binop_shru or Bool.or x y n bits_or rfl

theorem xor_shru : ∀ x y n : bit_int w, xor (shru x n) (shru y n) = shru (xor x y) n := fun x y n ↦ bitwise_binop_shru xor Bool.xor x y n bits_xor rfl

theorem shru_shru : ∀ x y z : bit_int w, ltu y iwordsize = true → ltu z iwordsize = true →
    ltu (add y z) iwordsize = true → shru (shru x y) z = shru x (add y z) := by
  intro x y z hy hz _
  apply bit_int.ext_bits
  change x.bits >>> y.bits.toNat >>> z.bits.toNat = x.bits >>> (add y z).bits.toNat
  rw [count_add _ _ hy hz, BitVec.shiftRight_add]

theorem shr_zero : ∀ x : bit_int w, shr x zero = x := by
  intro x
  apply same_bits_eq
  intro i hi
  rw [bits_shr _ _ _ hi, unsigned_zero, choose_lt]
  simp only [Int.add_zero, if_pos hi.2]

theorem bitwise_binop_shr : ∀ (f : bit_int w → bit_int w → bit_int w) (g : Bool → Bool → Bool) (x y n : bit_int w),
    (∀ x y i, 0 ≤ i ∧ i < @zwordsize w → testbit (f x y) i = g (testbit x i) (testbit y i)) →
    f (shr x n) (shr y n) = shr (f x y) n := by
  intro f g x y n hf
  apply same_bits_eq
  intro i hi
  rw [hf _ _ _ hi, bits_shr _ _ _ hi, bits_shr _ _ _ hi, bits_shr _ _ _ hi]
  apply (hf _ _ _ _).symm
  rw [choose_lt]
  have := (unsigned_range n).1; have := @wordsize_pos w
  split <;> omega

theorem and_shr : ∀ x y n : bit_int w, and (shr x n) (shr y n) = shr (and x y) n := fun x y n ↦ bitwise_binop_shr and Bool.and x y n bits_and

theorem or_shr : ∀ x y n : bit_int w, or (shr x n) (shr y n) = shr (or x y) n := fun x y n ↦ bitwise_binop_shr or Bool.or x y n bits_or

theorem xor_shr : ∀ x y n : bit_int w, xor (shr x n) (shr y n) = shr (xor x y) n := fun x y n ↦ bitwise_binop_shr xor Bool.xor x y n bits_xor

theorem shr_shr : ∀ x y z : bit_int w, ltu y iwordsize = true → ltu z iwordsize = true →
    ltu (add y z) iwordsize = true → shr (shr x y) z = shr x (add y z) := by
  intro x y z hy hz _
  apply bit_int.ext_bits
  change (x.bits.sshiftRight y.bits.toNat).sshiftRight z.bits.toNat = x.bits.sshiftRight (add y z).bits.toNat
  rw [count_add _ _ hy hz, BitVec.sshiftRight_add]

theorem and_shr_shru : ∀ x y z : bit_int w, and (shr x z) (shru y z) = shru (and x y) z := by
  intro x y z
  apply same_bits_eq
  intro i hi
  rw [bits_and _ _ _ hi, bits_shr _ _ _ hi, bits_shru _ _ _ hi, bits_shru _ _ _ hi]
  simp only [choose_lt]
  split
  · apply (bits_and _ _ _ _).symm
    have := (unsigned_range z).1; omega
  · simp

theorem shr_and_shru_and : ∀ x y z : bit_int w, shru (shl z y) y = z → and (shr x y) z = and (shru x y) z := by
  intro x y z hz
  calc
    and (shr x y) z = and (shr x y) (shru (shl z y) y) := by rw [hz]
    _ = and (shru x y) (shru (shl z y) y) := by rw [and_shr_shru, and_shru]
    _ = and (shru x y) z := by rw [hz]

private theorem top_count : unsigned (repr (@zwordsize w - 1) : bit_int w) = @zwordsize w - 1 := by
  have := @wordsize_pos w; have := @wordsize_max_unsigned w
  exact unsigned_repr _ (by omega)

private theorem sign_test (x : bit_int w) : testbit x (@zwordsize w - 1) = lt x zero := by
  rw [sign_bit_of_unsigned, lt, signed_zero, signed]
  have hx := unsigned_range x
  by_cases h : unsigned x < @half_modulus w <;>
    simp [choose_lt, h, show ¬unsigned x < 0 by omega, show unsigned x - @modulus w < 0 by omega,
      zlt, chooseSide]

theorem shru_lt_zero : ∀ x : bit_int w, shru x (repr (@zwordsize w - 1)) = if lt x zero then one else zero := by
  intro x
  apply same_bits_eq
  intro i hi
  rw [bits_shru _ _ _ hi, top_count, choose_lt]
  by_cases h : i = 0
  · subst i
    have hr : @zwordsize w - 1 < @zwordsize w := by omega
    simp only [Int.zero_add, hr, if_true, sign_test]
    cases e : lt x zero <;> simp [bits_zero, bits_one, zeq, proj_sumbool, decideSum, chooseSide]
  · have hr : ¬i + (@zwordsize w - 1) < @zwordsize w := by omega
    rw [if_neg hr]
    cases e : lt x zero <;> simp [bits_zero, bits_one, zeq, proj_sumbool, decideSum, chooseSide, h]

theorem shr_lt_zero : ∀ x : bit_int w, shr x (repr (@zwordsize w - 1)) = if lt x zero then mone else zero := by
  intro x
  apply same_bits_eq
  intro i hi
  rw [bits_shr _ _ _ hi, top_count, choose_lt]
  have h : (if i + (@zwordsize w - 1) < @zwordsize w then i + (@zwordsize w - 1)
      else @zwordsize w - 1) = @zwordsize w - 1 := by split <;> omega
  rw [h, sign_test]
  cases e : lt x zero <;> simp [bits_mone _ hi, bits_zero]

private theorem mod_range (i : Int) : 0 ≤ i.fmod (@zwordsize w) ∧ i.fmod (@zwordsize w) < @zwordsize w :=
  ⟨Int.fmod_nonneg_of_pos i wordsize_pos, Int.fmod_lt_of_pos i wordsize_pos⟩

private theorem mod_sub_index (i r W : Int) (hi : 0 ≤ i ∧ i < W) (hr : 0 ≤ r ∧ r < W) :
    (i - r) % W = if i < r then W + (i - r) else i - r := by
  split
  · rw [← Int.add_emod_left W (i - r)]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  · exact Int.emod_eq_of_lt (by omega) (by omega)

private theorem mod_add_index (i r W : Int) (hi : 0 ≤ i ∧ i < W) (hr : 0 ≤ r ∧ r < W) :
    (i + r) % W = if i + r < W then i + r else i + r - W := by
  split
  · exact Int.emod_eq_of_lt (by omega) (by omega)
  · rw [← Int.sub_emod_right (i + r) W]
    exact Int.emod_eq_of_lt (by omega) (by omega)

private theorem word_fmod (i : Int) : i.fmod (@zwordsize w) = i % @zwordsize w :=
  Int.fmod_eq_emod_of_nonneg _ (Int.le_of_lt wordsize_pos)

theorem bits_rol : ∀ (x y : bit_int w) (i : Int), 0 ≤ i ∧ i < @zwordsize w →
    testbit (rol x y) i = testbit x ((i - unsigned y).fmod (@zwordsize w)) := by
  intro x y i hi
  rw [readBit _ _ hi.1, readBit _ _ (mod_range _).1, word_fmod]
  change (x.bits.rotateLeft y.bits.toNat).getLsbD i.toNat =
    x.bits.getLsbD ((i - (y.bits.toNat : Int)) % (w.val : Int)).toNat
  rw [BitVec.getLsbD_rotateLeft, ← Int.sub_emod_emod, Int.ofNat_mod_ofNat]
  have hmod := Nat.mod_lt y.bits.toNat w.property
  change 0 ≤ i ∧ i < (w.val : Int) at hi
  rw [mod_sub_index _ _ _ hi (by omega)]
  have hw : i.toNat < w.val := by omega
  simp only [hw, decide_true, Bool.true_and]
  split <;> split <;> first | omega | congr 1 <;> omega

theorem bits_ror : ∀ (x y : bit_int w) (i : Int), 0 ≤ i ∧ i < @zwordsize w →
    testbit (ror x y) i = testbit x ((i + unsigned y).fmod (@zwordsize w)) := by
  intro x y i hi
  rw [readBit _ _ hi.1, readBit _ _ (mod_range _).1, word_fmod]
  change (x.bits.rotateRight y.bits.toNat).getLsbD i.toNat =
    x.bits.getLsbD ((i + (y.bits.toNat : Int)) % (w.val : Int)).toNat
  rw [BitVec.getLsbD_rotateRight, ← Int.add_emod_emod, Int.ofNat_mod_ofNat]
  have hmod := Nat.mod_lt y.bits.toNat w.property
  change 0 ≤ i ∧ i < (w.val : Int) at hi
  rw [mod_add_index _ _ _ hi (by omega)]
  have hw : i.toNat < w.val := by omega
  simp only [hw, decide_true, Bool.true_and]
  split <;> split <;> first | omega | congr 1 <;> omega

theorem shl_rolm : ∀ x n : bit_int w, ltu n iwordsize = true → shl x n = rolm x n (shl mone n) := by
  intro x n hn
  have hr := ltu_iwordsize_inv n hn
  apply same_bits_eq
  intro i hi
  rw [rolm, bits_and _ _ _ hi, bits_rol _ _ _ hi, bits_shl _ _ _ hi, bits_shl _ _ _ hi]
  simp only [choose_lt]
  split
  · simp
  · have hj : 0 ≤ i - unsigned n ∧ i - unsigned n < @zwordsize w := by omega
    rw [Zmod_small _ _ hj, bits_mone _ hj, Bool.and_true]

private theorem complement_count (n : bit_int w) (hn : ltu n iwordsize = true) :
    unsigned (sub iwordsize n) = @zwordsize w - unsigned n := by
  have := ltu_iwordsize_inv n hn; have := @wordsize_max_unsigned w
  unfold sub
  rw [unsigned_repr_wordsize]
  exact unsigned_repr _ (by omega)

private theorem complement_index (i n : Int) :
    (i - (@zwordsize w - n)).fmod (@zwordsize w) = (i + n).fmod (@zwordsize w) := by
  simp only [word_fmod,
    show i - (@zwordsize w - n) = i + n - @zwordsize w by omega, Int.sub_emod_right]

theorem shru_rolm : ∀ x n : bit_int w, ltu n iwordsize = true →
    shru x n = rolm x (sub iwordsize n) (shru mone n) := by
  intro x n hn
  have hr := ltu_iwordsize_inv n hn
  apply same_bits_eq
  intro i hi
  rw [rolm, bits_and _ _ _ hi, bits_rol _ _ _ hi, bits_shru _ _ _ hi, bits_shru _ _ _ hi,
    complement_count n hn, complement_index]
  simp only [choose_lt]
  split
  · have hj : 0 ≤ i + unsigned n ∧ i + unsigned n < @zwordsize w := by omega
    rw [Zmod_small _ _ hj, bits_mone _ hj, Bool.and_true]
  · simp

theorem rol_zero : ∀ x : bit_int w, rol x zero = x := by
  intro x
  apply same_bits_eq
  intro i hi
  rw [bits_rol _ _ _ hi, unsigned_zero]
  rw [Int.sub_zero, Zmod_small _ _ hi]

theorem bitwise_binop_rol : ∀ (f : bit_int w → bit_int w → bit_int w) (g : Bool → Bool → Bool) (x y n : bit_int w),
    (∀ x y i, 0 ≤ i ∧ i < @zwordsize w → testbit (f x y) i = g (testbit x i) (testbit y i)) →
    rol (f x y) n = f (rol x n) (rol y n) := by
  intro f g x y n hf
  apply same_bits_eq
  intro i hi
  rw [hf _ _ _ hi, bits_rol _ _ _ hi, bits_rol _ _ _ hi, bits_rol _ _ _ hi]
  exact hf _ _ _ (mod_range _)

theorem rol_and : ∀ x y n : bit_int w, rol (and x y) n = and (rol x n) (rol y n) := fun x y n ↦ bitwise_binop_rol and Bool.and x y n bits_and

theorem rol_or : ∀ x y n : bit_int w, rol (or x y) n = or (rol x n) (rol y n) := fun x y n ↦ bitwise_binop_rol or Bool.or x y n bits_or

theorem rol_xor : ∀ x y n : bit_int w, rol (xor x y) n = xor (rol x n) (rol y n) := fun x y n ↦ bitwise_binop_rol xor Bool.xor x y n bits_xor

private theorem count_mod_repr (z : Int) (hd : @zwordsize w ∣ @modulus w) :
    unsigned (repr z : bit_int w) % @zwordsize w = z % @zwordsize w := by
  rw [unsigned_repr_eq, Int.fmod_eq_emod_of_nonneg _ (Int.le_of_lt modulus_pos), Int.emod_emod_of_dvd _ hd]

theorem rol_rol : ∀ x n m : bit_int w, @zwordsize w ∣ @modulus w →
    rol (rol x n) m = rol x (modu (add n m) iwordsize) := by
  intro x n m hd
  apply same_bits_eq
  intro i hi
  rw [bits_rol _ _ _ hi, bits_rol _ _ _ (mod_range _), bits_rol _ _ _ hi]
  congr 1
  simp only [word_fmod, Int.emod_sub_emod]
  have hs : unsigned (modu (add n m) iwordsize) % @zwordsize w =
      (unsigned n + unsigned m) % @zwordsize w := by
    unfold modu
    rw [count_mod_repr _ hd, unsigned_repr_wordsize, word_fmod, Int.emod_emod, add, count_mod_repr _ hd]
  rw [← Int.sub_emod_emod i (unsigned (modu (add n m) iwordsize)), hs, Int.sub_emod_emod]
  congr 1
  omega

theorem rolm_zero : ∀ x m : bit_int w, rolm x zero m = and x m := fun x m ↦ by rw [rolm, rol_zero]

theorem rolm_rolm : ∀ x n₁ m₁ n₂ m₂ : bit_int w, @zwordsize w ∣ @modulus w →
    rolm (rolm x n₁ m₁) n₂ m₂ = rolm x (modu (add n₁ n₂) iwordsize) (and (rol m₁ n₂) m₂) := fun x n₁ m₁ n₂ m₂ hd ↦ by simp only [rolm, rol_and, and_assoc, rol_rol _ _ _ hd]

theorem or_rolm : ∀ x n m₁ m₂ : bit_int w, or (rolm x n m₁) (rolm x n m₂) = rolm x n (or m₁ m₂) := fun x n a b ↦ (and_or_distrib (rol x n) a b).symm

theorem ror_rol : ∀ x y : bit_int w, ltu y iwordsize = true → ror x y = rol x (sub iwordsize y) := by
  intro x y hy
  apply same_bits_eq
  intro i hi
  rw [bits_ror _ _ _ hi, bits_rol _ _ _ hi, complement_count y hy, complement_index]

theorem ror_rol_neg : ∀ x y : bit_int w, @zwordsize w ∣ @modulus w → ror x y = rol x (neg y) := by
  intro x y hd
  apply same_bits_eq
  intro i hi
  rw [bits_ror _ _ _ hi, bits_rol _ _ _ hi]
  congr 1
  simp only [word_fmod]
  rw [← Int.sub_emod_emod, neg, count_mod_repr _ hd, Int.sub_emod_emod, Int.sub_neg]

theorem or_ror : ∀ x y z : bit_int w, ltu y iwordsize = true → ltu z iwordsize = true →
    add y z = iwordsize → ror x z = or (shl x y) (shru x z) := by
  intro x y z hy hz hsum
  have h := unsigned_add_counts y z hy hz
  rw [hsum, unsigned_repr_wordsize] at h
  have hz' := (ltu_iwordsize_inv z hz).2
  change (z.bits.toNat : Int) < (w.val : Int) at hz'
  change (w.val : Int) = (y.bits.toNat : Int) + (z.bits.toNat : Int) at h
  apply bit_int.ext_bits
  change x.bits.rotateRight z.bits.toNat = x.bits <<< y.bits.toNat ||| x.bits >>> z.bits.toNat
  rw [BitVec.rotateRight_def, Nat.mod_eq_of_lt (by omega), BitVec.or_comm]
  congr 2
  omega

end Vellvm.Numeric.Integers
