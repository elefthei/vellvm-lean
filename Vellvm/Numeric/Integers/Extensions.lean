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
import Vellvm.Numeric.Integers.Arithmetic
import Vellvm.Numeric.Integers.Powers
import Vellvm.Numeric.Integers.Shifts
import Mathlib.Data.Int.Order.Basic

@[expose] public section
namespace Vellvm.Numeric.Integers
open Rocqlib
universe u

theorem Ziter_base : ∀ (A : Type u) (n : Int) (f : A → A) (x : A), n ≤ 0 → Zbits.Ziter n f x = x := Zbits.Ziter_base

theorem Ziter_succ : ∀ (A : Type u) (n : Int) (f : A → A) (x : A), 0 ≤ n →
    Zbits.Ziter (n+1) f x = f (Zbits.Ziter n f x) := Zbits.Ziter_succ

theorem Znatlike_ind : ∀ P : Int → Prop, (∀ n, n ≤ 0 → P n) → (∀ n, 0 ≤ n → P n → P (n+1)) → ∀ n, P n := Zbits.Znatlike_ind

theorem Zzero_ext_spec : ∀ n x i, 0 ≤ i → Zbits.testbit (Zzero_ext n x) i =
    chooseSide (zlt i n) (Zbits.testbit x i) false := Zbits.Zzero_ext_spec

private theorem choose_lt {A : Type u} (i n : Int) (a b : A) :
    chooseSide (zlt i n) a b = if i < n then a else b := by
  by_cases h : i < n <;> simp [zlt, chooseSide, h]

theorem bits_zero_ext : ∀ {w : Positive} n (x : bit_int w) i, 0 ≤ i →
    testbit (zero_ext n x) i = chooseSide (zlt i n) (testbit x i) false := by
  intro w n x i hi
  by_cases h : i < @zwordsize w
  · unfold zero_ext
    rw [testbit_repr _ _ ⟨hi, h⟩]
    exact Zzero_ext_spec _ _ _ hi
  · simp [bits_above _ _ (le_of_not_gt h), choose_lt]

theorem Zsign_ext_spec : ∀ n x i, 0 ≤ i → 0 < n → Zbits.testbit (Zsign_ext n x) i =
    Zbits.testbit x (chooseSide (zlt i n) i (n-1)) := Zbits.Zsign_ext_spec

theorem bits_sign_ext : ∀ {w : Positive} n (x : bit_int w) i, 0 ≤ i ∧ i < @zwordsize w → 0 < n →
    testbit (sign_ext n x) i = testbit x (chooseSide (zlt i n) i (n-1)) := by
  intro w n x i hi hn
  unfold sign_ext
  rw [testbit_repr _ _ hi]
  exact Zsign_ext_spec _ _ _ hi.1 hn

private theorem signBitMin {w : Positive} (n : Int) (x : bit_int w) (i : Int)
    (hi : 0 ≤ i ∧ i < @zwordsize w) (hn : 0 < n) :
    testbit (sign_ext n x) i = testbit x (min i (n-1)) := by
  rw [bits_sign_ext _ _ _ hi hn, choose_lt]
  split <;> congr 1 <;> omega

theorem zero_ext_above : ∀ {w : Positive} n (x : bit_int w), @zwordsize w ≤ n → zero_ext n x = x := by
  intro w n x hn
  apply same_bits_eq _ _
  intro i hi
  rw [bits_zero_ext _ _ _ hi.1, zlt_true _ _ _ _ _ (by omega)]

theorem sign_ext_above : ∀ {w : Positive} n (x : bit_int w), @zwordsize w ≤ n → sign_ext n x = x := by
  intro w n x hn
  apply same_bits_eq _ _
  intro i hi
  rw [signBitMin _ _ _ hi (by omega), min_eq_left (by omega)]

theorem zero_ext_and : ∀ {w : Positive} n (x : bit_int w), 0 ≤ n → zero_ext n x = and x (repr (two_p n - 1)) := by
  intro w n x hn
  apply same_bits_eq _ _
  intro i hi
  rw [bits_zero_ext _ _ _ hi.1, bits_and _ _ _ hi, testbit_repr _ _ hi,
    Zbits.Ztestbit_two_p_m1 _ _ hn hi.1, choose_lt, choose_lt]
  split <;> simp

theorem zero_ext_mod : ∀ {w : Positive} n (x : bit_int w), 0 ≤ n ∧ n < @zwordsize w →
    unsigned (zero_ext n x) = (unsigned x).fmod (two_p n) := by
  intro w n x hn
  apply Zbits.equal_same_bits
  intro i hi
  change testbit (zero_ext n x) i = _
  rw [bits_zero_ext _ _ _ hi, Zbits.Ztestbit_mod_two_p _ _ _ hn.1 hi]
  rfl

theorem zero_ext_widen : ∀ {w : Positive} (x : bit_int w) n m, 0 ≤ n ∧ n ≤ m →
    zero_ext m (zero_ext n x) = zero_ext n x := by
  intro w x n m h
  apply same_bits_eq _ _
  intro i hi
  simp only [bits_zero_ext _ _ _ hi.1, choose_lt]
  split_ifs <;> first | rfl | omega

theorem sign_ext_widen : ∀ {w : Positive} (x : bit_int w) n m, 0 < n ∧ n ≤ m →
    sign_ext m (sign_ext n x) = sign_ext n x := by
  intro w x n m h
  apply same_bits_eq _ _
  intro i hi
  rw [signBitMin _ _ _ hi (by omega), signBitMin _ _ _ ⟨by omega, by omega⟩ h.1,
    signBitMin _ _ _ hi h.1]
  congr 1 <;> omega

theorem sign_zero_ext_widen : ∀ {w : Positive} (x : bit_int w) n m, 0 ≤ n ∧ n < m →
    sign_ext m (zero_ext n x) = zero_ext n x := by
  intro w x n m h
  apply same_bits_eq _ _
  intro i hi
  rw [signBitMin _ _ _ hi (by omega), bits_zero_ext _ _ _ (by omega), bits_zero_ext _ _ _ hi.1,
    choose_lt, choose_lt]
  split_ifs <;> first | rfl | omega | congr 1 <;> omega

theorem zero_ext_narrow : ∀ {w : Positive} (x : bit_int w) n m, 0 ≤ n ∧ n ≤ m →
    zero_ext n (zero_ext m x) = zero_ext n x := by
  intro w x n m h
  apply same_bits_eq _ _
  intro i hi
  simp only [bits_zero_ext _ _ _ hi.1, choose_lt]
  split_ifs <;> first | rfl | omega

theorem sign_ext_narrow : ∀ {w : Positive} (x : bit_int w) n m, 0 < n ∧ n ≤ m →
    sign_ext n (sign_ext m x) = sign_ext n x := by
  intro w x n m h
  apply same_bits_eq _ _
  intro i hi
  rw [signBitMin _ _ _ hi h.1, signBitMin _ _ _ ⟨by omega, by omega⟩ (by omega),
    signBitMin _ _ _ hi h.1]
  congr 1 <;> omega

theorem zero_sign_ext_narrow : ∀ {w : Positive} (x : bit_int w) n m, 0 < n ∧ n ≤ m →
    zero_ext n (sign_ext m x) = zero_ext n x := by
  intro w x n m h
  apply same_bits_eq _ _
  intro i hi
  rw [bits_zero_ext _ _ _ hi.1, bits_zero_ext _ _ _ hi.1, signBitMin _ _ _ hi (by omega),
    choose_lt, choose_lt]
  split_ifs <;> first | rfl | congr 1 <;> omega

theorem zero_ext_idem : ∀ {w : Positive} n (x : bit_int w), 0 ≤ n → zero_ext n (zero_ext n x) = zero_ext n x := fun n x hn ↦ zero_ext_widen x n n ⟨hn, le_rfl⟩

theorem sign_ext_idem : ∀ {w : Positive} n (x : bit_int w), 0 < n → sign_ext n (sign_ext n x) = sign_ext n x := fun n x hn ↦ sign_ext_widen x n n ⟨hn, le_rfl⟩

theorem sign_ext_zero_ext : ∀ {w : Positive} n (x : bit_int w), 0 < n → sign_ext n (zero_ext n x) = sign_ext n x := by
  intro w n x hn
  apply same_bits_eq _ _
  intro i hi
  rw [signBitMin _ _ _ hi hn, bits_zero_ext _ _ _ (by omega), signBitMin _ _ _ hi hn,
    zlt_true _ _ _ _ _ (by omega)]

theorem zero_ext_sign_ext : ∀ {w : Positive} n (x : bit_int w), 0 < n → zero_ext n (sign_ext n x) = zero_ext n x := fun n x hn ↦ zero_sign_ext_narrow x n n ⟨hn, le_rfl⟩

theorem sign_ext_equal_if_zero_equal : ∀ {w : Positive} n (x y : bit_int w), 0 < n →
    zero_ext n x = zero_ext n y → sign_ext n x = sign_ext n y := by
  intro w n x y hn h
  rw [← sign_ext_zero_ext n x hn, ← sign_ext_zero_ext n y hn, h]

theorem zero_ext_shru_shl : ∀ {w : Positive} n (x : bit_int w), 0 < n ∧ n < @zwordsize w →
    let y := @repr w (@zwordsize w - n); zero_ext n x = shru (shl x y) y := by
  intro w n x hn y
  have hy : unsigned y = @zwordsize w - n := unsigned_repr _ ⟨by omega,
    by have := @wordsize_max_unsigned w; omega⟩
  apply same_bits_eq _ _
  intro i hi
  rw [bits_zero_ext _ _ _ hi.1, bits_shru _ _ _ hi, hy, choose_lt, choose_lt]
  by_cases e : i < n
  · simp only [e, if_true, show i + (@zwordsize w - n) < @zwordsize w by omega]
    rw [bits_shl _ _ _ ⟨by omega, by omega⟩, hy, zlt_false _ _ _ _ _ (by omega),
      add_sub_cancel_right]
  · rw [if_neg e, if_neg (show ¬i + (@zwordsize w - n) < @zwordsize w by omega)]

theorem sign_ext_shr_shl : ∀ {w : Positive} n (x : bit_int w), 0 < n ∧ n < @zwordsize w →
    let y := @repr w (@zwordsize w - n); sign_ext n x = shr (shl x y) y := by
  intro w n x hn y
  have hy : unsigned y = @zwordsize w - n := unsigned_repr _ ⟨by omega,
    by have := @wordsize_max_unsigned w; omega⟩
  apply same_bits_eq _ _
  intro i hi
  rw [signBitMin _ _ _ hi hn.1, bits_shr _ _ _ hi, hy, choose_lt]
  split <;> rw [bits_shl _ _ _ ⟨by omega, by omega⟩, hy, zlt_false _ _ _ _ _ (by omega)] <;>
    congr 1 <;> omega

theorem zero_ext_range : ∀ {w : Positive} n (x : bit_int w), 0 ≤ n ∧ n < @zwordsize w →
    0 ≤ unsigned (zero_ext n x) ∧ unsigned (zero_ext n x) < two_p n := by
  intro w n x hn
  rw [zero_ext_mod n x hn, ← Zbits.Zzero_ext_mod _ _ hn.1]
  exact Zbits.Zzero_ext_range _ _ hn.1

theorem eqmod_zero_ext : ∀ {w : Positive} n (x : bit_int w), 0 ≤ n ∧ n < @zwordsize w →
    eqmod (two_p n) (unsigned (zero_ext n x)) (unsigned x) := by
  intro w n x hn
  rw [zero_ext_mod n x hn]
  exact Zbits.eqmod_sym _ _ _ (Zbits.eqmod_mod _ _)

private theorem signedSignExt {w : Positive} (n : Int) (x : bit_int w)
    (hn : 0 < n ∧ n < @zwordsize w) : signed (sign_ext n x) = Zsign_ext n (unsigned x) := by
  apply signed_repr
  have hr := Zbits.Zsign_ext_range n (unsigned x) hn.1
  have hp := two_p_monotone (n-1) (@zwordsize w - 1) ⟨by omega, by omega⟩
  rw [← @half_modulus_power w] at hp
  change -(@half_modulus w) ≤ Zbits.Zsign_ext n (unsigned x) ∧
    Zbits.Zsign_ext n (unsigned x) ≤ @half_modulus w - 1
  omega

theorem sign_ext_range : ∀ {w : Positive} n (x : bit_int w), 0 < n ∧ n < @zwordsize w →
    -two_p (n-1) ≤ signed (sign_ext n x) ∧ signed (sign_ext n x) < two_p (n-1) := by
  intro w n x hn
  rw [signedSignExt n x hn]
  exact Zbits.Zsign_ext_range _ _ hn.1

theorem eqmod_sign_ext' : ∀ {w : Positive} n (x : bit_int w), 0 < n ∧ n < @zwordsize w →
    eqmod (two_p n) (unsigned (sign_ext n x)) (unsigned x) := by
  intro w n x hn
  have en : Int.ofNat n.toNat = n := Int.toNat_of_nonneg (Int.le_of_lt hn.1)
  rw [show two_p n = two_power_nat n.toNat by rw [two_power_nat_two_p, en]]
  apply Zbits.eqmod_same_bits
  intro i hi
  change testbit (sign_ext n x) i = testbit x i
  rw [signBitMin _ _ _ ⟨by omega, by omega⟩ hn.1, min_eq_left (by omega)]

theorem eqmod_sign_ext : ∀ {w : Positive} n (x : bit_int w), 0 < n ∧ n < @zwordsize w →
    eqmod (two_p n) (signed (sign_ext n x)) (unsigned x) := by
  intro w n x hn
  rw [signedSignExt n x hn]
  exact Zbits.eqmod_Zsign_ext _ _ hn.1

theorem one_bits_range : ∀ {w : Positive} (x i : bit_int w), i ∈ one_bits x → ltu i iwordsize = true := by
  intro w x i hi
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
  have h := @Z_one_bits_range w (unsigned x) a ha
  have hw := @wordsize_max_unsigned w
  have ea := @unsigned_repr w a ⟨h.1, by omega⟩
  simp only [ltu, ea, unsigned_repr_wordsize, h.2, decide_true]

private theorem reprPowerserie {w : Positive} (l : List Int)
    (bounds : ∀ a ∈ l, 0 ≤ a ∧ a < @zwordsize w) :
    repr (powerserie l) = int_of_one_bits (l.map (@repr w)) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha := bounds a List.mem_cons_self
    have ea := @unsigned_repr w a ⟨ha.1, by have := @wordsize_max_unsigned w; omega⟩
    change repr (two_p a + powerserie l) = add (shl one (repr a)) (int_of_one_bits _)
    rw [← ih (fun b hb ↦ bounds b (List.mem_cons_of_mem _ hb)), shl_mul_two_p, ea,
      mul_commut one, mul_one, add_unsigned]
    exact eqm_samerepr _ _ (eqm_add _ _ _ _ (eqm_unsigned_repr _) (eqm_unsigned_repr _))

theorem one_bits_decomp : ∀ {w : Positive} (x : bit_int w), x = int_of_one_bits (one_bits x) := by
  intro w x
  calc
    x = repr (unsigned x) := (repr_unsigned x).symm
    _ = repr (powerserie (Z_one_bits (@natwordsize w) (unsigned x) 0)) :=
      congrArg (@repr w) (@Z_one_bits_powerserie w _ (unsigned_range x))
    _ = int_of_one_bits (one_bits x) :=
      reprPowerserie _ (@Z_one_bits_range w (unsigned x))

end Vellvm.Numeric.Integers
