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

public import Vellvm.Numeric.Integers.Basic
import Mathlib.Tactic.Ring

@[expose] public section
namespace Vellvm.Numeric.Integers

open Vellvm.Numeric.Rocqlib
variable {w : Positive}

private theorem addOfReprs (a b : Int) : add (@repr w a) (repr b) = repr (a + b) := by
  apply eqm_samerepr
  apply eqm_add <;> apply eqm_sym <;> apply eqm_unsigned_repr

private theorem subOfReprs (a b : Int) : sub (@repr w a) (repr b) = repr (a - b) := by
  apply eqm_samerepr
  apply eqm_sub <;> apply eqm_sym <;> apply eqm_unsigned_repr

private theorem mulOfReprs (a b : Int) : mul (@repr w a) (repr b) = repr (a * b) := by
  apply eqm_samerepr
  apply eqm_mult <;> apply eqm_sym <;> apply eqm_unsigned_repr

theorem neg_repr (a : Int) : neg (@repr w a) = repr (-a) := by
  apply eqm_samerepr
  apply eqm_neg
  apply eqm_sym
  apply eqm_unsigned_repr

private theorem hasRepr (x : bit_int w) : ∃ a : Int, repr a = x := ⟨_, repr_unsigned x⟩

-- Lift word polynomials to integer polynomials before invoking the ring normalizer.
local macro "word_ring" : tactic => `(tactic| (
  repeat' (intro x; obtain ⟨a, h⟩ := hasRepr x; subst x)
  simp only [zero, one, mone, addOfReprs, subOfReprs, mulOfReprs, neg_repr] <;>
    apply congrArg repr <;> ring))

theorem add_unsigned : ∀ x y : bit_int w, add x y = repr (unsigned x + unsigned y) := by intros; rfl

theorem add_signed : ∀ x y : bit_int w, add x y = repr (signed x + signed y) := by
  intro x y
  apply eqm_samerepr
  apply eqm_add <;> apply eqm_sym <;> apply eqm_signed_unsigned

theorem add_commut : ∀ x y : bit_int w, add x y = add y x := by word_ring

theorem add_zero : ∀ x : bit_int w, add x zero = x := by word_ring

theorem add_zero_l : ∀ x : bit_int w, add zero x = x := by word_ring

theorem add_assoc : ∀ x y z : bit_int w, add (add x y) z = add x (add y z) := by word_ring

theorem add_permut : ∀ x y z : bit_int w, add x (add y z) = add y (add x z) := by word_ring

theorem add_neg_zero : ∀ x : bit_int w, add x (neg x) = zero := by word_ring

theorem unsigned_add_carry : ∀ x y : bit_int w,
    unsigned (add x y) = unsigned x + unsigned y - unsigned (add_carry x y zero) * @modulus w := by
  intro x y
  have hx := unsigned_range x
  have hy := unsigned_range y
  by_cases h : unsigned x + unsigned y < @modulus w
  · have e := Zmod_unique (unsigned x + unsigned y) (@modulus w) 0
        (unsigned x + unsigned y) (by simp) (by omega)
    simp [add, add_carry, unsigned_zero, unsigned_repr_eq, h, e]
  · have e := Zmod_unique (unsigned x + unsigned y) (@modulus w) 1
        (unsigned x + unsigned y - @modulus w) (by omega) (by omega)
    simp [add, add_carry, unsigned_zero, unsigned_one, unsigned_repr_eq, h, e]

theorem unsigned_add_either : ∀ x y : bit_int w, unsigned (add x y) = unsigned x + unsigned y ∨
    unsigned (add x y) = unsigned x + unsigned y - @modulus w := by
  intro x y
  rw [unsigned_add_carry]
  by_cases h : unsigned x + unsigned y < @modulus w <;>
    simp [add_carry, unsigned_zero, unsigned_one, h]

theorem neg_zero : neg (@zero w) = zero := by word_ring

theorem neg_involutive : ∀ x : bit_int w, neg (neg x) = x := by word_ring

theorem neg_add_distr : ∀ x y : bit_int w, neg (add x y) = add (neg x) (neg y) := by word_ring

theorem sub_zero_l : ∀ x : bit_int w, sub x zero = x := by word_ring

theorem sub_zero_r : ∀ x : bit_int w, sub zero x = neg x := by word_ring

theorem sub_add_opp : ∀ x y : bit_int w, sub x y = add x (neg y) := by word_ring

theorem sub_idem : ∀ x : bit_int w, sub x x = zero := by word_ring

theorem sub_add_l : ∀ x y z : bit_int w, sub (add x y) z = add (sub x z) y := by word_ring

theorem sub_add_r : ∀ x y z : bit_int w, sub x (add y z) = add (sub x z) (neg y) := by word_ring

theorem sub_shifted : ∀ x y z : bit_int w, sub (add x z) (add y z) = sub x y := by word_ring

theorem sub_signed : ∀ x y : bit_int w, sub x y = repr (signed x - signed y) := by
  intro x y
  apply eqm_samerepr
  apply eqm_sub <;> apply eqm_sym <;> apply eqm_signed_unsigned

theorem unsigned_sub_borrow : ∀ x y : bit_int w,
    unsigned (sub x y) = unsigned x - unsigned y + unsigned (sub_borrow x y zero) * @modulus w := by
  intro x y
  have hx := unsigned_range x
  have hy := unsigned_range y
  by_cases h : unsigned x - unsigned y < 0
  · have e := Zmod_unique (unsigned x - unsigned y) (@modulus w) (-1)
        (unsigned x - unsigned y + @modulus w) (by omega) (by omega)
    simp [sub, sub_borrow, unsigned_zero, unsigned_one, unsigned_repr_eq, h, e]
  · have e := Zmod_unique (unsigned x - unsigned y) (@modulus w) 0
        (unsigned x - unsigned y) (by simp) (by omega)
    simp [sub, sub_borrow, unsigned_zero, unsigned_repr_eq, h, e]

theorem mul_commut : ∀ x y : bit_int w, mul x y = mul y x := by word_ring

theorem mul_zero : ∀ x : bit_int w, mul x zero = zero := by word_ring

theorem mul_one : ∀ x : bit_int w, mul x one = x := by word_ring

theorem mul_mone : ∀ x : bit_int w, mul x mone = neg x := by word_ring

theorem mul_assoc : ∀ x y z : bit_int w, mul (mul x y) z = mul x (mul y z) := by word_ring

theorem mul_add_distr_l : ∀ x y z : bit_int w, mul (add x y) z = add (mul x z) (mul y z) := by word_ring

theorem mul_add_distr_r : ∀ x y z : bit_int w, mul x (add y z) = add (mul x y) (mul x z) := by word_ring

theorem neg_mul_distr_l : ∀ x y : bit_int w, neg (mul x y) = mul (neg x) y := by word_ring

theorem neg_mul_distr_r : ∀ x y : bit_int w, neg (mul x y) = mul x (neg y) := by word_ring

theorem mul_signed : ∀ x y : bit_int w, mul x y = repr (signed x * signed y) := by
  intro x y
  apply eqm_samerepr
  apply eqm_mult <;> apply eqm_sym <;> apply eqm_signed_unsigned

theorem modu_divu_Euclid : ∀ x y : bit_int w, y ≠ zero → x = add (mul (divu x y) y) (modu x y) := by
  intro x y _
  calc
    x = repr (unsigned x) := (repr_unsigned x).symm
    _ = _ := by
      conv_lhs => rw [← Int.fdiv_mul_add_fmod (unsigned x) (unsigned y)]
      rw [← addOfReprs, ← mulOfReprs, repr_unsigned] <;> rfl

private theorem remainderOfSum (x q r : bit_int w) (h : x = add q r) : r = sub x q := by
  rw [h, sub_add_l, sub_idem, add_zero_l]

theorem modu_divu : ∀ x y : bit_int w, y ≠ zero → modu x y = sub x (mul (divu x y) y) := by
  intro x y h
  exact remainderOfSum _ _ _ (modu_divu_Euclid x y h)

theorem mods_divs_Euclid : ∀ x y : bit_int w, x = add (mul (divs x y) y) (mods x y) := by
  intro x y
  calc
    x = repr (signed x) := (repr_signed x).symm
    _ = _ := by
      conv_lhs => rw [← Int.tdiv_mul_add_tmod (signed x) (signed y)]
      rw [← addOfReprs, ← mulOfReprs, repr_signed] <;> rfl

theorem mods_divs : ∀ x y : bit_int w, mods x y = sub x (mul (divs x y) y) := by
  intro x y
  exact remainderOfSum _ _ _ (mods_divs_Euclid x y)

theorem divu_one : ∀ x : bit_int w, divu x one = x := by
  intro x
  simp only [divu, unsigned_one, Int.fdiv_one, repr_unsigned]

theorem divs_one : ∀ x : bit_int w, 1 < @zwordsize w → divs x one = x := by
  intro x h
  simp only [divs, signed_one h, Int.tdiv_one, repr_signed]

theorem modu_one : ∀ x : bit_int w, modu x one = zero := by
  intro x
  simp only [modu, unsigned_one, Int.fmod_one, zero]

theorem divs_mone : ∀ x : bit_int w, divs x mone = neg x := by
  intro x
  simp only [divs, signed_mone, Int.tdiv_neg, Int.tdiv_one]
  rw [← neg_repr, repr_signed]

theorem mods_mone : ∀ x : bit_int w, mods x mone = zero := by
  intro x
  rw [mods_divs, divs_mone, mul_mone, neg_involutive, sub_idem]

theorem divmodu2_divu_modu : ∀ n d : bit_int w,
    d ≠ zero → divmodu2 zero n d = some (divu n d, modu n d) := by
  intro n d hd
  have hq : (unsigned n).fdiv (unsigned d) ≤ @max_unsigned w :=
    (Int.fdiv_le_self _ (unsigned_range n).1).trans (unsigned_range_2 n).2
  simp [divmodu2, divu, modu, hd, unsigned_zero, hq]

theorem unsigned_signed : ∀ n : bit_int w,
    unsigned n = if lt n zero then signed n + @modulus w else signed n := by
  intro n
  have hn := unsigned_range n
  have hm := @half_modulus_modulus w
  unfold lt
  rw [signed_zero]
  unfold signed
  by_cases h : unsigned n < @half_modulus w
  · have hz : ¬unsigned n < 0 := by omega
    simp [h, hz]
  · have hz : unsigned n - @modulus w < 0 := by omega
    simp [h, hz]

-- Only the smallest signed value divided by -1 can escape the signed range.
private theorem tdivRange (n d h : Int) (hp : 0 < h) (hn : -h ≤ n ∧ n ≤ h - 1)
    (hd : d ≠ 0) (hov : n ≠ -h ∨ d ≠ -1) : -h ≤ n.tdiv d ∧ n.tdiv d ≤ h - 1 := by
  by_cases h1 : d = 1
  · simpa [h1] using hn
  by_cases hm1 : d = -1
  · simp only [hm1, Int.tdiv_neg, Int.tdiv_one]; omega
  by_cases h0 : n = 0
  · simp [h0]; omega
  have ha : 0 < n.natAbs := by omega
  have hb : 1 < d.natAbs := by omega
  have hlt : (n.tdiv d).natAbs < n.natAbs := by
    rw [Int.natAbs_tdiv]; exact Nat.div_lt_self ha hb
  omega

theorem divmods2_divs_mods : ∀ n d : bit_int w, d ≠ zero → n ≠ repr (@min_signed w) ∨ d ≠ mone →
    divmods2 (if lt n zero then mone else zero) n d = some (divs n d, mods n d) := by
  intro n d hd hoverflow
  have hd' : signed d ≠ 0 := by
    intro e
    exact hd ((repr_signed d).symm.trans (congrArg repr e))
  have hov : signed n ≠ @min_signed w ∨ signed d ≠ -1 := by
    rcases hoverflow with h | h
    · exact Or.inl fun e ↦ h ((repr_signed n).symm.trans (congrArg repr e))
    · exact Or.inr fun e ↦ h ((repr_signed d).symm.trans (congrArg repr e))
  have hq := tdivRange (signed n) (signed d) (@half_modulus w) half_modulus_pos
    (signed_range n) hd' hov
  have hn : signed (if lt n zero then mone else zero : bit_int w) * @modulus w + unsigned n =
      signed n := by
    rw [unsigned_signed n]
    cases lt n zero <;> simp [signed_zero, signed_mone]
  simp [divmods2, divs, mods, hd, hn,
    show @min_signed w ≤ (signed n).tdiv (signed d) from hq.1,
    show (signed n).tdiv (signed d) ≤ @max_signed w from hq.2]

end Vellvm.Numeric.Integers
