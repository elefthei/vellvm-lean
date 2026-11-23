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

@[expose] public section
namespace Vellvm.Numeric.Integers
open Rocqlib

theorem Ztestbit_0 : ∀ n, Zbits.testbit 0 n = false := Zbits.Ztestbit_0

theorem Ztestbit_1 : ∀ n, Zbits.testbit 1 n = proj_sumbool (zeq n 0) := Zbits.Ztestbit_1

theorem Ztestbit_m1 : ∀ n, 0 ≤ n → Zbits.testbit (-1) n = true := Zbits.Ztestbit_m1

theorem Zshiftin_spec : ∀ b x, Zshiftin b x = 2 * x + (if b then 1 else 0) := Zbits.Zshiftin_spec

theorem Zshiftin_inj : ∀ b₁ x₁ b₂ x₂, Zshiftin b₁ x₁ = Zshiftin b₂ x₂ → b₁ = b₂ ∧ x₁ = x₂ := Zbits.Zshiftin_inj

theorem Zdecomp : ∀ x, x = Zshiftin (Int.bodd x) (Int.div2 x) := Zbits.Zdecomp

theorem Ztestbit_shiftin : ∀ b x n, 0 ≤ n → Zbits.testbit (Zshiftin b x) n = chooseSide (zeq n 0) b (Zbits.testbit x
    (n - 1)) := Zbits.Ztestbit_shiftin

theorem Ztestbit_shiftin_base : ∀ b x, Zbits.testbit (Zshiftin b x) 0 = b := Zbits.Ztestbit_shiftin_base

theorem Ztestbit_shiftin_succ : ∀ b x n, 0 ≤ n → Zbits.testbit (Zshiftin b x) (n + 1) = Zbits.testbit x n := Zbits.Ztestbit_shiftin_succ

theorem Ztestbit_eq : ∀ n x, 0 ≤ n → Zbits.testbit x n = chooseSide (zeq n 0) (Int.bodd x) (Zbits.testbit (Int.div2 x)
    (n - 1)) := Zbits.Ztestbit_eq

theorem Ztestbit_base : ∀ x, Zbits.testbit x 0 = Int.bodd x := Zbits.Ztestbit_base

theorem Ztestbit_succ : ∀ n x, 0 ≤ n → Zbits.testbit x (n + 1) = Zbits.testbit (Int.div2 x) n := Zbits.Ztestbit_succ

theorem eqmod_same_bits : ∀ (n : Nat) (x y : Int), (∀ i : Int, 0 ≤ i ∧ i < (n : Int) → Zbits.testbit x i =
    Zbits.testbit y i) → eqmod (two_power_nat n) x y := Zbits.eqmod_same_bits

theorem eqm_same_bits : ∀ {w : Positive}, ∀ x y, (∀ i, 0 ≤ i ∧ i < (@zwordsize w) →
    Zbits.testbit x i = Zbits.testbit y i) → @eqm w x y := by
  intro w x y h
  unfold eqm
  rw [modulus_two_power_nat, natwordsize_def]
  exact eqmod_same_bits w.val x y h

theorem same_bits_eqmod : ∀ (n : Nat) (x y i : Int), eqmod (two_power_nat n) x y → 0 ≤ i ∧ i < (n : Int) →
    Zbits.testbit x i = Zbits.testbit y i := Zbits.same_bits_eqmod

theorem same_bits_eqm : ∀ {w : Positive}, ∀ x y i, @eqm w x y → 0 ≤ i ∧ i < (@zwordsize w) →
    Zbits.testbit x i = Zbits.testbit y i := by
  intro w x y i h hi
  unfold eqm at h
  rw [modulus_two_power_nat, natwordsize_def] at h
  exact same_bits_eqmod w.val x y i h hi

theorem two_power_nat_infinity : ∀ x : Int, 0 ≤ x → ∃ n, x < two_power_nat n := by
  rintro (n | n) hn
  · exact ⟨n, Int.ofNat_lt.mpr Nat.lt_two_pow_self⟩
  · omega

theorem equal_same_bits : ∀ x y, (∀ i, 0 ≤ i → Zbits.testbit x i = Zbits.testbit y i) → x = y := Zbits.equal_same_bits

theorem Z_one_complement : ∀ i, 0 ≤ i → ∀ x, Zbits.testbit (-x - 1) i = !(Zbits.testbit x i) := Zbits.Z_one_complement

theorem Ztestbit_above : ∀ (n : Nat) (x i : Int), 0 ≤ x ∧ x < two_power_nat n → (n : Int) ≤ i → Zbits.testbit x
    i = false := Zbits.Ztestbit_above

theorem Ztestbit_above_neg : ∀ (n : Nat) (x i : Int), -two_power_nat n ≤ x ∧ x < 0 → (n : Int) ≤ i →
    Zbits.testbit x i = true := Zbits.Ztestbit_above_neg

theorem Zsign_bit : ∀ n x, 0 ≤ x ∧ x < two_power_nat (n+1) → Zbits.testbit x (Int.ofNat n) = chooseSide (zlt x
    (two_power_nat n)) false true := Zbits.Zsign_bit

theorem Zshiftin_ind : ∀ P : Int → Prop, P 0 → (∀ b x, 0 ≤ x → P x → P (Zshiftin b x)) → ∀ x, 0 ≤ x → P x := Zbits.Zshiftin_ind

theorem Zshiftin_pos_ind : ∀ P : Int → Prop, P 1 → (∀ b x, 0 < x → P x → P (Zshiftin b x)) → ∀ x, 0 < x →
    P x := Zbits.Zshiftin_pos_ind

theorem Ztestbit_le : ∀ x y, 0 ≤ y → (∀ i, 0 ≤ i → Zbits.testbit x i = true → Zbits.testbit y i = true) → x ≤ y := Zbits.Ztestbit_le

theorem testbit_repr : ∀ {w : Positive}, ∀ x i, 0 ≤ i ∧ i < (@zwordsize w) →
    testbit (@repr w x) i = Zbits.testbit x i := by
  intro w x i hi
  exact same_bits_eqm _ _ i (eqm_sym _ _ (@eqm_unsigned_repr w x)) hi

theorem same_bits_eq : ∀ {w : Positive}, ∀ x y : bit_int w, (∀ i, 0 ≤ i ∧ i < (@zwordsize w) →
    testbit x i = testbit y i) → x = y := by
  intro w x y h
  calc
    x = repr (unsigned x) := (repr_unsigned x).symm
    _ = repr (unsigned y) := eqm_samerepr _ _ (eqm_same_bits _ _ h)
    _ = y := repr_unsigned y

theorem bits_above : ∀ {w : Positive}, ∀ (x : bit_int w) i, (@zwordsize w) ≤ i → testbit x i = false := by
  intro w x i hi
  apply Ztestbit_above w.val _ _ _ hi
  simpa only [modulus_two_power_nat, natwordsize_def] using unsigned_range x

theorem bits_zero : ∀ {w : Positive}, ∀ i, testbit (@zero w) i = false := by
  intro w i
  simpa only [testbit, unsigned_zero] using Ztestbit_0 i

theorem bits_one : ∀ {w : Positive}, ∀ n, testbit (@one w) n = proj_sumbool (zeq n 0) := by
  intro w n
  simpa only [testbit, unsigned_one] using Ztestbit_1 n

theorem bits_mone : ∀ {w : Positive}, ∀ i, 0 ≤ i ∧ i < (@zwordsize w) → testbit (@mone w) i = true := by
  intro w i hi
  exact (testbit_repr (-1) i hi).trans (Ztestbit_m1 i hi.1)

theorem sign_bit_of_unsigned : ∀ {w : Positive}, ∀ x : bit_int w, testbit x ((@zwordsize w) - 1) =
    chooseSide (zlt (unsigned x) (@half_modulus w)) false true := by
  intro w x
  let n := w.val - 1
  have hs : n + 1 = w.val := by have := w.property; dsimp [n]; omega
  have hi : (@zwordsize w) - 1 = Int.ofNat n := by
    change (w.val : Int) - 1 = (n : Int)
    omega
  have hm : (@half_modulus w) = two_power_nat n := by
    rw [half_modulus_power, hi, ← two_power_nat_two_p]
  rw [hi, hm]
  apply Zsign_bit
  simpa only [hs, modulus_two_power_nat, natwordsize_def] using unsigned_range x

theorem bits_signed : ∀ {w : Positive}, ∀ (x : bit_int w) i, 0 ≤ i → Zbits.testbit (signed x) i =
    testbit x (chooseSide (zlt i (@zwordsize w)) i ((@zwordsize w) - 1)) := by
  intro w x i hi
  by_cases h : i < @zwordsize w
  · rw [zlt_true _ _ _ _ _ h]
    exact same_bits_eqm _ _ i (eqm_signed_unsigned x) ⟨hi, h⟩
  · rw [zlt_false _ _ _ _ _ (by omega), sign_bit_of_unsigned]
    by_cases s : unsigned x < @half_modulus w
    · rw [zlt_true _ _ _ _ _ s]
      simpa only [signed, ite_eq_left s, testbit] using bits_above x i (by omega)
    · rw [zlt_false _ _ _ _ _ (by omega)]
      simp only [signed, ite_eq_right s]
      apply Ztestbit_above_neg w.val
      · have hu := unsigned_range x
        rw [← (@natwordsize_def w), ← modulus_two_power_nat]
        omega
      · change (@zwordsize w) ≤ i; omega

theorem bits_le : ∀ {w : Positive}, ∀ x y : bit_int w,
    (∀ i, 0 ≤ i ∧ i < (@zwordsize w) → testbit x i = true → testbit y i = true) →
    unsigned x ≤ unsigned y := by
  intro w x y h
  apply Ztestbit_le _ _ (unsigned_range y).1
  intro i hi hx
  by_cases lt : i < @zwordsize w
  · exact h i ⟨hi, lt⟩ hx
  · exact False.elim (Bool.false_ne_true ((bits_above x i (by omega)).symm.trans hx))

theorem bits_and : ∀ {w : Positive}, ∀ (x y : bit_int w) i, 0 ≤ i ∧ i < (@zwordsize w) →
    testbit (and x y) i = (testbit x i && testbit y i) := by
  intro w x y i hi
  simp only [testbit, Zbits.testbit, hi.1, decide_true, Bool.true_and, unsigned, intval, and,
    Int.testBit, BitVec.toNat_and, Nat.testBit_and]

theorem bits_or : ∀ {w : Positive}, ∀ (x y : bit_int w) i, 0 ≤ i ∧ i < (@zwordsize w) →
    testbit (or x y) i = (testbit x i || testbit y i) := by
  intro w x y i hi
  simp only [testbit, Zbits.testbit, hi.1, decide_true, Bool.true_and, unsigned, intval, or,
    Int.testBit, BitVec.toNat_or, Nat.testBit_or]

theorem bits_xor : ∀ {w : Positive}, ∀ (x y : bit_int w) i, 0 ≤ i ∧ i < (@zwordsize w) →
    testbit (xor x y) i = Bool.xor (testbit x i) (testbit y i) := by
  intro w x y i hi
  simp only [testbit, Zbits.testbit, hi.1, decide_true, Bool.true_and, unsigned, intval, xor,
    Int.testBit, BitVec.toNat_xor, Nat.testBit_xor]

theorem bits_not : ∀ {w : Positive}, ∀ (x : bit_int w) i, 0 ≤ i ∧ i < (@zwordsize w) →
    testbit (not x) i = !(testbit x i) := by
  intro w x i hi
  have h : i.toNat < w.val := by change 0 ≤ i ∧ i < (w.val : Int) at hi; omega
  simp only [testbit, Zbits.testbit, hi.1, decide_true, Bool.true_and]
  change (~~~x.bits).getLsbD i.toNat = !x.bits.getLsbD i.toNat
  simp [h]

local macro "word_bits" : tactic =>
  `(tactic| (
    apply same_bits_eq
    intro i hi
    simp only [bits_and _ _ _ hi, bits_or _ _ _ hi, bits_xor _ _ _ hi, bits_not _ _ hi,
      bits_zero, bits_mone _ hi] <;> grind))

theorem and_commut : ∀ {w : Positive}, ∀ x y : bit_int w, and x y = and y x := by
  intro w x y
  word_bits

theorem and_assoc : ∀ {w : Positive}, ∀ x y z : bit_int w, and (and x y) z = and x (and y z) := by
  intro w x y z
  word_bits

theorem and_zero : ∀ {w : Positive}, ∀ x : bit_int w, and x zero = zero := by
  intro w x
  word_bits

theorem and_zero_l : ∀ {w : Positive}, ∀ x : bit_int w, and zero x = zero := by
  intro w x
  word_bits

theorem and_mone : ∀ {w : Positive}, ∀ x : bit_int w, and x mone = x := by
  intro w x
  word_bits

theorem and_mone_l : ∀ {w : Positive}, ∀ x : bit_int w, and mone x = x := by
  intro w x
  word_bits

theorem and_idem : ∀ {w : Positive}, ∀ x : bit_int w, and x x = x := by
  intro w x
  word_bits

theorem or_commut : ∀ {w : Positive}, ∀ x y : bit_int w, or x y = or y x := by
  intro w x y
  word_bits

theorem or_assoc : ∀ {w : Positive}, ∀ x y z : bit_int w, or (or x y) z = or x (or y z) := by
  intro w x y z
  word_bits

theorem or_zero : ∀ {w : Positive}, ∀ x : bit_int w, or x zero = x := by
  intro w x
  word_bits

theorem or_zero_l : ∀ {w : Positive}, ∀ x : bit_int w, or zero x = x := by
  intro w x
  word_bits

theorem or_mone : ∀ {w : Positive}, ∀ x : bit_int w, or x mone = mone := by
  intro w x
  word_bits

theorem or_idem : ∀ {w : Positive}, ∀ x : bit_int w, or x x = x := by
  intro w x
  word_bits

theorem and_or_distrib : ∀ {w : Positive}, ∀ x y z : bit_int w, and x (or y z) = or (and x y) (and x z) := by
  intro w x y z
  word_bits

theorem and_or_distrib_l : ∀ {w : Positive}, ∀ x y z : bit_int w, and (or x y) z = or (and x z) (and y z) := by
  intro w x y z
  word_bits

theorem or_and_distrib : ∀ {w : Positive}, ∀ x y z : bit_int w, or x (and y z) = and (or x y) (or x z) := by
  intro w x y z
  word_bits

theorem or_and_distrib_l : ∀ {w : Positive}, ∀ x y z : bit_int w, or (and x y) z = and (or x z) (or y z) := by
  intro w x y z
  word_bits

theorem and_or_absorb : ∀ {w : Positive}, ∀ x y : bit_int w, and x (or x y) = x := by
  intro w x y
  word_bits

theorem or_and_absorb : ∀ {w : Positive}, ∀ x y : bit_int w, or x (and x y) = x := by
  intro w x y
  word_bits

theorem xor_commut : ∀ {w : Positive}, ∀ x y : bit_int w, xor x y = xor y x := by
  intro w x y
  word_bits

theorem xor_assoc : ∀ {w : Positive}, ∀ x y z : bit_int w, xor (xor x y) z = xor x (xor y z) := by
  intro w x y z
  word_bits

theorem xor_zero : ∀ {w : Positive}, ∀ x : bit_int w, xor x zero = x := by
  intro w x
  word_bits

theorem xor_zero_l : ∀ {w : Positive}, ∀ x : bit_int w, xor zero x = x := by
  intro w x
  word_bits

theorem xor_idem : ∀ {w : Positive}, ∀ x : bit_int w, xor x x = zero := by
  intro w x
  word_bits

theorem xor_zero_one : ∀ {w : Positive}, xor (@zero w) one = one := fun {_} ↦ xor_zero_l one

theorem xor_one_one : ∀ {w : Positive}, xor (@one w) one = zero := fun {_} ↦ xor_idem one

theorem xor_zero_equal : ∀ {w : Positive}, ∀ x y : bit_int w, xor x y = zero → x = y := by
  intro w x y h
  apply same_bits_eq
  intro i hi
  have e := congrArg (fun z ↦ testbit z i) h
  simp only [bits_xor _ _ _ hi, bits_zero] at e
  grind

theorem xor_is_zero : ∀ {w : Positive}, ∀ x y : bit_int w, eq (xor x y) zero = eq x y := by
  intro w x y
  by_cases h : x = y
  · subst y; rw [xor_idem, eq_true, eq_true]
  · rw [eq_false _ _ h, eq_false _ _ (fun e ↦ h (xor_zero_equal _ _ e))]

theorem and_xor_distrib : ∀ {w : Positive}, ∀ x y z : bit_int w, and x (xor y z) = xor (and x y) (and x z) := by
  intro w x y z
  word_bits

theorem and_le : ∀ {w : Positive}, ∀ x y : bit_int w, unsigned (and x y) ≤ unsigned x := by
  intro w x y
  apply bits_le
  intro i hi h
  rw [bits_and _ _ _ hi, Bool.and_eq_true] at h
  exact h.1

theorem or_le : ∀ {w : Positive}, ∀ x y : bit_int w, unsigned x ≤ unsigned (or x y) := by
  intro w x y
  apply bits_le
  intro i hi h
  simp [bits_or _ _ _ hi, h]

theorem not_involutive : ∀ {w : Positive}, ∀ x : bit_int w, not (not x) = x := by
  intro w x
  word_bits

theorem not_zero : ∀ {w : Positive}, not (@zero w) = mone := by
  intro w
  word_bits

theorem not_mone : ∀ {w : Positive}, not (@mone w) = zero := by
  intro w
  word_bits

theorem not_or_and_not : ∀ {w : Positive}, ∀ x y : bit_int w, not (or x y) = and (not x) (not y) := by
  intro w x y
  word_bits

theorem not_and_or_not : ∀ {w : Positive}, ∀ x y : bit_int w, not (and x y) = or (not x) (not y) := by
  intro w x y
  word_bits

theorem and_not_self : ∀ {w : Positive}, ∀ x : bit_int w, and x (not x) = zero := by
  intro w x
  word_bits

theorem or_not_self : ∀ {w : Positive}, ∀ x : bit_int w, or x (not x) = mone := by
  intro w x
  word_bits

theorem xor_not_self : ∀ {w : Positive}, ∀ x : bit_int w, xor x (not x) = mone := by
  intro w x
  word_bits

theorem unsigned_not : ∀ {w : Positive}, ∀ x : bit_int w, unsigned (not x) = (@max_unsigned w) - unsigned x := by
  intro w x
  change Int.ofNat (~~~x.bits).toNat = (@modulus w) - 1 - Int.ofNat x.bits.toNat
  rw [BitVec.toNat_not, modulus_two_power_nat, natwordsize_def]
  have := x.bits.isLt
  change ((2 ^ w.val - 1 - x.bits.toNat : Nat) : Int) = ((2 ^ w.val : Nat) : Int) - 1 - ↑x.bits.toNat
  omega

private theorem not_as_repr {w : Positive} (x : bit_int w) :
    not x = repr (-unsigned x - 1) := by
  apply same_bits_eq
  intro i hi
  rw [bits_not _ _ hi, testbit_repr _ _ hi, Z_one_complement _ hi.1]
  rfl

private theorem add_of_repr {w : Positive} (x y : Int) :
    add (@repr w x) (repr y) = repr (x + y) :=
  eqm_samerepr _ _ (eqm_add _ _ _ _ (eqm_sym _ _ (eqm_unsigned_repr x))
    (eqm_sym _ _ (eqm_unsigned_repr y)))

private theorem sub_of_repr {w : Positive} (x y : Int) :
    sub (@repr w x) (repr y) = repr (x - y) :=
  eqm_samerepr _ _ (eqm_sub _ _ _ _ (eqm_sym _ _ (eqm_unsigned_repr x))
    (eqm_sym _ _ (eqm_unsigned_repr y)))

private theorem add_not_as_repr {w : Positive} (x y : bit_int w) :
    add x (not y) = repr (unsigned x + (-unsigned y - 1)) := by
  rw [not_as_repr, ← repr_unsigned x, add_of_repr, repr_unsigned]

theorem not_neg : ∀ {w : Positive}, ∀ x : bit_int w, not x = add (neg x) mone := by
  intro w x
  rw [not_as_repr]
  change repr (-unsigned x - 1) = add (@repr w (-unsigned x)) (repr (-1))
  rw [add_of_repr]; congr 1

theorem neg_not : ∀ {w : Positive}, ∀ x : bit_int w, neg x = add (not x) one := by
  intro w x
  rw [not_as_repr]
  change repr (-unsigned x) = add (@repr w (-unsigned x - 1)) (repr 1)
  rw [add_of_repr]; congr 1; omega

theorem sub_add_not : ∀ {w : Positive}, ∀ x y : bit_int w, sub x y = add (add x (not y)) one := by
  intro w x y
  rw [add_not_as_repr]
  change repr (unsigned x - unsigned y) = add (@repr w _) (repr 1)
  rw [add_of_repr]; congr 1; omega

theorem sub_add_not_3 : ∀ {w : Positive}, ∀ x y b : bit_int w, b = zero ∨ b = one → sub (sub x y) b = add (add x (not y)) (xor b one) := by
  intro w x y b h
  rw [add_not_as_repr]
  rcases h with rfl | rfl
  · rw [xor_zero_l]
    change sub (@repr w (unsigned x - unsigned y)) (repr 0) = add (repr _) (repr 1)
    rw [sub_of_repr, add_of_repr]; congr 1; omega
  · rw [xor_idem]
    change sub (@repr w (unsigned x - unsigned y)) (repr 1) = add (repr _) (repr 0)
    rw [sub_of_repr, add_of_repr]; congr 1; omega

theorem sub_borrow_add_carry : ∀ {w : Positive}, ∀ x y b : bit_int w, b = zero ∨ b = one → sub_borrow x y b = xor (add_carry x (not y) (xor b one)) one := by
  intro w x y b h
  have flip : unsigned (xor b one) = 1 - unsigned b := by
    rcases h with rfl | rfl <;> simp only [xor_zero_l, xor_idem, unsigned_one, unsigned_zero] <;> decide
  unfold sub_borrow add_carry
  rw [unsigned_not, flip]
  unfold max_unsigned
  by_cases lt : unsigned x - unsigned y - unsigned b < 0
  · have lt' : unsigned x + ((@modulus w) - 1 - unsigned y) + (1 - unsigned b) < @modulus w := by omega
    simp only [ite_eq_left lt, ite_eq_left lt', xor_zero_l]
  · have lt' : ¬unsigned x + ((@modulus w) - 1 - unsigned y) + (1 - unsigned b) < @modulus w := by omega
    simp only [ite_eq_right lt, ite_eq_right lt', xor_idem]

theorem Z_add_is_or : ∀ i, 0 ≤ i → ∀ x y, (∀ j, 0 ≤ j ∧ j ≤ i → (Zbits.testbit x j && Zbits.testbit y j) = false) →
    Zbits.testbit (x+y) i = (Zbits.testbit x i || Zbits.testbit y i) := Zbits.Z_add_is_or

theorem add_is_or : ∀ {w : Positive}, ∀ x y : bit_int w, and x y = zero → add x y = or x y := by
  intro w x y h
  apply same_bits_eq
  intro i hi
  unfold add
  rw [testbit_repr _ _ hi, bits_or _ _ _ hi]
  apply Z_add_is_or i hi.1
  intro j hj
  have hj' : 0 ≤ j ∧ j < @zwordsize w := by omega
  have e := congrArg (fun z ↦ testbit z j) h
  change (testbit x j && testbit y j) = false
  simpa only [bits_and _ _ _ hj', bits_zero] using e

theorem xor_is_or : ∀ {w : Positive}, ∀ x y : bit_int w, and x y = zero → xor x y = or x y := by
  intro w x y h
  apply same_bits_eq
  intro i hi
  have e := congrArg (fun z ↦ testbit z i) h
  simp only [bits_and _ _ _ hi, bits_zero] at e
  rw [bits_xor _ _ _ hi, bits_or _ _ _ hi]
  grind

theorem add_is_xor : ∀ {w : Positive}, ∀ x y : bit_int w, and x y = zero → add x y = xor x y := fun {_} x y h ↦ (add_is_or x y h).trans (xor_is_or x y h).symm

theorem add_and : ∀ {w : Positive}, ∀ x y z : bit_int w, and y z = zero → add (and x y) (and x z) = and x (or y z) := by
  intro w x y z h
  rw [and_or_distrib, add_is_or]
  apply same_bits_eq
  intro i hi
  have e := congrArg (fun t ↦ testbit t i) h
  simp only [bits_and _ _ _ hi, bits_zero] at e ⊢
  grind

end Vellvm.Numeric.Integers
