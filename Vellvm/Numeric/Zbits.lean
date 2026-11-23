/-
The Compcert verified compiler
Xavier Leroy, Collège de France and Inria Paris

Copyright Institut National de Recherche en Informatique et en Automatique.
All rights reserved. This file is distributed under the terms of the GNU
General Public License as published by the Free Software Foundation, either
version 2 of the License, or (at your option) any later version. This file
is also distributed under the terms of the INRIA Non-Commercial License Agreement.
-/
module

public import Vellvm.Numeric.Rocqlib
public import Mathlib.Data.Int.Bitwise
public import Mathlib.Data.Nat.Size
public import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import all Init.Data.Nat.Power2.Basic

@[expose] public section
namespace Vellvm.Numeric.Zbits
open Vellvm.Numeric.Rocqlib
universe u

def eqmod (m x y : Int) : Prop := ∃ k, x = k * m + y

theorem eqmod_refl : ∀ m x, eqmod m x x := by intro m x; exact ⟨0, by simp⟩

theorem eqmod_refl2 : ∀ m x y, x = y → eqmod m x y := by rintro m x _ rfl; exact eqmod_refl m x

theorem eqmod_sym : ∀ m x y, eqmod m x y → eqmod m y x := by rintro m _ y ⟨k, rfl⟩; exact ⟨-k, by ring⟩

theorem eqmod_trans : ∀ m x y z, eqmod m x y → eqmod m y z → eqmod m x z := by rintro m _ _ z ⟨k, rfl⟩ ⟨l, rfl⟩; exact ⟨k+l, by ring⟩

theorem eqmod_mod_eq : ∀ m : Int, 0 < m → ∀ x y, eqmod m x y → x.fmod m = y.fmod m := by rintro m hm _ y ⟨k, rfl⟩; simp [Int.fmod_eq_emod_of_nonneg _ hm.le]

theorem eqmod_small_eq : ∀ m x y, eqmod m x y → 0 ≤ x ∧ x < m → 0 ≤ y ∧ y < m → x = y := by
  intro m x y e hx hy
  simpa only [Zmod_small _ _ hx, Zmod_small _ _ hy] using eqmod_mod_eq m (by omega) x y e

theorem eqmod_mod : ∀ m x, eqmod m x (x.fmod m) := fun m x ↦ ⟨x.fdiv m, (Int.fdiv_mul_add_fmod x m).symm⟩

theorem eqmod_add : ∀ m a b c d, eqmod m a b → eqmod m c d → eqmod m (a + c) (b + d) := by rintro m _ b _ d ⟨k, rfl⟩ ⟨l, rfl⟩; exact ⟨k+l, by ring⟩

theorem eqmod_sub : ∀ m a b c d, eqmod m a b → eqmod m c d → eqmod m (a - c) (b - d) := by rintro m _ b _ d ⟨k, rfl⟩ ⟨l, rfl⟩; exact ⟨k-l, by ring⟩

theorem eqmod_neg : ∀ m x y, eqmod m x y → eqmod m (-x) (-y) := by rintro m _ y ⟨k, rfl⟩; exact ⟨-k, by ring⟩

theorem eqmod_mult : ∀ m a b c d, eqmod m a c → eqmod m b d → eqmod m (a * b) (c * d) := by rintro m _ _ c d ⟨k, rfl⟩ ⟨l, rfl⟩; exact ⟨k*l*m+c*l+k*d, by ring⟩

theorem eqmod_divides : ∀ n m x y, eqmod n x y → m ∣ n → eqmod m x y := by rintro _ m _ y ⟨k, rfl⟩ ⟨l, rfl⟩; exact ⟨k*l, by ring⟩

def P_mod_two_p (p : Positive) (n : Nat) : Int := Int.ofNat (p.val &&& (2^n - 1))

def Z_mod_two_p (x : Int) (n : Nat) : Int :=
  match x with
  | .ofNat m => Int.ofNat (m &&& (2^n - 1))
  | .negSucc m => two_power_nat n - 1 - Int.ofNat (m &&& (2^n - 1))

theorem P_mod_two_p_eq : ∀ n p, P_mod_two_p p n = (Int.ofNat p.val).fmod (two_power_nat n) := by
  intro n p
  rw [Int.fmod_eq_emod_of_nonneg _ (two_power_nat_pos n).le]
  simp [P_mod_two_p, two_power_nat]

theorem Z_mod_two_p_eq : ∀ n x, Z_mod_two_p x n = x.fmod (two_power_nat n) := by
  intro n x
  rw [Int.fmod_eq_emod_of_nonneg _ (two_power_nat_pos n).le]
  cases x with
  | ofNat m => simp [Z_mod_two_p, two_power_nat]
  | negSucc m => rw [Int.negSucc_emod _ (two_power_nat_pos n)]; simp [Z_mod_two_p, two_power_nat]

theorem P_mod_two_p_range : ∀ n p, 0 ≤ P_mod_two_p p n ∧ P_mod_two_p p n < two_power_nat n := by
  intro n x
  rw [P_mod_two_p_eq]
  exact ⟨Int.fmod_nonneg_of_pos _ (two_power_nat_pos n), Int.fmod_lt_of_pos _ (two_power_nat_pos n)⟩

theorem Z_mod_two_p_range : ∀ n x, 0 ≤ Z_mod_two_p x n ∧ Z_mod_two_p x n < two_power_nat n := by
  intro n x
  rw [Z_mod_two_p_eq]
  exact ⟨Int.fmod_nonneg_of_pos _ (two_power_nat_pos n), Int.fmod_lt_of_pos _ (two_power_nat_pos n)⟩

def testbit (x i : Int) := decide (0 ≤ i) && Int.testBit x i.toNat

abbrev Zshiftin := Int.bit

private theorem testbit_nat (x : Int) (i : Nat) : testbit x (i : Int) = x.testBit i := by
  simp [testbit]

private theorem side_lt {A : Type u} (x y : Int) (a b : A) :
    chooseSide (zlt x y) a b = if x < y then a else b := by
  by_cases h : x < y <;> simp [h, zlt, chooseSide]

private theorem side_eq {A : Type u} (x y : Int) (a b : A) :
    chooseSide (zeq x y) a b = if x = y then a else b := by
  by_cases h : x = y <;> simp [h, zeq, decideSum, chooseSide]

theorem Ztestbit_0 : ∀ n, testbit 0 n = false := by intro n; simp [testbit, Int.testBit]

theorem Ztestbit_1 : ∀ n, testbit 1 n = proj_sumbool (zeq n 0) := by
  intro n
  rw [proj_sumbool, side_eq]
  rcases n with n | n
  · change (1 : Nat).testBit n = _
    cases n <;> simp [Nat.testBit_succ] <;> omega
  · simp [testbit]

theorem Ztestbit_m1 : ∀ n, 0 ≤ n → testbit (-1) n = true := by intro n hn; change decide (0 ≤ n) && !(Nat.testBit 0 n.toNat) = true; simp [hn]

theorem Zshiftin_spec : ∀ b x, Zshiftin b x = 2 * x + (if b then 1 else 0) := by intro b x; cases b <;> simp [Zshiftin, Int.bit]

theorem Zshiftin_inj : ∀ b₁ x₁ b₂ x₂, Zshiftin b₁ x₁ = Zshiftin b₂ x₂ → b₁ = b₂ ∧ x₁ = x₂ := by
  intro b x c y h
  rw [Zshiftin_spec, Zshiftin_spec] at h
  cases b <;> cases c <;> simp_all <;> omega

theorem Zdecomp : ∀ x, x = Zshiftin (Int.bodd x) (Int.div2 x) := fun x ↦ (Int.bit_decomp x).symm

theorem Ztestbit_shiftin_base : ∀ b x, testbit (Zshiftin b x) 0 = b := fun b x ↦ Int.testBit_bit_zero b x

theorem Ztestbit_shiftin_succ : ∀ b x n, 0 ≤ n → testbit (Zshiftin b x) (n + 1) = testbit x n := by
  rintro b x (n | n) hn
  · exact Int.testBit_bit_succ n b x
  · omega

theorem Ztestbit_shiftin : ∀ b x n, 0 ≤ n → testbit (Zshiftin b x) n = chooseSide (zeq n 0) b
    (testbit x (n - 1)) := by
  intro b x n hn
  rw [side_eq]
  split
  · next h => subst n; exact Ztestbit_shiftin_base _ _
  · have e := Ztestbit_shiftin_succ b x (n-1) (by omega)
    simpa using e

theorem Zshiftin_ind : ∀ P : Int → Prop, P 0 → (∀ b x, 0 ≤ x → P x → P (Zshiftin b x)) → ∀ x, 0 ≤ x
    → P x := by
  intro P base step x hx
  induction h : x.toNat using Nat.strong_induction_on generalizing x with
  | ind n ih =>
    by_cases e : x = 0
    · simpa [e] using base
    · rw [Zdecomp x]
      apply step
      · rw [Int.div2_val]; omega
      · apply ih (Int.div2 x).toNat (by rw [Int.div2_val]; omega) _ (by rw [Int.div2_val]; omega) rfl

theorem Zshiftin_pos_ind : ∀ P : Int → Prop, P 1 → (∀ b x, 0 < x → P x → P (Zshiftin b x)) → ∀ x, 0
    < x → P x := by
  intro P base step x hx
  induction h : x.toNat using Nat.strong_induction_on generalizing x with
  | ind n ih =>
    by_cases e : x = 1
    · simpa [e] using base
    · rw [Zdecomp x]
      apply step
      · rw [Int.div2_val]; omega
      · apply ih (Int.div2 x).toNat (by rw [Int.div2_val]; omega) _ (by rw [Int.div2_val]; omega) rfl

theorem Ztestbit_base : ∀ x, testbit x 0 = Int.bodd x := by
  intro x
  exact (congrArg (fun z ↦ testbit z 0) (Zdecomp x)).trans (Ztestbit_shiftin_base _ _)

theorem Ztestbit_succ : ∀ n x, 0 ≤ n → testbit x (n + 1) = testbit (Int.div2 x) n := by
  intro n x hn
  exact (congrArg (fun z ↦ testbit z (n+1)) (Zdecomp x)).trans (Ztestbit_shiftin_succ _ _ _ hn)

theorem Ztestbit_eq : ∀ n x, 0 ≤ n → testbit x n = chooseSide (zeq n 0) (Int.bodd x) (testbit
    (Int.div2 x) (n - 1)) := by
  intro n x hn
  exact (congrArg (fun z ↦ testbit z n) (Zdecomp x)).trans (Ztestbit_shiftin _ _ _ hn)

private theorem low_bits (n : Nat) (x : Int) (i : Nat) :
    (x.fmod (two_power_nat n)).testBit i = (decide (i < n) && x.testBit i) := by
  rw [Int.fmod_eq_emod_of_nonneg _ (two_power_nat_pos n).le]
  cases x with
  | ofNat m => exact Nat.testBit_mod_two_pow m n i
  | negSucc m =>
    have h := Nat.mod_lt m (Nat.two_pow_pos n)
    rw [Int.negSucc_emod _ (two_power_nat_pos n)]
    have e : two_power_nat n - 1 - (m : Int) % two_power_nat n =
        Int.ofNat (2^n - (m % 2^n + 1)) := by
      change ((2^n : Nat) : Int) - 1 - ((m % 2^n : Nat) : Int) = ((2^n - (m % 2^n + 1) : Nat) : Int)
      rw [Int.natCast_sub (by omega), Int.natCast_add]; omega
    rw [e]; change Nat.testBit _ i = _
    rw [Nat.testBit_two_pow_sub_succ h, Nat.testBit_mod_two_pow]
    by_cases hi : i < n <;> simp [hi, Int.testBit]

theorem eqmod_same_bits : ∀ (n : Nat) (x y : Int), (∀ i : Int, 0 ≤ i ∧ i < (n : Int) → testbit x i =
    testbit y i) → eqmod (two_power_nat n) x y := by
  intro n x y bits
  let m := two_power_nat n
  have e : x.fmod m = y.fmod m := by
    have hx := Int.fmod_nonneg_of_pos x (two_power_nat_pos n)
    have hy := Int.fmod_nonneg_of_pos y (two_power_nat_pos n)
    change 0 ≤ x.fmod m at hx
    change 0 ≤ y.fmod m at hy
    suffices (x.fmod m).toNat = (y.fmod m).toNat by omega
    apply Nat.eq_of_testBit_eq
    intro i
    have bit (z : Int) (hz : 0 ≤ z) : z.toNat.testBit i = z.testBit i := by
      rcases z with z | z <;> first | rfl | omega
    rw [bit _ hx, bit _ hy, low_bits, low_bits]
    by_cases hi : i < n
    · simpa only [hi, decide_true, Bool.true_and, testbit_nat] using bits (i : Int) ⟨by omega, by omega⟩
    · simp [hi]
  exact eqmod_trans m x (x.fmod m) y (eqmod_mod m x) (e.symm ▸ eqmod_sym m y _ (eqmod_mod m y))

theorem same_bits_eqmod : ∀ (n : Nat) (x y i : Int), eqmod (two_power_nat n) x y → 0 ≤ i ∧ i < (n :
    Int) → testbit x i = testbit y i := by
  intro n x y i e hi
  have b := congrArg (fun z : Int ↦ z.testBit i.toNat) (eqmod_mod_eq _ (two_power_nat_pos n) x y e)
  change (x.fmod (two_power_nat n)).testBit i.toNat = (y.fmod (two_power_nat n)).testBit i.toNat at b
  rw [low_bits, low_bits] at b
  simpa only [testbit, hi.1, show i.toNat < n by omega, decide_true, Bool.true_and] using b

theorem Z_one_complement : ∀ i, 0 ≤ i → ∀ x, testbit (-x - 1) i = !(testbit x i) := by
  intro i hi x
  have e : -x-1 = Int.lnot x := by cases x <;> simp [Int.lnot] <;> omega
  simp [testbit, hi, e]

theorem Ztestbit_above : ∀ (n : Nat) (x i : Int), 0 ≤ x ∧ x < two_power_nat n → (n : Int) ≤ i →
    testbit x i = false := by
  rintro n (x | x) i hx hi
  · simp only [testbit, show 0 ≤ i by omega, decide_true, Bool.true_and, Int.testBit]
    exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Int.ofNat_lt.mp hx.2)
      (Nat.pow_le_pow_right (by decide) (show n ≤ i.toNat by omega)))
  · omega

theorem Ztestbit_above_neg : ∀ (n : Nat) (x i : Int), -two_power_nat n ≤ x ∧ x < 0 → (n : Int) ≤ i →
    testbit x i = true := by
  intro n x i hx hi
  have h := Ztestbit_above n (-x-1) i ⟨by omega, by omega⟩ hi
  simpa [Z_one_complement i (by omega)] using h

theorem equal_same_bits : ∀ x y, (∀ i, 0 ≤ i → testbit x i = testbit y i) → x = y := by
  intro x y h
  have same (i : Nat) := h (i : Int) (by omega)
  simp only [testbit_nat] at same
  have mixed (a b : Nat) (h : ∀ i, a.testBit i = !(b.testBit i)) : False := by
    let i := a + b + 1
    have ht := Nat.lt_two_pow_self (n := i)
    have ha := Nat.testBit_lt_two_pow (show a < 2^i by dsimp [i] at *; omega)
    have hb := Nat.testBit_lt_two_pow (show b < 2^i by dsimp [i] at *; omega)
    simpa [ha, hb] using h i
  cases x with
  | ofNat a => cases y with
    | ofNat b => exact congrArg Int.ofNat (Nat.eq_of_testBit_eq same)
    | negSucc b => exact (mixed a b same).elim
  | negSucc a => cases y with
    | ofNat b => exact (mixed b a (fun i ↦ (same i).symm)).elim
    | negSucc b => apply congrArg Int.negSucc; apply Nat.eq_of_testBit_eq; intro i
                   simpa [Int.testBit] using same i

theorem Zsign_bit : ∀ n x, 0 ≤ x ∧ x < two_power_nat (n+1) → testbit x (Int.ofNat n) = chooseSide
    (zlt x (two_power_nat n)) false true := by
  rintro n (x | x) hx
  · rw [side_lt]; change Nat.testBit x n = _
    split
    · next h => exact Nat.testBit_lt_two_pow (Int.ofNat_lt.mp h)
    · next h => exact Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt
                  (by exact Int.ofNat_le.mp (by omega : two_power_nat n ≤ Int.ofNat x))
                  (Int.ofNat_lt.mp hx.2)
  · omega

theorem Ztestbit_le : ∀ x y, 0 ≤ y → (∀ i, 0 ≤ i → testbit x i = true → testbit y i = true) → x ≤ y := by
  rintro (x | x) (y | y) hy h <;> try omega
  apply Int.ofNat_le.mpr; apply Nat.le_of_testBit
  exact fun i ↦ h (i : Int) (by omega)

theorem Ztestbit_mod_two_p : ∀ n x i, 0 ≤ n → 0 ≤ i → testbit (Int.fmod x (two_p n)) i = chooseSide
    (zlt i n) (testbit x i) false := by
  rintro (n | n) x (i | i) hn hi <;> try omega
  rw [side_lt]
  change (x.fmod (two_power_nat n)).testBit i = if (i : Int) < (n : Int) then x.testBit i else false
  rw [low_bits]; by_cases h : i < n <;> simp [h]

theorem Ztestbit_two_p_m1 : ∀ n i, 0 ≤ n → 0 ≤ i → testbit (two_p n - 1) i = chooseSide (zlt i n)
    true false := by
  intro n i hn hi
  have hp := lt_of_le_of_lt hn (two_p_strict n hn)
  have e : (-1 : Int).fmod (two_p n) = two_p n - 1 :=
    Zmod_unique _ _ (-1) _ (by ring) ⟨by omega, by omega⟩
  rw [← e, Ztestbit_mod_two_p _ _ _ hn hi, Ztestbit_m1 _ hi]

theorem Ztestbit_neg_two_p : ∀ n i, 0 ≤ n → 0 ≤ i → testbit (-(two_p n)) i = chooseSide (zlt i n)
    false true := by
  intro n i hn hi
  rw [show -two_p n = -(two_p n-1)-1 by omega, Z_one_complement _ hi, Ztestbit_two_p_m1 _ _ hn hi,
    side_lt, side_lt]
  split <;> rfl

theorem Z_add_is_or : ∀ i, 0 ≤ i → ∀ x y, (∀ j, 0 ≤ j ∧ j ≤ i → (testbit x j && testbit y j) =
    false) → testbit (x+y) i = (testbit x i || testbit y i) := by
  rintro (i | i) hi <;> try omega
  clear hi
  induction i with
  | zero =>
    intro x y h
    change testbit (x+y) 0 = (testbit x 0 || testbit y 0)
    have e := h 0 ⟨by decide, by decide⟩
    rw [Ztestbit_base, Ztestbit_base] at e
    simp only [Ztestbit_base, Int.bodd_add]
    cases hx : x.bodd <;> cases hy : y.bodd <;> simp [hx, hy] at e ⊢
  | succ i ih =>
    intro x y h
    have e := h 0 ⟨by decide, Int.natCast_nonneg _⟩
    rw [Ztestbit_base, Ztestbit_base] at e
    have halves : (x+y).div2 = x.div2 + y.div2 := by
      have dx := Zdecomp x; have dy := Zdecomp y
      rw [Zshiftin_spec] at dx dy
      simp only [Int.div2_val] at dx dy ⊢
      cases hx : x.bodd <;> cases hy : y.bodd <;> simp [hx, hy] at dx dy e <;> omega
    change testbit (x+y) ((i : Int)+1) = (testbit x ((i : Int)+1) || testbit y ((i : Int)+1))
    simp only [Ztestbit_succ _ _ (Int.natCast_nonneg i), halves]
    apply ih
    intro j hj
    change 0 ≤ j ∧ j ≤ (i : Int) at hj
    have bound : j+1 ≤ (i : Int)+1 := by omega
    simpa only [Ztestbit_succ _ _ hj.1] using h (j+1) ⟨by omega, bound⟩

def Ziter {A : Type u} (n : Int) (f : A → A) (x : A) : A := f^[n.toNat] x

def Zzero_ext (n x : Int) : Int := Int.land x (two_power_nat n.toNat - 1)

-- The source uses the low bit as its sign bit even at nonpositive widths.
def Zsign_ext (n x : Int) : Int :=
  let k := max n 1
  if testbit x (k-1) then Int.lor x (-two_p k) else Zzero_ext k x

theorem Ziter_base : ∀ (A : Type u) (n : Int) (f : A → A) (x : A), n ≤ 0 → Ziter n f x = x := by intro A n f x hn; simp [Ziter, show n.toNat = 0 by omega]

theorem Ziter_succ : ∀ (A : Type u) (n : Int) (f : A → A) (x : A), 0 ≤ n → Ziter (n+1) f x = f
    (Ziter n f x) := by
  intro A n f x hn
  simp only [Ziter, show (n+1).toNat = n.toNat+1 by omega, Function.iterate_succ_apply']

theorem Znatlike_ind : ∀ P : Int → Prop, (∀ n, n ≤ 0 → P n) → (∀ n, 0 ≤ n → P n → P (n+1)) → ∀ n, P
    n := by
  rintro P base step (n | n)
  · induction n with
    | zero => exact base 0 (by omega)
    | succ n ih => exact step n (by omega) ih
  · exact base _ (by omega)

theorem Zzero_ext_spec : ∀ n x i, 0 ≤ i → testbit (Zzero_ext n x) i = chooseSide (zlt i n) (testbit
    x i) false := by
  intro n x i hi
  have h := Ztestbit_two_p_m1 (Int.ofNat n.toNat) i (Int.natCast_nonneg _) hi
  rw [← two_power_nat_two_p, side_lt] at h
  simp only [testbit, hi, decide_true, Bool.true_and] at h ⊢
  rw [Zzero_ext, Int.testBit_land, h, side_lt]
  simp only [Int.ofNat_eq_natCast] at *
  by_cases e : i < n
  · simp only [e, show i < (n.toNat : Int) by omega, if_true, Bool.and_true]
  · simp only [e, show ¬i < (n.toNat : Int) by omega, if_false, Bool.and_false]

theorem Zsign_ext_spec : ∀ n x i, 0 ≤ i → 0 < n → testbit (Zsign_ext n x) i = testbit x (chooseSide
    (zlt i n) i (n-1)) := by
  intro n x i hi hn
  unfold Zsign_ext; simp only [max_eq_left (by omega : 1 ≤ n)]
  rw [side_lt]
  split
  · next sign =>
    have h := Ztestbit_neg_two_p n i (by omega) hi
    rw [side_lt] at h
    have lor : testbit (Int.lor x (-two_p n)) i = (testbit x i || testbit (-two_p n) i) := by
      simp only [testbit, hi, decide_true, Bool.true_and, Int.testBit_lor]
    rw [lor, h]
    by_cases e : i < n <;> simp [e, sign]
  · next sign =>
    rw [Zzero_ext_spec _ _ _ hi, side_lt]
    by_cases e : i < n <;> simp [e, sign]

theorem Zzero_ext_mod : ∀ n x, 0 ≤ n → Zzero_ext n x = Int.fmod x (two_p n) := by
  intro n x hn; apply equal_same_bits; intro i hi
  rw [Zzero_ext_spec _ _ _ hi, Ztestbit_mod_two_p _ _ _ hn hi]

theorem Zzero_ext_range : ∀ n x, 0 ≤ n → 0 ≤ Zzero_ext n x ∧ Zzero_ext n x < two_p n := by
  intro n x hn
  have hp := lt_of_le_of_lt hn (two_p_strict n hn)
  rw [Zzero_ext_mod _ _ hn]
  exact ⟨Int.fmod_nonneg_of_pos _ hp, Int.fmod_lt_of_pos _ hp⟩

theorem eqmod_Zzero_ext : ∀ n x, 0 ≤ n → eqmod (two_p n) (Zzero_ext n x) x := by
  intro n x hn; rw [Zzero_ext_mod _ _ hn]; exact eqmod_sym _ _ _ (eqmod_mod _ _)

theorem Zsign_ext_zero_ext : ∀ n, 0 < n → ∀ x, Zsign_ext n x = Zzero_ext n x - (if testbit x (n-1)
    then two_p n else 0) := by
  intro n hn x; apply equal_same_bits; intro i hi
  rw [Zsign_ext_spec _ _ _ hi hn, side_lt]
  cases sign : testbit x (n-1) with
  | false => simp only [Bool.false_eq_true, if_false, sub_zero, Zzero_ext_spec _ _ _ hi, side_lt]
             split <;> simp_all
  | true =>
    simp only [if_true, sub_eq_add_neg]
    rw [Z_add_is_or i hi, Zzero_ext_spec _ _ _ hi, Ztestbit_neg_two_p n i (by omega) hi,
      side_lt, side_lt]
    · split <;> simp_all [← sub_eq_add_neg]
    · intro j hj
      rw [Zzero_ext_spec _ _ _ hj.1, Ztestbit_neg_two_p n j (by omega) hj.1, side_lt, side_lt]
      split <;> simp

private theorem pow_succ (n : Nat) : two_power_nat (n+1) = 2 * two_power_nat n := by
  simp [two_power_nat, Nat.pow_succ, mul_comm]

private theorem pow_add_one (i : Int) (hi : 0 ≤ i) : two_p (i+1) = 2 * two_p i := by
  rcases i with i | i <;> first | exact pow_succ i | omega

theorem Zsign_ext_range : ∀ n x, 0 < n → -two_p (n-1) ≤ Zsign_ext n x ∧ Zsign_ext n x < two_p (n-1) := by
  intro n x hn
  let k := (n-1).toNat
  have hk : Int.ofNat k = n-1 := by dsimp [k]; omega
  have hk' : Int.ofNat (k+1) = n := by change (k : Int)+1 = n; change (k : Int) = n-1 at hk; omega
  have h := Zzero_ext_range n x hn.le
  have e := Zsign_bit k (Zzero_ext n x) (by rw [two_power_nat_two_p, hk']; exact h)
  rw [hk, Zzero_ext_spec _ _ _ (by omega), zlt_true _ _ _ _ _ (by omega),
    two_power_nat_two_p, hk, side_lt] at e
  have p := pow_add_one (n-1) (by omega)
  simp only [sub_add_cancel] at p
  rw [Zsign_ext_zero_ext n hn, e]
  split <;> simp <;> omega

theorem eqmod_Zsign_ext : ∀ n x, 0 < n → eqmod (two_p n) (Zsign_ext n x) x := by
  intro n x hn
  rw [Zsign_ext_zero_ext n hn]
  obtain ⟨k, hk⟩ := eqmod_Zzero_ext n x hn.le
  rw [hk]; cases testbit x (n-1)
  · exact ⟨k, by simp⟩
  · exact ⟨k-1, by simp; ring⟩

def Z_one_bits : Nat → Int → Int → List Int
  | 0, _, _ => []
  | n+1, x, i =>
    let tail := Z_one_bits n x.div2 (i+1)
    if x.bodd then i :: tail else tail

def powerserie : List Int → Int
  | [] => 0
  | i :: l => two_p i + powerserie l

private theorem one_bits_sum (n : Nat) (x i : Int) (hi : 0 ≤ i)
    (hx : 0 ≤ x ∧ x < two_power_nat n) : x * two_p i = powerserie (Z_one_bits n x i) := by
  induction n generalizing x i with
  | zero => have h : x = 0 := by change 0 ≤ x ∧ x < 1 at hx; omega
            simp [h, Z_one_bits, powerserie]
  | succ n ih =>
    rw [pow_succ] at hx
    have e := ih x.div2 (i+1) (by omega) (by rw [Int.div2_val]; omega)
    rw [pow_add_one _ hi] at e
    have d := Zdecomp x
    rw [Zshiftin_spec] at d
    cases h : x.bodd <;> simp only [h, Z_one_bits, powerserie, Bool.false_eq_true, if_false,
      if_true, ← e, add_zero] at * <;> calc
        _ = _ := congrArg (· * two_p i) d
        _ = _ := by ring

theorem Z_one_bits_powerserie : ∀ n x, 0 ≤ x ∧ x < two_power_nat n → x = powerserie (Z_one_bits n x
    0) := by
  intro n x hx; simpa [show two_p 0 = 1 from rfl] using one_bits_sum n x 0 (by decide) hx

private theorem one_bits_bounds (n : Nat) (x i j : Int) (h : j ∈ Z_one_bits n x i) :
    i ≤ j ∧ j < i + n := by
  induction n generalizing i x with
  | zero => simp [Z_one_bits] at h
  | succ n ih =>
    have tail := ih x.div2 (i+1)
    cases e : x.bodd <;> simp [Z_one_bits, e] at h
    · have := tail h; omega
    · rcases h with h | h
      · omega
      · have := tail h; omega

theorem Z_one_bits_range : ∀ (n : Nat) (x i : Int), i ∈ Z_one_bits n x 0 → 0 ≤ i ∧ i < (n : Int) := by intro n x i h; simpa using one_bits_bounds n x 0 i h

theorem Z_one_bits_zero : ∀ n i, Z_one_bits n 0 i = [] := by
  intro n i; induction n generalizing i with
  | zero => rfl
  | succ n ih => simpa [Z_one_bits, show (0:Int).div2 = 0 from rfl] using ih (i+1)

theorem Z_one_bits_two_p : ∀ (n : Nat) (x i : Int), 0 ≤ x ∧ x < (n : Int) → Z_one_bits n (two_p x) i
    = [i+x] := by
  intro n; induction n with
  | zero => intro x i h; omega
  | succ n ih =>
    intro x i hx
    by_cases e : x = 0
    · subst x; simp [Z_one_bits, show two_p 0 = 1 from rfl, show (1:Int).div2 = 0 from rfl,
        Z_one_bits_zero]
    · have p := pow_add_one (x-1) (by omega)
      have d : two_p x = Zshiftin false (two_p (x-1)) := by
        simpa [Zshiftin_spec] using p
      have bits := Zshiftin_inj _ _ _ _ ((Zdecomp (two_p x)).symm.trans d)
      simp only [Z_one_bits, bits.1, Bool.false_eq_true, if_false, bits.2,
        ih (x-1) (i+1) (by omega : 0 ≤ x-1 ∧ x-1 < (n : Int))]
      congr 1 <;> omega

abbrev Zlog2 (x : Int) : Int := Int.ofNat x.toNat.log2

def P_is_power2 (p : Positive) : Bool := decide p.val.isPowerOfTwo

def Z_is_power2 (x : Int) : Option Int :=
  if h : 0 < x then
    if P_is_power2 ⟨x.toNat, by omega⟩ then some (Zlog2 x) else none
  else none

def Z_is_power2m1 (x : Int) := Z_is_power2 (x+1)

theorem P_is_power2_sound : ∀ p, P_is_power2 p = true → Int.ofNat p.val = two_p (Zlog2 (Int.ofNat
    p.val)) := by
  intro p h
  have he := of_decide_eq_true (show decide p.val.isPowerOfTwo = true from h)
  change ∃ k, p.val = 2^k at he
  obtain ⟨k, hk⟩ := he
  change Int.ofNat p.val = Int.ofNat (2^p.val.log2)
  rw [hk, Nat.log2_two_pow]

theorem Z_is_power2_sound : ∀ x i, Z_is_power2 x = some i → x = two_p i ∧ i = Zlog2 x := by
  intro x i h
  unfold Z_is_power2 at h
  split at h <;> try contradiction
  next hx =>
    split at h <;> try contradiction
    next hp =>
      cases h
      refine ⟨?_, rfl⟩
      simpa only [Int.ofNat_eq_natCast, Int.toNat_of_nonneg hx.le] using
        P_is_power2_sound ⟨x.toNat, by omega⟩ hp

theorem Z_is_power2_range : ∀ n x i, 0 ≤ n → 0 ≤ x ∧ x < two_p n → Z_is_power2 x = some i → 0 ≤ i ∧
    i < n := by
  intro n x i hn hx he
  obtain ⟨hp, rfl⟩ := Z_is_power2_sound x i he
  constructor
  · exact Int.natCast_nonneg _
  · by_contra! h
    have q := two_p_monotone n (Zlog2 x) ⟨hn, h⟩
    omega

theorem Z_is_power2_complete : ∀ i, 0 ≤ i → Z_is_power2 (two_p i) = some i := by
  rintro (i | i) hi <;> try omega
  have hp : (2^i : Nat).isPowerOfTwo := ⟨i, rfl⟩
  have hpos := two_power_nat_pos i
  change Z_is_power2 (two_power_nat i) = some (Int.ofNat i)
  unfold Z_is_power2; rw [dif_pos hpos]
  change (if decide (2^i : Nat).isPowerOfTwo then some (Int.ofNat (2^i : Nat).log2) else none) = _
  simp [hp, Nat.log2_two_pow]

theorem Z_is_power2m1_sound : ∀ x i, Z_is_power2m1 x = some i → x = two_p i - 1 := by
  intro x i h; have := (Z_is_power2_sound (x+1) i h).1; omega

theorem Z_is_power2m1_complete : ∀ i, 0 ≤ i → Z_is_power2m1 (two_p i - 1) = some i := by
  intro i hi; simpa [Z_is_power2m1] using Z_is_power2_complete i hi

theorem Z_is_power2m1_range : ∀ n x i, 0 ≤ n → 0 ≤ x ∧ x < two_p n → Z_is_power2m1 x = some i → 0 ≤
    i ∧ i ≤ n := by
  intro n x i hn hx h
  by_cases he : x = two_p n-1
  · subst x; rw [Z_is_power2m1_complete n hn] at h; cases h; omega
  · have := Z_is_power2_range n (x+1) i hn ⟨by omega, by omega⟩ h; omega

theorem Zshiftl_mul_two_p : ∀ x n : Int, 0 ≤ n → x <<< n = x * two_p n := by rintro x (n | n) hn <;> first | exact Int.shiftLeft_eq_mul_pow x n | omega

theorem Zshiftr_div_two_p : ∀ x n : Int, 0 ≤ n → x >>> n = x.fdiv (two_p n) := by
  rintro x (n | n) hn <;> try omega
  change x >>> (n : Int) = x.fdiv (two_power_nat n)
  rw [Int.shiftRight_natCast_right, Int.shiftRight_eq_div_pow,
    Int.fdiv_eq_ediv_of_nonneg _ (two_power_nat_pos n).le]
  rfl

theorem Zdiv_shift : ∀ x y : Int, y > 0 → (x + (y-1)).fdiv y = x.fdiv y + chooseSide (zeq (x.fmod y)
    0) 0 1 := by
  intro x y hy
  have e := Int.fdiv_mul_add_fmod x y
  have hlo := Int.fmod_nonneg_of_pos x hy
  have hhi := Int.fmod_lt_of_pos x hy
  rw [side_eq]; split
  · next hr => simp only [add_zero]; apply Zdiv_unique _ _ _ (y-1) <;> omega
  · next hr => apply Zdiv_unique _ _ _ (x.fmod y-1)
               · rw [add_mul]; simp; omega
               · omega

theorem Zquot_Zdiv : ∀ x y : Int, y > 0 → x.tdiv y = chooseSide (zlt x 0) ((x+y-1).fdiv y) (x.fdiv
    y) := by
  intro x y hy
  rw [side_lt]; split
  · next hx =>
    rw [show x+y-1 = x+(y-1) by omega, Zdiv_shift _ _ hy, side_eq,
      Int.fdiv_eq_ediv_of_nonneg _ hy.le, Int.fmod_eq_emod_of_nonneg _ hy.le,
      Int.tdiv_eq_ediv, Int.sign_eq_one_of_pos hy]
    by_cases h : x % y = 0 <;> simp [Int.dvd_iff_emod_eq_zero, h, show ¬0 ≤ x by omega]
  · next hx => rw [Int.tdiv_eq_ediv_of_nonneg (by omega), Int.fdiv_eq_ediv_of_nonneg _ hy.le]

def Zsize (x : Int) : Int := Int.ofNat x.toNat.size

theorem Zsize_pos : ∀ x, 0 ≤ Zsize x := fun x ↦ Int.natCast_nonneg _

theorem Zsize_pos' : ∀ x, 0 < x → 0 < Zsize x := fun _ hx ↦ Int.ofNat_lt.mpr (Nat.size_pos.mpr (by omega))

theorem Zsize_shiftin : ∀ b x, 0 < x → Zsize (Zshiftin b x) = Zsize x + 1 := by
  rintro b (x | x) hx <;> try omega
  change Zsize (Int.bit b (x : Int)) = _
  rw [Int.bit_natCast]; change ((Nat.bit b x).size : Int) = (x.size : Int)+1
  have hpos : 0 < x := Int.ofNat_lt.mp hx
  have hb : Nat.bit b x ≠ 0 := by cases b <;> simp [Nat.bit_val] <;> omega
  rw [Nat.size_bit hb]; omega

theorem Ztestbit_size_1 : ∀ x, 0 < x → testbit x (Zsize x - 1) = true := by
  apply Zshiftin_pos_ind
  · decide
  · intro b x hx ih
    rw [Zsize_shiftin _ _ hx, show Zsize x + 1 - 1 = (Zsize x - 1) + 1 by omega,
      Ztestbit_shiftin_succ _ _ _ (by have := Zsize_pos' x hx; omega)]
    exact ih

theorem Ztestbit_size_2 : ∀ x, 0 ≤ x → ∀ i, i ≥ Zsize x → testbit x i = false := by
  intro x hx i hi; apply Ztestbit_above x.toNat.size _ _ ⟨hx, ?_⟩ hi
  simpa [Int.toNat_of_nonneg hx] using Int.ofNat_lt.mpr (Nat.lt_size_self x.toNat)

theorem Zsize_interval_1 : ∀ x, 0 ≤ x → 0 ≤ x ∧ x < two_p (Zsize x) := by
  intro x hx
  exact ⟨hx, by simpa [Zsize, two_p, two_power_nat, Int.toNat_of_nonneg hx] using
    Int.ofNat_lt.mpr (Nat.lt_size_self x.toNat)⟩

theorem Zsize_interval_2 : ∀ x n, 0 ≤ n → 0 ≤ x ∧ x < two_p n → n ≥ Zsize x := by
  rintro (x | x) (n | n) hn hx <;> try omega
  exact Int.ofNat_le.mpr (Nat.size_le.mpr (Int.ofNat_lt.mp hx.2))

theorem Zsize_monotone : ∀ x y, 0 ≤ x ∧ x ≤ y → Zsize x ≤ Zsize y := by
  intro x y h; exact Int.ofNat_le.mpr (Nat.size_le_size (by omega))

end Vellvm.Numeric.Zbits
