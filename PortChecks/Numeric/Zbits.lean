/-
The Compcert verified compiler
Xavier Leroy, Collège de France and Inria Paris

Copyright Institut National de Recherche en Informatique et en Automatique.
All rights reserved. This file is distributed under the terms of the GNU
General Public License as published by the Free Software Foundation, either
version 2 of the License, or (at your option) any later version. This file
is also distributed under the terms of the INRIA Non-Commercial License Agreement.
-/
import PortChecks.SourceType
import Vellvm.Numeric.Zbits

open Vellvm Vellvm.Numeric.Rocqlib Vellvm.Numeric.Zbits
universe u

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|eqmod_refl"
  eqmod_refl : ∀ m x, eqmod m x x

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|eqmod_refl2"
  eqmod_refl2 : ∀ m x y, x = y → eqmod m x y

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|eqmod_sym"
  eqmod_sym : ∀ m x y, eqmod m x y → eqmod m y x

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|eqmod_trans"
  eqmod_trans : ∀ m x y z, eqmod m x y → eqmod m y z → eqmod m x z

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|eqmod_small_eq"
  eqmod_small_eq : ∀ m x y, eqmod m x y → 0 ≤ x ∧ x < m → 0 ≤ y ∧ y < m → x = y

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|eqmod_mod_eq"
  eqmod_mod_eq : ∀ m : Int, 0 < m → ∀ x y, eqmod m x y → x.fmod m = y.fmod m

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|eqmod_mod"
  eqmod_mod : ∀ m x, eqmod m x (x.fmod m)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|eqmod_add"
  eqmod_add : ∀ m a b c d, eqmod m a b → eqmod m c d → eqmod m (a + c) (b + d)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|eqmod_neg"
  eqmod_neg : ∀ m x y, eqmod m x y → eqmod m (-x) (-y)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|eqmod_sub"
  eqmod_sub : ∀ m a b c d, eqmod m a b → eqmod m c d → eqmod m (a - c) (b - d)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|eqmod_mult"
  eqmod_mult : ∀ m a b c d, eqmod m a c → eqmod m b d → eqmod m (a * b) (c * d)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|eqmod_divides"
  eqmod_divides : ∀ n m x y, eqmod n x y → m ∣ n → eqmod m x y

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|P_mod_two_p_range"
  P_mod_two_p_range : ∀ n p, 0 ≤ P_mod_two_p p n ∧ P_mod_two_p p n < two_power_nat n

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|P_mod_two_p_eq"
  P_mod_two_p_eq : ∀ n p, P_mod_two_p p n = (Int.ofNat p.val).fmod (two_power_nat n)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Z_mod_two_p_range"
  Z_mod_two_p_range : ∀ n x, 0 ≤ Z_mod_two_p x n ∧ Z_mod_two_p x n < two_power_nat n

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Z_mod_two_p_eq"
  Z_mod_two_p_eq : ∀ n x, Z_mod_two_p x n = x.fmod (two_power_nat n)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ztestbit_0"
  Ztestbit_0 : ∀ n, testbit 0 n = false

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ztestbit_1"
  Ztestbit_1 : ∀ n, testbit 1 n = proj_sumbool (zeq n 0)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ztestbit_m1"
  Ztestbit_m1 : ∀ n, 0 ≤ n → testbit (-1) n = true

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zshiftin_spec"
  Zshiftin_spec : ∀ b x, Zshiftin b x = 2 * x + (if b then 1 else 0)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zshiftin_inj"
  Zshiftin_inj : ∀ b₁ x₁ b₂ x₂, Zshiftin b₁ x₁ = Zshiftin b₂ x₂ → b₁ = b₂ ∧ x₁ = x₂

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zdecomp"
  Zdecomp : ∀ x, x = Zshiftin (Int.bodd x) (Int.div2 x)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ztestbit_shiftin"
  Ztestbit_shiftin : ∀ b x n, 0 ≤ n → testbit (Zshiftin b x) n = chooseSide (zeq n 0) b (testbit x
    (n - 1))

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ztestbit_shiftin_base"
  Ztestbit_shiftin_base : ∀ b x, testbit (Zshiftin b x) 0 = b

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ztestbit_shiftin_succ"
  Ztestbit_shiftin_succ : ∀ b x n, 0 ≤ n → testbit (Zshiftin b x) (n + 1) = testbit x n

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zshiftin_ind"
  Zshiftin_ind : ∀ P : Int → Prop, P 0 → (∀ b x, 0 ≤ x → P x → P (Zshiftin b x)) → ∀ x, 0 ≤ x → P x

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zshiftin_pos_ind"
  Zshiftin_pos_ind : ∀ P : Int → Prop, P 1 → (∀ b x, 0 < x → P x → P (Zshiftin b x)) → ∀ x, 0 < x →
    P x

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ztestbit_eq"
  Ztestbit_eq : ∀ n x, 0 ≤ n → testbit x n = chooseSide (zeq n 0) (Int.bodd x) (testbit (Int.div2 x)
    (n - 1))

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ztestbit_base"
  Ztestbit_base : ∀ x, testbit x 0 = Int.bodd x

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ztestbit_succ"
  Ztestbit_succ : ∀ n x, 0 ≤ n → testbit x (n + 1) = testbit (Int.div2 x) n

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|eqmod_same_bits"
  eqmod_same_bits : ∀ (n : Nat) (x y : Int), (∀ i : Int, 0 ≤ i ∧ i < (n : Int) → testbit x i =
    testbit y i) → eqmod (two_power_nat n) x y

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|same_bits_eqmod"
  same_bits_eqmod : ∀ (n : Nat) (x y i : Int), eqmod (two_power_nat n) x y → 0 ≤ i ∧ i < (n : Int) →
    testbit x i = testbit y i

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|equal_same_bits"
  equal_same_bits : ∀ x y, (∀ i, 0 ≤ i → testbit x i = testbit y i) → x = y

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Z_one_complement"
  Z_one_complement : ∀ i, 0 ≤ i → ∀ x, testbit (-x - 1) i = !(testbit x i)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ztestbit_above"
  Ztestbit_above : ∀ (n : Nat) (x i : Int), 0 ≤ x ∧ x < two_power_nat n → (n : Int) ≤ i → testbit x
    i = false

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ztestbit_above_neg"
  Ztestbit_above_neg : ∀ (n : Nat) (x i : Int), -two_power_nat n ≤ x ∧ x < 0 → (n : Int) ≤ i →
    testbit x i = true

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zsign_bit"
  Zsign_bit : ∀ n x, 0 ≤ x ∧ x < two_power_nat (n+1) → testbit x (Int.ofNat n) = chooseSide (zlt x
    (two_power_nat n)) false true

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ztestbit_le"
  Ztestbit_le : ∀ x y, 0 ≤ y → (∀ i, 0 ≤ i → testbit x i = true → testbit y i = true) → x ≤ y

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ztestbit_mod_two_p"
  Ztestbit_mod_two_p : ∀ n x i, 0 ≤ n → 0 ≤ i → testbit (Int.fmod x (two_p n)) i = chooseSide (zlt i
    n) (testbit x i) false

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ztestbit_two_p_m1"
  Ztestbit_two_p_m1 : ∀ n i, 0 ≤ n → 0 ≤ i → testbit (two_p n - 1) i = chooseSide (zlt i n) true
    false

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ztestbit_neg_two_p"
  Ztestbit_neg_two_p : ∀ n i, 0 ≤ n → 0 ≤ i → testbit (-(two_p n)) i = chooseSide (zlt i n) false
    true

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Z_add_is_or"
  Z_add_is_or : ∀ i, 0 ≤ i → ∀ x y, (∀ j, 0 ≤ j ∧ j ≤ i → (testbit x j && testbit y j) = false) →
    testbit (x+y) i = (testbit x i || testbit y i)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ziter_base"
  Ziter_base : ∀ (A : Type u) (n : Int) (f : A → A) (x : A), n ≤ 0 → Ziter n f x = x

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ziter_succ"
  Ziter_succ : ∀ (A : Type u) (n : Int) (f : A → A) (x : A), 0 ≤ n → Ziter (n+1) f x = f (Ziter n f
    x)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Znatlike_ind"
  Znatlike_ind : ∀ P : Int → Prop, (∀ n, n ≤ 0 → P n) → (∀ n, 0 ≤ n → P n → P (n+1)) → ∀ n, P n

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zzero_ext_spec"
  Zzero_ext_spec : ∀ n x i, 0 ≤ i → testbit (Zzero_ext n x) i = chooseSide (zlt i n) (testbit x i)
    false

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zsign_ext_spec"
  Zsign_ext_spec : ∀ n x i, 0 ≤ i → 0 < n → testbit (Zsign_ext n x) i = testbit x (chooseSide (zlt i
    n) i (n-1))

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zzero_ext_mod"
  Zzero_ext_mod : ∀ n x, 0 ≤ n → Zzero_ext n x = Int.fmod x (two_p n)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zzero_ext_range"
  Zzero_ext_range : ∀ n x, 0 ≤ n → 0 ≤ Zzero_ext n x ∧ Zzero_ext n x < two_p n

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|eqmod_Zzero_ext"
  eqmod_Zzero_ext : ∀ n x, 0 ≤ n → eqmod (two_p n) (Zzero_ext n x) x

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zsign_ext_zero_ext"
  Zsign_ext_zero_ext : ∀ n, 0 < n → ∀ x, Zsign_ext n x = Zzero_ext n x - (if testbit x (n-1) then
    two_p n else 0)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zsign_ext_range"
  Zsign_ext_range : ∀ n x, 0 < n → -two_p (n-1) ≤ Zsign_ext n x ∧ Zsign_ext n x < two_p (n-1)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|eqmod_Zsign_ext"
  eqmod_Zsign_ext : ∀ n x, 0 < n → eqmod (two_p n) (Zsign_ext n x) x

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Z_one_bits_powerserie"
  Z_one_bits_powerserie : ∀ n x, 0 ≤ x ∧ x < two_power_nat n → x = powerserie (Z_one_bits n x 0)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Z_one_bits_range"
  Z_one_bits_range : ∀ (n : Nat) (x i : Int), i ∈ Z_one_bits n x 0 → 0 ≤ i ∧ i < (n : Int)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Z_one_bits_zero"
  Z_one_bits_zero : ∀ n i, Z_one_bits n 0 i = []

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Z_one_bits_two_p"
  Z_one_bits_two_p : ∀ (n : Nat) (x i : Int), 0 ≤ x ∧ x < (n : Int) → Z_one_bits n (two_p x) i =
    [i+x]

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|P_is_power2_sound"
  P_is_power2_sound : ∀ p, P_is_power2 p = true → Int.ofNat p.val = two_p (Zlog2 (Int.ofNat p.val))

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Z_is_power2_sound"
  Z_is_power2_sound : ∀ x i, Z_is_power2 x = some i → x = two_p i ∧ i = Zlog2 x

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Z_is_power2_range"
  Z_is_power2_range : ∀ n x i, 0 ≤ n → 0 ≤ x ∧ x < two_p n → Z_is_power2 x = some i → 0 ≤ i ∧ i < n

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Z_is_power2_complete"
  Z_is_power2_complete : ∀ i, 0 ≤ i → Z_is_power2 (two_p i) = some i

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Z_is_power2m1_sound"
  Z_is_power2m1_sound : ∀ x i, Z_is_power2m1 x = some i → x = two_p i - 1

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Z_is_power2m1_complete"
  Z_is_power2m1_complete : ∀ i, 0 ≤ i → Z_is_power2m1 (two_p i - 1) = some i

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Z_is_power2m1_range"
  Z_is_power2m1_range : ∀ n x i, 0 ≤ n → 0 ≤ x ∧ x < two_p n → Z_is_power2m1 x = some i → 0 ≤ i ∧ i
    ≤ n

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zshiftl_mul_two_p"
  Zshiftl_mul_two_p : ∀ x n : Int, 0 ≤ n → x <<< n = x * two_p n

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zshiftr_div_two_p"
  Zshiftr_div_two_p : ∀ x n : Int, 0 ≤ n → x >>> n = x.fdiv (two_p n)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zquot_Zdiv"
  Zquot_Zdiv : ∀ x y : Int, y > 0 → x.tdiv y = chooseSide (zlt x 0) ((x+y-1).fdiv y) (x.fdiv y)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zdiv_shift"
  Zdiv_shift : ∀ x y : Int, y > 0 → (x + (y-1)).fdiv y = x.fdiv y + chooseSide (zeq (x.fmod y) 0) 0
    1

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zsize_pos"
  Zsize_pos : ∀ x, 0 ≤ Zsize x

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zsize_pos'"
  Zsize_pos' : ∀ x, 0 < x → 0 < Zsize x

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zsize_shiftin"
  Zsize_shiftin : ∀ b x, 0 < x → Zsize (Zshiftin b x) = Zsize x + 1

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ztestbit_size_1"
  Ztestbit_size_1 : ∀ x, 0 < x → testbit x (Zsize x - 1) = true

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Ztestbit_size_2"
  Ztestbit_size_2 : ∀ x, 0 ≤ x → ∀ i, i ≥ Zsize x → testbit x i = false

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zsize_interval_1"
  Zsize_interval_1 : ∀ x, 0 ≤ x → 0 ≤ x ∧ x < two_p (Zsize x)

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zsize_interval_2"
  Zsize_interval_2 : ∀ x n, 0 ≤ n → 0 ≤ x ∧ x < two_p n → n ≥ Zsize x

#source_check "src/rocq/Numeric/Zbits.v|Vellvm.Numeric.Zbits|Zsize_monotone"
  Zsize_monotone : ∀ x y, 0 ≤ x ∧ x ≤ y → Zsize x ≤ Zsize y
