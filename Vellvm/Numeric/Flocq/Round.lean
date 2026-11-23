import Vellvm.Numeric.Flocq.Normalize

namespace Vellvm.Numeric.Flocq

section Field
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

@[simp] theorem trunc_intCast (n : Int) : Ztrunc (n : K) = n := by simp [Ztrunc]
@[simp] theorem nearest_intCast (c : Int → Bool) (n : Int) : Znearest c (n : K) = n := by
  simp [Znearest]
@[simp] theorem odd_intCast (n : Int) : Zrnd_odd (n : K) = n := by simp [Zrnd_odd]
@[simp] theorem mode_intCast (m : Mode) (n : Int) : round_mode m (n : K) = n := by
  cases m <;> simp [round_mode]

theorem mode_floor_ceil (m : Mode) (x : K) :
    ⌊x⌋ ≤ round_mode m x ∧ round_mode m x ≤ ⌈x⌉ := by
  have := Int.floor_le_ceil x
  cases m <;> simp only [round_mode, Ztrunc, Znearest] <;> (try split_ifs) <;> omega

theorem log_mul_two_zpow {x : K} (hx : 0 < x) (i : Int) :
    Int.log 2 (x * (2 : K) ^ i) = Int.log 2 x + i := by
  have hy : 0 < x * (2 : K) ^ i := by positivity
  have hb : 1 < (2 : Nat) := by decide
  have hl := Int.zpow_log_le_self hb hx
  have hu := Int.lt_zpow_succ_log_self hb x
  apply le_antisymm
  · have : Int.log 2 (x * (2 : K) ^ i) < Int.log 2 x + i + 1 := by
      apply (Int.lt_zpow_iff_log_lt hb hy).mp
      rw [show Int.log 2 x + i + 1 = (Int.log 2 x + 1) + i by omega, zpow_add₀ (by norm_num)]
      exact mul_lt_mul_of_pos_right hu (by positivity)
    omega
  · apply (Int.zpow_le_iff_le_log hb hy).mp
    rw [zpow_add₀ (by norm_num)]
    exact mul_le_mul_of_nonneg_right hl (by positivity)

@[simp] theorem cexp_neg (ex : Int → Int) (x : K) : cexp ex (-x) = cexp ex x := by simp [cexp]

theorem canonical_mag (m : Positive) (i : Int) :
    Int.log 2 ((m.val : K) * (2 : K) ^ i) + 1 = (digits2_pos m).val + i := by
  rw [log_mul_two_zpow (Nat.cast_pos.mpr m.property), Int.log_natCast]
  simp [digits2_pos]; omega

theorem canonical_exp {p e : Int} {m : Positive} {i : Int} (h : bounded p e m i = true) (s : Bool) :
    cexp (fexp p e) (signed s ((m.val : K) * (2 : K) ^ i)) = i := by
  have hm := (of_decide_eq_true h).1
  have hpos : 0 < (m.val : K) * (2 : K) ^ i := mul_pos (Nat.cast_pos.mpr m.property) (by positivity)
  cases s <;> simp [cexp, signed, abs_of_pos hpos, canonical_mag, hm]

theorem format_scaled {p e : Int} (hp : 0 < p) (m i : Int) (hm : |m| < pow2 p)
    (hi : emin p e ≤ i) : generic_format (fexp p e) ((m : ℝ) * (2 : ℝ) ^ i) := by
  by_cases h0 : m = 0
  · subst m; simp [generic_format, round, Ztrunc]
  have hpos : 0 < |(m : ℝ)| := abs_pos.mpr (by exact_mod_cast h0)
  have hm' : |(m : ℝ)| < (2 : ℝ) ^ p := by rw [← pow2_cast hp.le]; exact_mod_cast hm
  have hd : Int.log 2 |(m : ℝ)| < p := (Int.lt_zpow_iff_log_lt (by decide : 1 < 2) hpos).mp (by simpa using hm')
  let j := cexp (fexp p e) ((m : ℝ) * (2 : ℝ) ^ i)
  have hj : j ≤ i := by
    simp only [j, cexp, abs_mul, abs_of_pos (zpow_pos (by norm_num : (0:ℝ)<2) i),
      log_mul_two_zpow hpos, fexp, FLT_exp]; omega
  have hscale : (m : ℝ) * (2 : ℝ) ^ i / (2 : ℝ) ^ j = ((m * pow2 (i - j) : Int) : ℝ) := by
    rw [Int.cast_mul, pow2_cast (by omega), zpow_sub₀ (by norm_num)]; ring
  change (m : ℝ) * (2 : ℝ) ^ i = (Ztrunc ((m : ℝ) * (2 : ℝ) ^ i / (2 : ℝ) ^ j) : ℝ) * _
  rw [hscale, trunc_intCast, ← hscale, div_mul_cancel₀ _ (by positivity)]

theorem trunc_neg (x : K) : Ztrunc (-x) = -Ztrunc x := by
  rcases lt_trichotomy x 0 with h | rfl | h
  · simp [Ztrunc, h, h.not_gt, Int.floor_neg]
  · simp [Ztrunc]
  · simp [Ztrunc, h, h.not_gt, Int.ceil_neg]

theorem format_neg {ex : Int → Int} {x : ℝ} (hx : generic_format ex x) :
    generic_format ex (-x) := by
  unfold generic_format round at *
  simp only [cexp_neg, neg_div, trunc_neg, Int.cast_neg, neg_mul]
  exact congrArg Neg.neg hx

theorem format_round {ex : Int → Int} {x : ℝ} (hx : generic_format ex x) (md : Mode) :
    round ex (round_mode md) x = x := by
  let j := cexp ex x
  have h : x / (2 : ℝ) ^ j = (Ztrunc (x / (2 : ℝ) ^ j) : ℝ) :=
    (div_eq_iff (by positivity)).mpr hx
  change (round_mode md (x / (2 : ℝ) ^ j) : ℝ) * (2 : ℝ) ^ j = x
  conv_lhs => arg 1; arg 1; arg 2; rw [h]
  rw [mode_intCast]; exact hx.symm

end Field

end Vellvm.Numeric.Flocq
