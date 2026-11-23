import Vellvm.Numeric.Flocq.NormalizeCorrect

namespace Vellvm.Numeric.Flocq

private theorem cexp_cast (ex : Int → Int) (q : ℚ) : cexp ex (q : ℝ) = cexp ex q := by
  unfold cexp
  congr 2
  by_cases hq : q = 0
  · simp [hq]
  have hq' : 0 < |q| := abs_pos.mpr hq
  have hr : 0 < |(q : ℝ)| := by exact_mod_cast hq'
  have hlo := Int.zpow_log_le_self (by decide : 1 < 2) hq'
  have hhi := Int.lt_zpow_succ_log_self (by decide : 1 < 2) |q|
  have a : Int.log 2 |q| ≤ Int.log 2 |(q : ℝ)| :=
    (Int.zpow_le_iff_le_log (by decide : 1 < 2) hr).mp (by
      simpa using (Rat.cast_le (K := ℝ)).mpr hlo)
  have b : Int.log 2 |(q : ℝ)| < Int.log 2 |q| + 1 :=
    (Int.lt_zpow_iff_log_lt (by decide : 1 < 2) hr).mp (by
      simpa using (Rat.cast_lt (K := ℝ)).mpr hhi)
  omega

private theorem nearest_cast (c : Int → Bool) (q : ℚ) : Znearest c (q : ℝ) = Znearest c q := by
  have hl : (q : ℝ) - (⌊q⌋ : ℝ) < 1/2 ↔ q - ⌊q⌋ < 1/2 := by
    simpa only [Rat.cast_sub, Rat.cast_intCast, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ) (p := q - ⌊q⌋) (q := 1/2))
  have hu : 1/2 < (q : ℝ) - (⌊q⌋ : ℝ) ↔ 1/2 < q - ⌊q⌋ := by
    simpa only [Rat.cast_sub, Rat.cast_intCast, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ) (p := 1/2) (q := q - ⌊q⌋))
  simp only [Znearest, Rat.floor_cast, Rat.ceil_cast, hl, hu]

private theorem mode_cast (md : Mode) (q : ℚ) : round_mode md (q : ℝ) = round_mode md q := by
  have h : (q : ℝ) < 0 ↔ q < 0 := by norm_cast
  cases md <;> simp only [round_mode, nearest_cast, Rat.floor_cast, Rat.ceil_cast, Ztrunc, h]

theorem round_cast (ex : Int → Int) (md : Mode) (q : ℚ) :
    ((round ex (round_mode md) q : ℚ) : ℝ) = round ex (round_mode md) (q : ℝ) := by
  have hr := mode_cast md (q / 2 ^ cexp ex q)
  push_cast at hr
  simp only [round, cexp_cast, Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat, Rat.cast_intCast, hr]

/-- The integer rounder is at most one carry bit wider than the destination precision. -/
theorem scaled_le (p e : Int) (hp : 0 < p) (md : Mode) (q : ℚ) :
    (round_mode md (q / (2 : ℚ) ^ cexp (fexp p e) q)).natAbs ≤ 2 ^ p.toNat := by
  let i := cexp (fexp p e) q
  have he : Int.log 2 |q| + 1 ≤ p + i := by dsimp [i,cexp,fexp,FLT_exp]; omega
  have hb : 0 < (2 : ℚ) ^ i := by positivity
  have ha : |q| < (2 : ℚ) ^ (p + i) :=
    (Int.lt_zpow_succ_log_self (by decide : 1 < 2) |q|).trans_le (zpow_right_mono₀ (by norm_num) he)
  have hscaled : |q / (2 : ℚ) ^ i| ≤ ((pow2 p : Int) : ℚ) := by
    rw [abs_div, abs_of_pos hb, pow2_cast hp.le, div_le_iff₀ hb, ← zpow_add₀ (by norm_num)]
    exact ha.le
  have ⟨hl,hu⟩ := abs_le.mp hscaled
  have ⟨h₁,h₂⟩ := mode_floor_ceil md (q / (2 : ℚ) ^ i)
  have a : -pow2 p ≤ ⌊q / (2 : ℚ) ^ i⌋ := Int.le_floor.mpr (by simpa using hl)
  have b : ⌈q / (2 : ℚ) ^ i⌉ ≤ pow2 p := Int.ceil_le.mpr hu
  have H := abs_le.mpr ⟨a.trans h₁, h₂.trans b⟩
  rw [← Int.natCast_natAbs] at H
  simpa only [pow2,zpowNat,if_neg hp.not_gt,← Nat.cast_ofNat (R := Int) (n := 2), ← Nat.cast_pow, Nat.cast_le] using H

theorem ofRat_correct_Q (p e : Int) (hp : 0 < p) (he : p < e) (md : Mode) (q : ℚ) (sz : Bool) :
    let r := round (fexp p e) (round_mode md) q
    let s := if q = 0 then sz else decide (q < 0)
    let f := ofRat p e hp he md q sz
    if |r| < (2 : ℚ) ^ e then B2Q f = r ∧ is_finite f = true ∧ Bsign f = s
    else B2FF f = binary_overflow p e md s := by
  let i := cexp (fexp p e) q
  let z := round_mode md (q / (2 : ℚ) ^ i)
  let s := if q = 0 then sz else decide (q < 0)
  have hb : 0 < (2 : ℚ) ^ i := by positivity
  have hmag : |(z : ℚ) * (2 : ℚ) ^ i| = (z.natAbs : ℚ) * (2 : ℚ) ^ i := by simp [abs_mul,abs_of_pos hb]
  have hs : signed s ((z.natAbs : ℚ) * (2 : ℚ) ^ i) = (z : ℚ) * (2 : ℚ) ^ i := by
    have ⟨hl,hu⟩ := mode_floor_ceil md (q / (2 : ℚ) ^ i)
    rcases lt_trichotomy q 0 with hn | h0 | hp'
    · have h : z ≤ 0 := hu.trans (Int.ceil_nonpos.mpr (div_nonpos_of_nonpos_of_nonneg hn.le hb.le))
      have h' : (z : ℚ) ≤ 0 := by exact_mod_cast h
      simp [s,signed,hn.ne,hn,abs_of_nonpos h']
    · have hz : z = 0 := by
        simpa only [z,h0,zero_div,Int.cast_zero] using (mode_intCast (K := ℚ) md 0)
      cases sz <;> simp [s,signed,h0,hz]
    · have h : 0 ≤ z := (Int.floor_nonneg.mpr (div_nonneg hp'.le hb.le)).trans hl
      have h' : (0 : ℚ) ≤ z := by exact_mod_cast h
      simp [s,signed,hp'.ne',hp'.not_gt,abs_of_nonneg h']
  change (if |(z : ℚ) * (2 : ℚ) ^ i| < (2 : ℚ) ^ e then _ else _)
  simp only [hmag,ofRat]
  by_cases hz : 0 < z.natAbs
  · have hfull : 0 < (round_mode md (q / 2 ^ cexp (fexp p e) q)).natAbs := hz
    simp only [dif_pos hfull]
    have hpack := pack_correct hp he md s ⟨z.natAbs,hz⟩ i (le_max_right _ _) (scaled_le p e hp md q)
    simp only [hs] at hpack
    exact hpack
  · have h0 : z = 0 := by omega
    have hfull : ¬ 0 < (round_mode md (q / 2 ^ cexp (fexp p e) q)).natAbs := hz
    simp only [dif_neg hfull, h0, Int.natAbs_zero, Nat.cast_zero, zero_mul, if_pos (zpow_pos (by norm_num : (0:ℚ)<2) e)]
    change (0 : ℚ) = z * (2 : ℚ) ^ i ∧ true = true ∧ s = s
    simp [h0]

theorem ofRat_correct (p e : Int) (hp : 0 < p) (he : p < e) (md : Mode) (q : ℚ) (sz : Bool) :
    let r := round (fexp p e) (round_mode md) (q : ℝ)
    let s := if q = 0 then sz else decide (q < 0)
    let f := ofRat p e hp he md q sz
    if |r| < (2 : ℝ) ^ e then B2R f = r ∧ is_finite f = true ∧ Bsign f = s
    else B2FF f = binary_overflow p e md s := by
  have hr := ofRat_correct_Q p e hp he md q sz
  let r := round (fexp p e) (round_mode md) q
  have hcast : |(r : ℝ)| < (2 : ℝ) ^ e ↔ |r| < (2 : ℚ) ^ e := by
    simpa using (Rat.cast_lt (K := ℝ) (p := |r|) (q := (2:ℚ)^e))
  dsimp only at hr ⊢
  simp only [← round_cast]
  by_cases h : |r| < (2 : ℚ) ^ e
  · have hp' := hcast.mpr h
    rw [if_pos h] at hr
    rw [if_pos hp']
    exact ⟨by simpa only [cast_B2Q] using congrArg (fun x : ℚ ↦ (x : ℝ)) hr.1, hr.2⟩
  · have hn := mt hcast.mp h
    rw [if_neg h] at hr
    rw [if_neg hn]
    exact hr

end Vellvm.Numeric.Flocq
