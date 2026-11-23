import Vellvm.Numeric.Flocq.Bounds

namespace Vellvm.Numeric.Flocq

theorem format_scale {p e : Int} {x : ℝ} (hx : generic_format (fexp p e) x) {k : Int} (hk : 0 ≤ k) :
    generic_format (fexp p e) (x * 2^k) := by
  by_cases h0 : x = 0
  · subst x; simpa using hx
  let i := cexp (fexp p e) x
  let j := cexp (fexp p e) (x*2^k)
  have hl : j ≤ i+k := by
    simp only [j,i,cexp,fexp,FLT_exp,abs_mul,abs_of_pos (zpow_pos (by norm_num : (0:ℝ)<2) k),
      log_mul_two_zpow (abs_pos.mpr h0)]; omega
  let m := Ztrunc (x / (2 : ℝ)^i)
  have hm : x = (m : ℝ) * 2^i := hx
  have hg : x * 2^k / (2:ℝ)^j = ((m * pow2 (i+k-j) : Int) : ℝ) := by
    conv_lhs => rw [hm]
    rw [Int.cast_mul,pow2_cast (by omega), zpow_sub₀ (by norm_num),zpow_add₀ (by norm_num)]; ring
  change x * 2^k = (Ztrunc (x * 2^k / (2:ℝ)^j) : ℝ) * 2^j
  rw [hg,trunc_intCast,← hg,div_mul_cancel₀ _ (by positivity)]

theorem round_scale_large {p e : Int} (hp : 0 < p) (he : p < e) (rnd : ℝ → Int) {x : ℝ}
    (h : (2:ℝ)^p ≤ |x|) {k : Int} (hk : 0 ≤ k) :
    round (fexp p e) rnd (x * 2^k) = round (fexp p e) rnd x * 2^k := by
  have ha : 0 < |x| := lt_of_lt_of_le (by positivity) h
  have hl : p ≤ Int.log 2 |x| := (Int.zpow_le_iff_le_log (by decide : 1 < 2) ha).mp (by simpa using h)
  let i := cexp (fexp p e) x
  have hj : cexp (fexp p e) (x * 2^k) = i + k := by
    simp only [i,cexp,fexp,FLT_exp,emin,abs_mul,abs_of_pos (zpow_pos (by norm_num : (0:ℝ)<2) k),
      log_mul_two_zpow ha]; omega
  simp only [round,hj,zpow_add₀ (by norm_num : (2:ℝ)≠0)]
  change (rnd (x * 2^k / (2^i * 2^k)) : ℝ) * _ = _
  rw [mul_div_mul_right _ _ (zpow_ne_zero _ (by norm_num : (2:ℝ) ≠ 0))]; ring

end Vellvm.Numeric.Flocq
