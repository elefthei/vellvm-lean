import Vellvm.Numeric.Flocq.Round

namespace Vellvm.Numeric.Flocq

theorem round_grid_le {ex : Int → Int} (md : Mode) {x : ℝ} (m i : Int)
    (hi : cexp ex x ≤ i) (hx : x ≤ m * (2 : ℝ) ^ i) :
    round ex (round_mode md) x ≤ m * (2 : ℝ) ^ i := by
  let j := cexp ex x
  have hb : 0 < (2 : ℝ) ^ j := by positivity
  have E : (m : ℝ) * 2 ^ i = ((m * pow2 (i-j) : Int) : ℝ) * 2 ^ j := by
    rw [Int.cast_mul, pow2_cast (sub_nonneg.mpr hi), zpow_sub₀ (by norm_num)]; field_simp; rfl
  rw [E] at hx ⊢
  apply mul_le_mul_of_nonneg_right _ hb.le
  exact_mod_cast (mode_floor_ceil md (x / 2^j)).2.trans (Int.ceil_le.mpr ((div_le_iff₀ hb).mpr hx))

theorem round_grid_ge {ex : Int → Int} (md : Mode) {x : ℝ} (m i : Int)
    (hi : cexp ex x ≤ i) (hx : m * (2 : ℝ) ^ i ≤ x) :
    m * (2 : ℝ) ^ i ≤ round ex (round_mode md) x := by
  let j := cexp ex x
  have hb : 0 < (2 : ℝ) ^ j := by positivity
  have E : (m : ℝ) * 2 ^ i = ((m * pow2 (i-j) : Int) : ℝ) * 2 ^ j := by
    rw [Int.cast_mul, pow2_cast (sub_nonneg.mpr hi), zpow_sub₀ (by norm_num)]; field_simp; rfl
  rw [E] at hx ⊢
  apply mul_le_mul_of_nonneg_right _ hb.le
  exact_mod_cast (Int.le_floor.mpr ((le_div_iff₀ hb).mpr hx)).trans (mode_floor_ceil md (x / 2^j)).1

theorem bounded_cexp {p e : Int} (hp : 0 < p) (he : p < e) {x : ℝ} (h : |x| < 2^e) :
    cexp (fexp p e) x ≤ e - p := by
  by_cases hx : x = 0
  · subst x; simp [cexp,fexp,FLT_exp,emin]; omega
  have hm := (Int.lt_zpow_iff_log_lt (by decide : 1 < 2) (abs_pos.mpr hx)).mp (by simpa using h)
  unfold cexp fexp FLT_exp emin; omega

theorem round_ge_pow {p e : Int} (hp : 0 < p) (md : Mode) (x : ℝ) (i : Int)
    (hl : emin p e ≤ i) (h : (2 : ℝ)^i ≤ x) : 2^i ≤ round (fexp p e) (round_mode md) x := by
  let j := cexp (fexp p e) x
  by_cases hj : j ≤ i
  · simpa using round_grid_ge md 1 i hj (by simpa using h)
  have hx : 0 < x := lt_of_lt_of_le (by positivity) h
  have hh : j ≤ Int.log 2 x := by
    simp only [j,cexp,fexp,FLT_exp,abs_of_pos hx] at *; omega
  have hxj := (Int.zpow_le_iff_le_log (by decide : 1 < 2) hx).mpr hh
  have ha := round_grid_ge (ex := fexp p e) md 1 j le_rfl (by simpa using hxj)
  exact (zpow_right_mono₀ (by norm_num : (1:ℝ) ≤ 2) (le_of_lt (not_le.mp hj))).trans (by simpa using ha)

theorem round_le_neg_pow {p e : Int} (hp : 0 < p) (md : Mode) (x : ℝ) (i : Int)
    (hl : emin p e ≤ i) (h : x ≤ -(2 : ℝ)^i) : round (fexp p e) (round_mode md) x ≤ -2^i := by
  let j := cexp (fexp p e) x
  by_cases hj : j ≤ i
  · simpa using round_grid_le md (-1) i hj (by simpa using h)
  have hx : x < 0 := lt_of_le_of_lt h (neg_lt_zero.mpr (by positivity))
  have hh : j ≤ Int.log 2 (-x) := by simp only [j,cexp,fexp,FLT_exp,abs_of_neg hx] at *; omega
  have hxj := (Int.zpow_le_iff_le_log (by decide : 1 < 2) (neg_pos.mpr hx)).mpr hh
  have ha := round_grid_le (ex := fexp p e) md (-1) j le_rfl (by simpa using neg_le_neg hxj)
  exact (by simpa using ha : round (fexp p e) (round_mode md) x ≤ -2^j).trans
    (neg_le_neg (zpow_right_mono₀ (by norm_num : (1:ℝ) ≤ 2) (le_of_lt (not_le.mp hj))))

theorem bounded_mag {p e : Int} {m : Vellvm.Positive} {i : Int} (h : bounded p e m i = true) :
    emin p e ≤ i ∧ ((digits2_pos m).val : Int) ≤ p ∧ i ≤ e - p := by
  have := of_decide_eq_true h
  dsimp only [fexp,FLT_exp] at this; omega

theorem finite_lt {p e : Int} (f : binary_float p e) : |B2R f| < (2 : ℝ) ^ e := by
  cases f with
  | B754_finite s m i h =>
    obtain ⟨_,hd,hi⟩ := bounded_mag h
    have hm : 0 < (m.val : ℝ) * 2^i := mul_pos (Nat.cast_pos.mpr m.property) (by positivity)
    have hl := canonical_mag (K := ℝ) m i
    have hlt := (Int.lt_zpow_iff_log_lt (by decide : 1 < 2) hm).mpr (show Int.log 2 ((m.val : ℝ)*2^i) < e by omega)
    cases s <;> simpa [B2R,B2F,signed,abs_of_pos hm] using hlt
  | _ => simp [B2R,B2F]; positivity

theorem bounds_format {p e p' e' : Int} (hp : 0 < p') (hpw : p ≤ p') (hew : e ≤ e')
    (f : binary_float p e) : generic_format (fexp p' e') (B2R f) := by
  cases f with
  | B754_finite s m i h =>
    obtain ⟨hl,hd,_⟩ := bounded_mag h
    have hm : (m.val : Int) < pow2 p' := by
      have hu := Nat.lt_pow_succ_log_self (by decide : 1 < 2) m.val
      have hh : Nat.log 2 m.val + 1 ≤ p'.toNat := by dsimp [digits2_pos] at hd; omega
      have h' := hu.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hh)
      simp only [pow2,zpowNat,if_neg hp.not_gt]; exact_mod_cast h'
    have H := format_scaled hp (e := e') (m.val : Int) i (by simpa using hm) (by unfold emin at *; omega)
    cases s <;> first | simpa [B2R,B2F,signed] using H | simpa [B2R,B2F,signed] using format_neg H
  | _ => simp [B2R,B2F,generic_format,round,Ztrunc]

end Vellvm.Numeric.Flocq
