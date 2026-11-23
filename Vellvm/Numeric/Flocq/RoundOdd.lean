/-
Flocq binary floating-point arithmetic, https://flocq.gitlabpages.inria.fr/
Copyright (C) 2013–2018 Sylvie Boldo and Guillaume Melquiond.
This library is free software; you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation; either version 3 of the License, or (at your option) any later version.
This library is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.
-/
import Vellvm.Numeric.Flocq.Round

namespace Vellvm.Numeric.Flocq

private def SameSide (x y t : ℝ) : Prop := (x < t ↔ y < t) ∧ (t < x ↔ t < y)

/-- Odd rounding never moves a value onto, or across, an even integer. -/
private theorem odd_side (x : ℝ) (n : Int) : SameSide x (Zrnd_odd x) ((2 * n : Int) : ℝ) := by
  by_cases hx : (⌊x⌋ : ℝ) = x
  · have he : (Zrnd_odd x : ℝ) = x := by simp only [Zrnd_odd, hx, true_or, ite_true]
    simp [SameSide, he]
  have hf := (Int.floor_le x).lt_of_ne hx
  have hc : ⌈x⌉ = ⌊x⌋ + 1 := Int.ceil_eq_iff.mpr (by
    push_cast
    exact ⟨by linarith, (Int.lt_floor_add_one x).le⟩)
  have hb : ⌊x⌋ ≤ Zrnd_odd x ∧ Zrnd_odd x ≤ ⌈x⌉ := by
    unfold Zrnd_odd; split <;> omega
  have hodd : Zrnd_odd x % 2 = 1 := by
    simp only [Zrnd_odd, hx, false_or, hc]
    split <;> omega
  have hn : Zrnd_odd x ≠ 2 * n := fun he ↦ by simp [he] at hodd
  rcases lt_trichotomy x ((2 * n : Int) : ℝ) with h | h | h
  · have hle := Int.ceil_le.mpr h.le
    have hy : (Zrnd_odd x : ℝ) < ((2 * n : Int) : ℝ) := by
      exact_mod_cast (by omega : Zrnd_odd x < 2 * n)
    exact ⟨iff_of_true h hy, iff_of_false h.not_gt hy.not_gt⟩
  · rw [h, odd_intCast]; simp [SameSide]
  · have hle := Int.le_floor.mpr h.le
    have hy : ((2 * n : Int) : ℝ) < Zrnd_odd x := by
      exact_mod_cast (by omega : 2 * n < Zrnd_odd x)
    exact ⟨iff_of_false h.not_gt hy.not_gt, iff_of_true h hy⟩

private theorem odd_grid {ex : Int → Int} (x : ℝ) {i : Int} (hi : cexp ex x < i) (n : Int) :
    SameSide x (round ex Zrnd_odd x) (n * (2 : ℝ)^i) := by
  let j := cexp ex x
  have h : 0 ≤ i - j - 1 := by dsimp [j]; omega
  have hp : (2 : ℝ)^i = (2 : ℝ)^(i-j-1) * 2 * 2^j := by
    conv_lhs => rw [show i = (i-j-1+1)+j by omega, zpow_add₀ (by norm_num),
      zpow_add₀ (by norm_num), zpow_one]
  have ht : (n : ℝ) * 2^i = ((2 * (n * pow2 (i-j-1)) : Int) : ℝ) * 2^j := by
    rw [hp, Int.cast_mul, Int.cast_mul, pow2_cast h]; push_cast; ring
  have hs : 0 < (2 : ℝ)^j := by positivity
  have H := odd_side (x / 2^j) (n * pow2 (i-j-1))
  change SameSide x ((Zrnd_odd (x / 2^j) : ℝ) * 2^j) _
  rw [ht]
  simpa only [SameSide, div_lt_iff₀ hs, lt_div_iff₀ hs, mul_lt_mul_iff_left₀ hs] using H

private theorem abs_grid {ex : Int → Int} (x : ℝ) {i : Int} (hi : cexp ex x < i) :
    |x| < 2^i ↔ |round ex Zrnd_odd x| < 2^i := by
  have L := (odd_grid x hi (-1)).2
  have U := (odd_grid x hi 1).1
  simp only [Int.cast_neg, Int.cast_one, neg_one_mul, one_mul] at L U
  simpa only [abs_lt] using and_congr L U

private theorem nearest_side (x y : ℝ) (c : Int → Bool)
    (h : ∀ n : Int, SameSide x y (n / 2)) : Znearest c y = Znearest c x := by
  have I (k : Int) : SameSide x y k := by simpa using h (2*k)
  have hfloor : ⌊y⌋ = ⌊x⌋ := Int.floor_eq_iff.mpr ⟨
    le_of_not_gt (fun hy ↦ (Int.floor_le x).not_gt ((I ⌊x⌋).1.mpr hy)),
    by simpa using (I (⌊x⌋+1)).1.mp (by simp)⟩
  have hceil : ⌈y⌉ = ⌈x⌉ := Int.ceil_eq_iff.mpr ⟨
    by simpa using (I (⌈x⌉-1)).2.mp (by push_cast; linarith [Int.ceil_lt_add_one x]),
    le_of_not_gt (fun hy ↦ (Int.le_ceil x).not_gt ((I ⌈x⌉).2.mpr hy))⟩
  have T : SameSide x y (⌊x⌋ + 1 / 2) := by
    convert h (2 * ⌊x⌋ + 1) using 1; push_cast; ring
  have L : y - ⌊x⌋ < 1/2 ↔ x - ⌊x⌋ < 1/2 := by
    simpa only [sub_lt_iff_lt_add, add_comm (1/2 : ℝ)] using T.1.symm
  have U : 1/2 < y - ⌊x⌋ ↔ 1/2 < x - ⌊x⌋ := by
    simpa only [lt_sub_iff_add_lt, add_comm (1/2 : ℝ)] using T.2.symm
  simp only [Znearest, hfloor, hceil, L, U]

/-- With two extra significand bits and two extra subnormal bits, odd rounding
preserves every nearest-rounding decision, including the caller's choice at ties. -/
theorem odd_flt (p e : Int) (_hp : 0 < p) (p' emin' : Int) (x : ℝ) (c : Int → Bool)
    (hp : 1 < p) (_hp' : 1 < p') (hprec : p + 2 ≤ p') (hmin : emin' ≤ emin p e - 2) :
    round (fexp p e) (Znearest c) (round (FLT_exp emin' p') Zrnd_odd x) =
      round (fexp p e) (Znearest c) x := by
  by_cases hx : x = 0
  · subst x; simp [round, Zrnd_odd]
  let y := round (FLT_exp emin' p') Zrnd_odd x
  let j := cexp (fexp p e) x
  let a := cexp (FLT_exp emin' p') x
  have hgap : a ≤ j - 2 := by dsimp [a,j,cexp,fexp,FLT_exp]; omega
  have hs := odd_grid (ex := FLT_exp emin' p') x (i := j) (by change a < j; omega) 0
  have hs0 : SameSide x y 0 := by simpa [y] using hs
  have hy : y ≠ 0 := by
    rcases lt_or_gt_of_ne hx with h | h
    · exact ((hs0.1.mp h).ne)
    · exact ((hs0.2.mp h).ne')
  have hlog (i : Int) (hi : a < i) : Int.log 2 |x| < i ↔ Int.log 2 |y| < i := by
    rw [← Int.lt_zpow_iff_log_lt (by decide : 1 < 2) (abs_pos.mpr hx),
      ← Int.lt_zpow_iff_log_lt (by decide : 1 < 2) (abs_pos.mpr hy)]
    exact abs_grid x hi
  have hu : Int.log 2 |y| < j+p := (hlog _ (by omega)).mp (by dsimp [j,cexp,fexp,FLT_exp]; omega)
  have he : cexp (fexp p e) y = j := by
    by_cases h : j ≤ emin p e
    · dsimp [cexp,fexp,FLT_exp]; dsimp [j,cexp,fexp,FLT_exp] at *; omega
    · have hl : ¬ Int.log 2 |y| < j+p-1 := fun hl ↦ by
        have hh := (hlog _ (by omega)).mpr hl
        dsimp [j,cexp,fexp,FLT_exp] at hh h; omega
      dsimp [cexp,fexp,FLT_exp]; omega
  have hb : 0 < (2 : ℝ)^j := by positivity
  have H (n : Int) : SameSide (x / 2^j) (y / 2^j) (n / 2) := by
    have hh := odd_grid (ex := FLT_exp emin' p') x (i := j-1) (by change a < j-1; omega) n
    have ht : (n : ℝ) / 2 * 2^j = n * 2^(j-1) := by rw [zpow_sub₀ (by norm_num), zpow_one]; ring
    simpa only [SameSide, div_lt_iff₀ hb, lt_div_iff₀ hb, ht] using hh
  change (Znearest c (y / (2:ℝ)^(cexp (fexp p e) y)) : ℝ) * 2^(cexp (fexp p e) y) = _
  rw [he, nearest_side _ _ c H]
  rfl

/-- At sufficiently large magnitudes a fixed first-stage exponent has two guard bits. -/
theorem odd_fix (p e : Int) (hp : 0 < p) (he : p < e) (x : ℝ) (k : Int) (c : Int → Bool)
    (hp₁ : 1 < p) (hk : 0 ≤ k) (hx : (2 : ℝ)^(p+k+1) ≤ |x|) :
    round (fexp p e) (Znearest c) (round (fun _ ↦ k) Zrnd_odd x) =
      round (fexp p e) (Znearest c) x := by
  let q := Int.log 2 |x| + 1 - k
  have hpos : 0 < |x| := lt_of_lt_of_le (by positivity) hx
  have hm := (Int.zpow_le_iff_le_log (by decide : 1 < 2) hpos).mp hx
  have hq : p + 2 ≤ q := by dsimp [q]; omega
  have hj : cexp (FLT_exp (emin p e - 2) q) x = k := by
    dsimp [cexp,FLT_exp,emin,q]; omega
  have E : round (fun _ ↦ k) Zrnd_odd x = round (FLT_exp (emin p e-2) q) Zrnd_odd x := by
    simp only [round,hj]; rfl
  rw [E]
  exact odd_flt p e hp q _ x c hp₁ (by omega) hq le_rfl

end Vellvm.Numeric.Flocq
