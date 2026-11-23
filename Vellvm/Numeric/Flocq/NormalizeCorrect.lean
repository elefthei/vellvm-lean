import Vellvm.Numeric.Flocq.Round

namespace Vellvm.Numeric.Flocq

@[simp] theorem cast_B2Q {p e} (f : binary_float p e) : ((B2Q f : ℚ) : ℝ) = B2R f := by
  cases f with
  | B754_finite s m i _ => cases s <;> simp [B2Q, B2R, B2F, signed]
  | _ => simp [B2Q, B2R, B2F]

@[simp] theorem FF_overflow {p e} (hp : 0 < p) (he : p < e) (md : Mode) (s : Bool) :
    B2FF (overflow p e hp he md s) = binary_overflow p e md s := by
  unfold overflow binary_overflow
  split <;> simp only [B2FF]
  congr 1
  apply Subtype.ext
  have h : 1 < (2 : Nat) ^ p.toNat := one_lt_pow₀ (by decide) (by omega)
  have hc : (2 : Int) ^ p.toNat = ((2 ^ p.toNat : Nat) : Int) := by norm_cast
  change 2 ^ p.toNat - 1 = max 1 (pow2 p - 1).toNat
  simp only [pow2, zpowNat, if_neg hp.not_gt]
  rw [hc]; omega

theorem pack_correct {p e} (hp : 0 < p) (he : p < e) (md : Mode) (s : Bool)
    (m : Positive) (i : Int) (hi : emin p e ≤ i) (hm : m.val ≤ 2 ^ p.toNat) :
    let f := pack p e hp he md s m i hi
    if (m.val : ℚ) * (2 : ℚ) ^ i < (2 : ℚ) ^ e then
      B2Q f = signed s ((m.val : ℚ) * (2 : ℚ) ^ i) ∧ is_finite f = true ∧ Bsign f = s
    else B2FF f = binary_overflow p e md s := by
  have hmpos : (0 : ℚ) < m.val := Nat.cast_pos.mpr m.property
  have hmag := canonical_mag (K := ℚ) m i
  have hiff : (m.val : ℚ) * (2 : ℚ) ^ i < (2 : ℚ) ^ e ↔ (digits2_pos m).val + i ≤ e := by
    rw [show ((2 : ℚ) ^ e) = ((2 : Nat) : ℚ) ^ e by norm_num,
      Int.lt_zpow_iff_log_lt (by decide : 1 < 2) (mul_pos hmpos (by positivity))]; omega
  simp only [hiff]
  by_cases hd : p < ((digits2_pos m).val : Int)
  · have hle : (digits2_pos m).val ≤ p + 1 := by
      have := Nat.log_mono_right (b := 2) hm
      rw [Nat.log_pow (by decide)] at this
      simp [digits2_pos]; omega
    have hk : (((digits2_pos m).val : Int) - p).toNat = 1 := by omega
    have heq : m.val = 2 ^ p.toNat := by
      have hlog : Nat.log 2 m.val = p.toNat := by dsimp [digits2_pos] at hd hle; omega
      have h := Nat.pow_log_le_self 2 m.property.ne'
      rw [hlog] at h
      omega
    have hmEven : 2 ∣ m.val := by
      rw [heq, show p.toNat = (p.toNat - 1) + 1 by omega, pow_succ]; exact dvd_mul_left ..
    by_cases hj : i + (((digits2_pos m).val : Int) - p).toNat ≤ e - p
    · simp only [pack, dif_pos hd, dif_pos hj, if_pos (show ((digits2_pos m).val : Int) + i ≤ e by omega)]
      refine ⟨?_, rfl, rfl⟩
      change signed s (((m.val / 2 ^ _) : Nat) * (2 : ℚ) ^ (i + _)) = _
      congr 1
      simp only [hk, pow_one, Nat.cast_one, zpow_add₀ (by norm_num : (2:ℚ)≠0), zpow_one]
      have hdiv : ((m.val / 2 : Nat) : ℚ) * 2 = m.val := by exact_mod_cast Nat.div_mul_cancel hmEven
      linarith only [congrArg (· * (2 : ℚ) ^ i) hdiv]
    · simp only [pack, dif_pos hd, dif_neg hj, if_neg (show ¬ ((digits2_pos m).val : Int) + i ≤ e by omega)]
      exact FF_overflow ..
  · let k := (min (p - ((digits2_pos m).val : Int)) (i - emin p e)).toNat
    have hk : (k : Int) = min (p - ((digits2_pos m).val : Int)) (i - emin p e) := by dsimp [k]; omega
    have hmin : emin p e ≤ e - p := by unfold emin; omega
    by_cases hj : i - k ≤ e - p
    · have hb : ((digits2_pos m).val : Int) + i ≤ e := by omega
      dsimp only [k] at hj
      simp only [pack, dif_neg hd, dif_pos hj, if_pos hb]
      refine ⟨?_, rfl, rfl⟩
      change signed s ((((m.val * 2 ^ k : Nat) : ℚ)) * (2 : ℚ) ^ (i - k)) = _
      congr 1
      push_cast
      rw [zpow_sub₀ (by norm_num : (2:ℚ)≠0), zpow_natCast]; field_simp
    · have hb : ¬ ((digits2_pos m).val : Int) + i ≤ e := by omega
      dsimp only [k] at hj
      simp only [pack, dif_neg hd, dif_neg hj, if_neg hb]
      exact FF_overflow ..

@[simp] theorem ofRat_not_nan {p e} (hp : 0 < p) (he : p < e) (md : Mode) (q : ℚ) (s : Bool) :
    is_nan (ofRat p e hp he md q s) = false := by
  simp only [ofRat]; split
  · unfold pack; dsimp only; split <;> split <;> first | rfl | (unfold overflow; split_ifs <;> rfl)
  · rfl

end Vellvm.Numeric.Flocq
