/-
This file is part of the Flocq formalization of floating-point arithmetic:
https://flocq.gitlabpages.inria.fr/
Copyright (C) 2010–2018 Sylvie Boldo and Guillaume Melquiond.
This library is free software; you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation; either version 3 of the License, or (at your option) any later version.
This library is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE. See the COPYING file for more details.
-/
import Vellvm.Numeric.Flocq.Round

namespace Vellvm.Numeric.Flocq

/-- Sterbenz's lemma: subtracting nearby ordered floats is exact, even for subnormal results. -/
theorem sterbenz {p e : Int} (_hp : 0 < p) {x y : ℝ}
    (hx : generic_format (fexp p e) x) (hy : generic_format (fexp p e) y)
    (hy0 : 0 ≤ y) (hyx : y ≤ x) (hx2 : x ≤ 2 * y) : generic_format (fexp p e) (x - y) := by
  rcases hyx.eq_or_lt with rfl | hyx
  · simp [generic_format, round, Ztrunc]
  have hd : 0 < x - y := sub_pos.mpr hyx
  let j := cexp (fexp p e) (x - y)
  -- Both operands are integer multiples of the spacing at the (smaller) difference.
  have onGrid (z : ℝ) (hz : generic_format (fexp p e) z) (hle : x - y ≤ z) :
      ∃ n : Int, z / 2 ^ j = n := by
    let i := cexp (fexp p e) z
    have hlog := Int.log_mono_right (b := 2) hd hle
    have hji : j ≤ i := by
      simp only [j, i, cexp, abs_of_pos hd, abs_of_pos (hd.trans_le hle), fexp, FLT_exp]
      omega
    let m := Ztrunc (z / (2 : ℝ) ^ i)
    have hzm : z = (m : ℝ) * 2 ^ i := hz
    refine ⟨m * pow2 (i - j), ?_⟩
    rw [hzm, Int.cast_mul, pow2_cast (sub_nonneg.mpr hji), zpow_sub₀ (by norm_num)]
    ring
  obtain ⟨a, ha⟩ := onGrid x hx (sub_le_self x hy0)
  obtain ⟨b, hb⟩ := onGrid y hy (by linarith)
  have hab : (x - y) / 2 ^ j = ((a - b : Int) : ℝ) := by rw [sub_div, ha, hb, Int.cast_sub]
  change x - y = (Ztrunc ((x - y) / (2 : ℝ) ^ j) : ℝ) * 2 ^ j
  rw [hab, trunc_intCast, ← hab, div_mul_cancel₀ _ (by positivity)]

end Vellvm.Numeric.Flocq
