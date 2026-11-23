/-
Flocq binary floating-point arithmetic, https://flocq.gitlabpages.inria.fr/
Copyright (C) 2011–2018 Sylvie Boldo and Guillaume Melquiond.
This library is free software; you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation; either version 3 of the License, or (at your option) any later version.
This library is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.
-/
import Vellvm.Numeric.Flocq.Binary

namespace Vellvm.Numeric.Flocq

def join_bits (mw ew : Nat) (s : Bool) (m k : Int) : Int :=
  m + ((if s then 2 ^ ew else 0) + k) * 2 ^ mw

def split_bits (mw ew : Nat) (n : Int) : (Bool × Int) × Int :=
  ((decide (2 ^ ew * 2 ^ mw ≤ n), n % 2 ^ mw), (n / 2 ^ mw) % 2 ^ ew)

theorem split_join_bits (mw ew : Nat) (s : Bool) (m k : Int)
    (hm : 0 ≤ m ∧ m < 2^mw) (hk : 0 ≤ k ∧ k < 2^ew) :
    split_bits mw ew (join_bits mw ew s m k) = ((s, m), k) := by
  have hM : 0 < (2 : Int)^mw := by positivity
  unfold split_bits join_bits
  simp only [← Int.le_ediv_iff_mul_le hM, Int.add_mul_ediv_right _ _ hM.ne',
    Int.ediv_eq_zero_of_lt hm.1 hm.2, zero_add, Int.add_mul_emod_self_right,
    Int.emod_eq_of_lt hm.1 hm.2]
  cases s <;> simp [Int.add_emod, Int.emod_eq_of_lt hk.1 hk.2, hk.1, hk.2.not_ge]

private abbrev Fields (mw ew : Nat) := { t : (Bool × Int) × Int //
  (0 ≤ t.1.2 ∧ t.1.2 < 2^mw) ∧ (0 ≤ t.2 ∧ t.2 < 2^ew) }

private def readFields (mw ew : Nat) (n : Int) : Fields mw ew :=
  ⟨split_bits mw ew n, ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩,
    ⟨Int.emod_nonneg _ (by positivity), Int.emod_lt_of_pos _ (by positivity)⟩⟩

private def writeFields {mw ew : Nat} (f : Fields mw ew) : Int :=
  join_bits mw ew f.val.1.1 f.val.1.2 f.val.2

private theorem read_write {mw ew : Nat} (f : Fields mw ew) :
    readFields mw ew (writeFields f) = f := by
  apply Subtype.ext
  exact split_join_bits _ _ _ _ _ f.property.1 f.property.2

private theorem write_read (mw ew : Nat) (n : Int) (h : 0 ≤ n ∧ n < 2 * 2^ew * 2^mw) :
    writeFields (readFields mw ew n) = n := by
  let M := (2 : Int)^mw
  let E := (2 : Int)^ew
  have hM : 0 < M := by dsimp [M]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hlo : 0 ≤ n / M := Int.ediv_nonneg h.1 hM.le
  have hhi : n / M < 2 * E := (Int.ediv_lt_iff_lt_mul hM).mpr h.2
  change n % M + ((if decide (E * M ≤ n) then E else 0) + n / M % E) * M = n
  simp only [decide_eq_true_eq, ← Int.le_ediv_iff_mul_le hM]
  by_cases hs : E ≤ n / M
  · have hu : 0 ≤ n / M - E ∧ n / M - E < E := by omega
    have hr : (n / M) % E = n / M - E := by
      simpa only [sub_add_cancel] using
        (Int.add_emod_right (n / M - E) E).trans (Int.emod_eq_of_lt hu.1 hu.2)
    simp [hs, hr, Int.emod_add_ediv_mul]
  · simp [hs, Int.emod_eq_of_lt hlo (lt_of_not_ge hs), Int.emod_add_ediv_mul]

private theorem write_range {mw ew : Nat} (f : Fields mw ew) :
    0 ≤ writeFields f ∧ writeFields f < 2 * 2^ew * 2^mw := by
  rcases f with ⟨⟨⟨s,m⟩,k⟩,hm,hk⟩
  change 0 ≤ m ∧ m < 2^mw at hm
  change 0 ≤ k ∧ k < 2^ew at hk
  let a := (if s then (2 : Int)^ew else 0) + k
  change 0 ≤ m + a * 2^mw ∧ m + a * 2^mw < _
  have ha : 0 ≤ a ∧ a + 1 ≤ 2 * 2^ew := by cases s <;> dsimp [a] <;> omega
  have hM : 0 ≤ (2 : Int)^mw := by positivity
  have hu := mul_le_mul_of_nonneg_right ha.2 hM
  rw [add_mul, one_mul] at hu
  exact ⟨add_nonneg hm.1 (mul_nonneg ha.1 hM), by omega⟩

private abbrev prec (mw : Nat) : Int := (mw : Int) + 1

private theorem mant_lt_iff (m : Positive) (w : Nat) :
    (m.val : Int) < (2 : Int)^w ↔ Nat.log 2 m.val < w := by
  exact_mod_cast (Nat.log_lt_iff_lt_pow (by decide : 1 < 2) m.property.ne').symm

private theorem nan_iff {mw : Nat} {m : Positive} :
    nan_pl (prec mw) m = true ↔ (m.val : Int) < 2^mw := by
  rw [mant_lt_iff]; simp [nan_pl, digits2_pos, prec]

private theorem bounded_iff {mw : Nat} {e i : Int} {m : Positive} :
    bounded (prec mw) e m i = true ↔
      emin (prec mw) e ≤ i ∧ i ≤ e - prec mw ∧ (m.val : Int) < 2^mw * 2 ∧
      (i = emin (prec mw) e ∨ 2^mw ≤ (m.val : Int)) := by
  rw [← pow_succ, mant_lt_iff, ← not_lt (a := (m.val : Int)) (b := 2^mw), mant_lt_iff]
  simp only [bounded, decide_eq_true_eq, fexp, FLT_exp, digits2_pos, Nat.cast_add, Nat.cast_one,
    prec]
  omega

private def positiveOfInt (z : Int) (h : 0 < z) : Positive := ⟨z.toNat, by omega⟩

@[simp] private theorem positive_val (z : Int) (h : 0 < z) :
    ((positiveOfInt z h).val : Int) = z := Int.toNat_of_nonneg h.le

@[simp] private theorem positive_eta (p : Positive) (h : 0 < (p.val : Int)) :
    positiveOfInt p.val h = p := by apply Subtype.ext; simp [positiveOfInt]

private def encodeFields (mw ew : Nat) (e : Int) (he : 2 ≤ e) (hE : (2:Int)^ew = 2*e) :
    binary_float (prec mw) e → Fields mw ew
  | .B754_zero s => ⟨((s,0),0), ⟨le_rfl, by positivity⟩, ⟨le_rfl, by positivity⟩⟩
  | .B754_infinity s => ⟨((s,0),2^ew-1), ⟨le_rfl, by positivity⟩, by dsimp; omega⟩
  | .B754_nan s m h => ⟨((s,m.val),2^ew-1), ⟨by positivity, nan_iff.mp h⟩, by dsimp; omega⟩
  | .B754_finite s m i h =>
    if hn : 2^mw ≤ (m.val : Int) then
      ⟨((s,m.val-2^mw),i-emin (prec mw) e+1), by
        have H := bounded_iff.mp h; dsimp; omega, by
        have H := bounded_iff.mp h; dsimp [emin] at *; omega⟩
    else ⟨((s,m.val),0), ⟨by positivity, lt_of_not_ge hn⟩, ⟨le_rfl, by positivity⟩⟩

private def decodeFields (mw ew : Nat) (e : Int) (he : 2 ≤ e) (hE : (2:Int)^ew = 2*e) :
    Fields mw ew → binary_float (prec mw) e
  | ⟨((s,m),k), hm, hk⟩ =>
    if h0 : k = 0 then
      if hm0 : m = 0 then .B754_zero s else
        .B754_finite s (positiveOfInt m (by dsimp at hm; omega)) (emin (prec mw) e) (by
          apply bounded_iff.mpr; rw [positive_val]; dsimp [emin] at *; omega)
    else if hmax : k = 2^ew-1 then
      if hm0 : m = 0 then .B754_infinity s else
        .B754_nan s (positiveOfInt m (by dsimp at hm; omega)) (nan_iff.mpr (by simpa using hm.2))
    else
      .B754_finite s (positiveOfInt (m + 2^mw) (by have := hm.1; dsimp at this; positivity))
        (k + emin (prec mw) e - 1) (by
          apply bounded_iff.mpr; rw [positive_val]; dsimp [emin] at *; omega)

private theorem decode_encode (mw ew : Nat) (e : Int) (he : 2 ≤ e) (hE : (2:Int)^ew = 2*e)
    (x : binary_float (prec mw) e) : decodeFields mw ew e he hE (encodeFields mw ew e he hE x) = x := by
  have hmax : (2:Int)^ew - 1 ≠ 0 := by omega
  cases x with
  | B754_zero => rfl
  | B754_infinity => simp [encodeFields, decodeFields, hmax]
  | B754_nan s m h =>
    simp [encodeFields, decodeFields, hmax, m.property.ne']
  | B754_finite s m i h =>
    obtain ⟨hl, hu, hm, hc⟩ := bounded_iff.mp h
    by_cases hn : 2^mw ≤ (m.val : Int)
    · have hk : i - emin (prec mw) e + 1 ≠ 0 := by omega
      have hx : i - emin (prec mw) e + 1 ≠ 2^ew-1 := by unfold emin; omega
      simp [encodeFields, decodeFields, hn, hk, hx]; omega
    · have hi : i = emin (prec mw) e := hc.resolve_right hn
      simp [encodeFields, decodeFields, hn, hi, m.property.ne']

private theorem encode_decode (mw ew : Nat) (e : Int) (he : 2 ≤ e) (hE : (2:Int)^ew = 2*e)
    (f : Fields mw ew) : encodeFields mw ew e he hE (decodeFields mw ew e he hE f) = f := by
  rcases f with ⟨⟨⟨s,m⟩,k⟩,hm,hk⟩
  change 0 ≤ m ∧ m < 2^mw at hm
  apply Subtype.ext
  by_cases h0 : k = 0
  · subst k; by_cases hm0 : m = 0 <;> simp [decodeFields, encodeFields, hm0, hm.2.not_ge]
  · by_cases hx : k = 2^ew-1
    · have hn : (2:Int)^ew - 1 ≠ 0 := by omega
      by_cases hm0 : m = 0 <;> simp [decodeFields, encodeFields, hx, hm0, hn]
    · have hn : 2^mw ≤ m + 2^mw := by omega
      simp [decodeFields, encodeFields, h0, hx, hn]; omega

section Codec
variable (mw ew : Nat) (e : Int) (he : 2 ≤ e) (hE : (2:Int)^ew = 2*e)

private def encode (x : binary_float (prec mw) e) := writeFields (encodeFields mw ew e he hE x)
private def decode (n : Int) := decodeFields mw ew e he hE (readFields mw ew n)

private theorem decode_encode_bits (x : binary_float (prec mw) e) :
    decode mw ew e he hE (encode mw ew e he hE x) = x := by
  unfold decode encode; rw [read_write, decode_encode]

private theorem encode_decode_bits (n : Int) (h : 0 ≤ n ∧ n < 2 * 2^ew * 2^mw) :
    encode mw ew e he hE (decode mw ew e he hE n) = n := by
  unfold decode encode; rw [encode_decode, write_read _ _ _ h]
end Codec

def bits_of_b64 := encode 52 11 1024 (by decide) (by decide)
def b64_of_bits := decode 52 11 1024 (by decide) (by decide)
def bits_of_b32 := encode 23 8 128 (by decide) (by decide)
def b32_of_bits := decode 23 8 128 (by decide) (by decide)

theorem bits_of_b64_range (x : binary_float 53 1024) :
    0 ≤ bits_of_b64 x ∧ bits_of_b64 x < 2^64 := write_range (encodeFields _ _ _ _ _ x)

theorem bits_of_b32_range (x : binary_float 24 128) :
    0 ≤ bits_of_b32 x ∧ bits_of_b32 x < 2^32 := write_range (encodeFields _ _ _ _ _ x)

theorem b64_of_bits_of_b64 (x : binary_float 53 1024) : b64_of_bits (bits_of_b64 x) = x :=
  decode_encode_bits 52 11 1024 _ _ x

theorem b32_of_bits_of_b32 (x : binary_float 24 128) : b32_of_bits (bits_of_b32 x) = x :=
  decode_encode_bits 23 8 128 _ _ x

theorem bits_of_b64_of_bits (n : Int) (h : 0 ≤ n ∧ n < 2^64) : bits_of_b64 (b64_of_bits n) = n :=
  encode_decode_bits 52 11 1024 _ _ n h

theorem bits_of_b32_of_bits (n : Int) (h : 0 ≤ n ∧ n < 2^32) : bits_of_b32 (b32_of_bits n) = n :=
  encode_decode_bits 23 8 128 _ _ n h

theorem b64_of_bits_normal {n : Int} {s : Bool} {m k : Int}
    (h : split_bits 52 11 n = ((s,m),k)) (hk : 0 < k ∧ k < 2047) :
    ∃ (v : Positive) (hv : bounded 53 1024 v (k-1075) = true),
      (v.val : Int) = m + 2^52 ∧ b64_of_bits n = .B754_finite s v (k-1075) hv := by
  have F := (readFields 52 11 n).property
  dsimp only [readFields, Subtype.coe_mk] at F
  rw [h] at F
  have H : readFields 52 11 n = ⟨((s,m),k), F⟩ := Subtype.ext h
  have h0 : k ≠ 0 := by omega
  have hx : k ≠ (2:Int)^11-1 := by norm_num; omega
  have hi : k + emin (prec 52) 1024 - 1 = k - 1075 := by unfold emin prec; omega
  unfold b64_of_bits decode; rw [H, ← hi]; simp only [decodeFields, dif_neg h0, dif_neg hx]
  generalize_proofs
  exact ⟨_, by assumption, positive_val _ _, rfl⟩

end Vellvm.Numeric.Flocq
