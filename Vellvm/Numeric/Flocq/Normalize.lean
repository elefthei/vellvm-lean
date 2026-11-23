import Vellvm.Numeric.Flocq.Binary

namespace Vellvm.Numeric.Flocq

theorem pow2_pos {i : Int} (hi : 0 ≤ i) : 0 < pow2 i := by
  simp only [pow2, zpowNat, if_neg (not_lt.mpr hi)]
  positivity

theorem pow2_add {i j : Int} (hi : 0 ≤ i) (hj : 0 ≤ j) :
    pow2 (i + j) = pow2 i * pow2 j := by
  simp [pow2, zpowNat, not_lt.mpr hi, not_lt.mpr hj, not_lt.mpr (add_nonneg hi hj),
    Int.toNat_add hi hj, pow_add]

theorem pow2_mono {i j : Int} (hi : 0 ≤ i) (h : i ≤ j) : pow2 i ≤ pow2 j := by
  simp only [pow2, zpowNat, if_neg (not_lt.mpr hi), if_neg (not_lt.mpr (hi.trans h))]
  gcongr <;> omega

theorem pow2_cast {K : Type*} [Field K] [CharZero K] {i : Int} (h : 0 ≤ i) :
    (pow2 i : K) = (2 : K) ^ i := by
  lift i to Nat using h
  simp [pow2, zpowNat]

private theorem log_mul_pow (m n : Nat) (hm : 0 < m) :
    Nat.log 2 (m * 2 ^ n) = Nat.log 2 m + n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, Nat.log_mul_base (by decide) (by positivity), ih]; omega

def maximumMantissa (p : Int) (hp : 0 < p) : Positive :=
  ⟨2 ^ p.toNat - 1, by
    have : 1 < (2 : Nat) ^ p.toNat := one_lt_pow₀ (by decide) (by omega)
    omega⟩

theorem maximum_digits (p : Int) (hp : 0 < p) :
    ((digits2_pos (maximumMantissa p hp)).val : Int) = p := by
  obtain ⟨n, hn⟩ : ∃ n : Nat, p = n + 1 := ⟨(p - 1).toNat, by omega⟩
  subst p
  have h : 0 < (2 : Nat) ^ n := by positivity
  have hlog : Nat.log 2 (2 ^ (n + 1) - 1) = n :=
    Nat.log_eq_of_pow_le_of_lt_pow (by rw [pow_succ]; omega) (by rw [pow_succ]; omega)
  simpa [digits2_pos, maximumMantissa, hlog] using congrArg (fun k : Nat ↦ (k : Int) + 1) hlog

def overflow (p e : Int) (hp : 0 < p) (he : p < e) (mode : Mode) (s : Bool) : binary_float p e :=
  if overflow_to_inf mode s then .B754_infinity s else
    .B754_finite s (maximumMantissa p hp) (e - p) (by
      simp [bounded, maximum_digits, hp, fexp, FLT_exp, emin]; omega)

/-- Normalize a positive integer significance already rounded at exponent `i`. A carry can
    increase its digit length; left shifts stop at `emin` to preserve gradual underflow. -/
def pack (p e : Int) (hp : 0 < p) (he : p < e) (md : Mode) (s : Bool)
    (m : Positive) (i : Int) (hi : emin p e ≤ i) : binary_float p e :=
  let d : Int := (digits2_pos m).val
  if hd : p < d then
    let k := (d - p).toNat
    let j := i + k
    if hj : j ≤ e - p then
      have hk : k ≤ Nat.log 2 m.val := by dsimp [k,d,digits2_pos] at *; omega
      have hn : 0 < m.val / 2 ^ k := by
        apply Nat.div_pos _ (by positivity)
        exact (Nat.pow_le_pow_right (by decide : 0 < 2) hk).trans (Nat.pow_log_le_self 2 m.property.ne')
      .B754_finite s ⟨m.val / 2 ^ k, hn⟩ j (by
        simp only [bounded, decide_eq_true_eq, digits2_pos, Nat.log_div_base_pow, fexp, FLT_exp]
        dsimp [j,k,d,digits2_pos] at *; omega)
    else overflow p e hp he md s
  else
    let k := (min (p - d) (i - emin p e)).toNat
    let j := i - k
    if hj : j ≤ e - p then
      .B754_finite s ⟨m.val * 2 ^ k, Nat.mul_pos m.property (by positivity)⟩ j (by
        simp only [bounded, decide_eq_true_eq, digits2_pos, log_mul_pow _ _ m.property, fexp, FLT_exp]
        dsimp [j,k,d,digits2_pos] at *; omega)
    else overflow p e hp he md s

/-- Correctly signed zero is supplied by the caller when its exact input is zero. -/
def ofRat (p e : Int) (hp : 0 < p) (he : p < e) (md : Mode) (x : ℚ) (zeroSign : Bool) :
    binary_float p e :=
  let s := if x = 0 then zeroSign else decide (x < 0)
  let i := cexp (fexp p e) x
  let z := round_mode md (x / (2 : ℚ) ^ i)
  if hz : 0 < z.natAbs then
    pack p e hp he md s ⟨z.natAbs, hz⟩ i (le_max_right _ _)
  else .B754_zero s

def binary_normalize (p e : Int) (hp : 0 < p) (he : p < e) (md : Mode) (m i : Int)
    (zeroSign : Bool) := ofRat p e hp he md ((m : ℚ) * (2 : ℚ) ^ i) zeroSign

def roundQuotient (p e : Int) (hp : 0 < p) (he : p < e) (md : Mode) (s : Bool)
    (m : Positive) (i : Int) (n : Positive) (j : Int) :=
  ofRat p e hp he md (signed s ((m.val : ℚ) / n.val * (2 : ℚ) ^ (i - j))) s

end Vellvm.Numeric.Flocq
