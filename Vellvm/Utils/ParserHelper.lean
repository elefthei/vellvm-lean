import Vellvm.Numeric.Flocq.Normalize
import Vellvm.Syntax.Number

namespace Vellvm.Utils.ParserHelper
open Vellvm.Numeric.Flocq

def N_of_uint := Decimal.uint.toNat
def N_of_hex_uint := Hexadecimal.uint.toNat

/-- Unbounded signed mantissa and exponent; no requirement of canonical representation. -/
@[ext] structure bfloat where
  BFloat ::
  Fnum : Int
  Fexp : Int
  deriving DecidableEq, Repr

export bfloat (BFloat Fnum Fexp)

def inc_e (f : bfloat) (de : Positive) : Option bfloat :=
  let scale := (2 : Int) ^ de.val
  if f.Fnum % scale = 0 then some ⟨f.Fnum / scale, f.Fexp + de.val⟩ else none

def dec_e (f : bfloat) (de : Positive) : bfloat :=
  ⟨f.Fnum * 2 ^ de.val, f.Fexp - de.val⟩

def shift_e (f : bfloat) (de : Int) : Option bfloat :=
  if h : 0 < de then inc_e f ⟨de.toNat, by omega⟩
  else if h : de < 0 then some (dec_e f ⟨(-de).toNat, by omega⟩)
  else some f

def set_e (f : bfloat) (e : Int) := shift_e f (e - f.Fexp)
def Zdigits (m : Int) : Int := (m.natAbs.log2 : Int) + 1
def inc_digits_m := dec_e
def dec_digits_m := inc_e
def shift_digits_m (f : bfloat) (ddm : Int) := shift_e f (-ddm)
def set_digits_m (f : bfloat) (dm : Int) := shift_digits_m f (dm - Zdigits f.Fnum)

/-- Both positive digit constructors drop one low bit; `xH` stops. -/
def log_inf (p : Positive) : Int :=
  if h : 2 ≤ p.val then 1 + log_inf ⟨p.val / 2, by omega⟩ else 0
termination_by p.val
decreasing_by exact Nat.div_lt_self p.property (by decide)

theorem Zlog2_log_inf (p : Positive) : (p.val.log2 : Int) = log_inf p := by
  rw [log_inf, Nat.log2_def]
  split <;> rename_i h
  · have ih : ((p.val / 2).log2 : Int) = log_inf ⟨p.val / 2, by omega⟩ :=
      Zlog2_log_inf ⟨p.val / 2, by omega⟩
    omega
  · rfl
termination_by p.val
decreasing_by exact Nat.div_lt_self p.property (by decide)

def normalize_float (p e : Int) (f : bfloat) : Option bfloat := do
  let lo := 3 - e - p
  let f₁ ← set_e f lo
  if Zdigits f₁.Fnum ≤ p then return f₁
  let f₂ ← set_digits_m f p
  if lo ≤ f₂.Fexp ∧ f₂.Fexp ≤ e - p then return f₂
  none

def can_convert_exactly (p e : Int) (m : Positive) (i : Int) : Bool :=
  (normalize_float p e (BFloat m.val i)).isSome

def can_convert_float_to_float32 : binary_float 53 1024 → Bool
  | .B754_finite _ m i _ => can_convert_exactly 24 128 m i
  | _ => true

def can_convert_float_to_float64 : binary_float 53 1024 → Bool
  | .B754_finite _ m i _ => can_convert_exactly 53 1024 m i
  | _ => true

theorem digits2_pos_digits (m : Positive) : ((digits2_pos m).val : Int) = (m.val.log2 : Int) + 1 := by
  simp [digits2_pos, Nat.log2_eq_log_two]

theorem bounded_closed_form (p e : Int) (_hp : 0 < p) (he : p < e) (m : Positive) (i : Int) :
    bounded p e m i = true ↔
      ((m.val.log2 : Int) + 1 < p ∧ i = 3 - e - p) ∨
      ((m.val.log2 : Int) + 1 = p ∧ 3 - e - p ≤ i ∧ i ≤ e - p) := by
  simp only [bounded, decide_eq_true_eq, fexp, FLT_exp, emin, digits2_pos_digits]
  omega

def valid_float (p e : Int) (f : bfloat) : Bool :=
  if h : 0 < f.Fnum.natAbs then bounded p e ⟨f.Fnum.natAbs, h⟩ f.Fexp else true

def float_eq (f g : bfloat) : Prop :=
  (g.Fexp ≤ f.Fexp ∧ g.Fnum = f.Fnum * pow2 (f.Fexp - g.Fexp)) ∨
  (f.Fexp ≤ g.Fexp ∧ f.Fnum = g.Fnum * pow2 (g.Fexp - f.Fexp))

theorem float_eq_refl (f : bfloat) : float_eq f f := Or.inl (by simp [pow2, zpowNat])
theorem float_eq_sym {f g : bfloat} (h : float_eq f g) : float_eq g f := h.symm

theorem Zpow_divide (b a c : Int) (_ : 0 < b) (h : 0 ≤ a ∧ a ≤ c) :
    zpowNat b a ∣ zpowNat b c := by
  simp only [zpowNat, ite_eq_right (by omega : ¬a < 0), ite_eq_right (by omega : ¬c < 0)]
  exact pow_dvd_pow _ (by omega)

private theorem align_mantissas {m n a b k : Int} (hk : k ≤ b) (hab : b ≤ a) :
    m * pow2 (a - k) = n * pow2 (b - k) ↔ n = m * pow2 (a - b) := by
  rw [show a - k = (a - b) + (b - k) by omega,
    pow2_add (by omega) (by omega), ← mul_assoc]
  exact ⟨fun h ↦ (mul_right_cancel₀ (pow2_pos (by omega)).ne' h).symm,
    fun h ↦ congrArg (· * _) h.symm⟩

private theorem eq_at_exponent {f g : bfloat} {k : Int} (hf : k ≤ f.Fexp) (hg : k ≤ g.Fexp) :
    float_eq f g ↔ f.Fnum * pow2 (f.Fexp - k) = g.Fnum * pow2 (g.Fexp - k) := by
  constructor
  · rintro (⟨le, h⟩ | ⟨le, h⟩)
    · exact (align_mantissas hg le).2 h
    · exact ((align_mantissas hf le).2 h).symm
  · intro h
    rcases le_total g.Fexp f.Fexp with h' | h'
    · exact Or.inl ⟨h', (align_mantissas hg h').1 h⟩
    · exact Or.inr ⟨h', (align_mantissas hf h').1 h.symm⟩

theorem float_eq_trans {f g k : bfloat} (fg : float_eq f g) (gk : float_eq g k) : float_eq f k := by
  let b := min (min f.Fexp g.Fexp) k.Fexp
  have hf : b ≤ f.Fexp := by dsimp [b]; omega
  have hg : b ≤ g.Fexp := by dsimp [b]; omega
  have hk : b ≤ k.Fexp := by dsimp [b]; omega
  exact (eq_at_exponent hf hk).2 (((eq_at_exponent hf hg).1 fg).trans ((eq_at_exponent hg hk).1 gk))

theorem float_eq_equivalence : Equivalence float_eq :=
  ⟨float_eq_refl, float_eq_sym, float_eq_trans⟩

def not_zero (f : bfloat) := f.Fnum ≠ 0

theorem not_zero_Zpos (m : Positive) (e : Int) : not_zero (BFloat m.val e) := by
  change (m.val : Int) ≠ 0
  exact_mod_cast m.property.ne'

theorem not_zero_eq (f g : bfloat) (hf : not_zero f) (h : float_eq f g) : not_zero g := by
  change g.Fnum ≠ 0
  rcases h with ⟨h, hm⟩ | ⟨_, hm⟩
  · rw [hm]; exact mul_ne_zero hf (pow2_pos (by omega)).ne'
  · intro hg; exact hf (by simpa [hg] using hm)

theorem inc_e_correct (f : bfloat) (d : Positive) {g : bfloat} (h : inc_e f d = some g) :
    g.Fexp = f.Fexp + d.val := by
  simp only [inc_e] at h
  split at h <;> cases h
  rfl

theorem dec_e_correct (f : bfloat) (d : Positive) :
    (dec_e f d).Fexp = f.Fexp - d.val := rfl

theorem shift_e_correct (f : bfloat) (d : Int) {g : bfloat} (h : shift_e f d = some g) :
    g.Fexp = f.Fexp + d := by
  unfold shift_e at h
  split at h
  · have he := inc_e_correct _ _ h; dsimp at he; omega
  · split at h
    · cases h; simp only [dec_e_correct]; omega
    · cases h; omega

theorem set_e_correct (f : bfloat) (e : Int) {g : bfloat} (h : set_e f e = some g) :
    g.Fexp = e := by have := shift_e_correct f _ h; omega

theorem inc_e_eq (f : bfloat) (d : Positive) {g : bfloat} (h : inc_e f d = some g) :
    float_eq f g := by
  simp only [inc_e] at h
  split at h <;> cases h
  rename_i hexact
  right
  simp only [add_sub_cancel_left, pow2, zpowNat, Int.natCast_nonneg, not_lt.mpr,
    ite_false, Int.toNat_natCast]
  exact ⟨by omega, (Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hexact)).symm⟩

theorem dec_e_eq (f : bfloat) (d : Positive) : float_eq f (dec_e f d) := by
  left
  simp [dec_e, pow2, zpowNat]

theorem shift_e_eq (f : bfloat) (d : Int) {g : bfloat} (h : shift_e f d = some g) : float_eq f g := by
  unfold shift_e at h
  split at h
  · exact inc_e_eq _ _ h
  · split at h
    · cases h; apply dec_e_eq
    · cases h; apply float_eq_refl

theorem set_e_eq (f : bfloat) (e : Int) {g : bfloat} : set_e f e = some g → float_eq f g :=
  shift_e_eq f _

private theorem digits_mul (m : Int) (n : Nat) (hm : m ≠ 0) :
    Zdigits (m * 2 ^ n) = Zdigits m + (n : Int) := by
  have hm' : 0 < m.natAbs := Int.natAbs_pos.mpr hm
  have log_mul : Nat.log 2 (m.natAbs * 2 ^ n) = Nat.log 2 m.natAbs + n := by
    induction n with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, ← mul_assoc, Nat.log_mul_base (by decide) (by positivity), ih]
        omega
  simp only [Zdigits, Int.natAbs_mul, Int.natAbs_pow, Nat.log2_eq_log_two]
  change (Nat.log 2 (m.natAbs * 2 ^ n) : Int) + 1 = _
  rw [log_mul]; omega

theorem Zdigits_mul_pow2 (m : Int) (d : Positive) (hm : m ≠ 0) :
    Zdigits (m * 2 ^ d.val) = Zdigits m + (d.val : Int) := digits_mul m d.val hm

theorem Zabs_div_exact (a b : Int) (hb : b ≠ 0) (h : a % b = 0) :
    |a / b| = |a| / |b| := by
  obtain ⟨k, rfl⟩ := Int.dvd_of_emod_eq_zero h
  simp [abs_mul, hb]

theorem Zdigits_div_pow2 (m : Int) (d : Positive) (hm : m ≠ 0) (h : m % 2 ^ d.val = 0) :
    Zdigits (m / 2 ^ d.val) = Zdigits m - (d.val : Int) := by
  have he := Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero h)
  have hn : m / 2 ^ d.val ≠ 0 := fun hz ↦ hm (by simpa [hz] using he.symm)
  have hd := Zdigits_mul_pow2 _ d hn
  rw [he] at hd; omega

/-- The position just above the highest set bit is invariant throughout a nonzero cohort. -/
private theorem total_digits {f g : bfloat} (nz : not_zero f) (eq : float_eq f g) :
    Zdigits f.Fnum + f.Fexp = Zdigits g.Fnum + g.Fexp := by
  have aux {m : Int} (hn : m ≠ 0) {d : Int} (hd : 0 ≤ d) :
      Zdigits (m * pow2 d) = Zdigits m + d := by
    simpa [pow2, zpowNat, not_lt.mpr hd, Int.toNat_of_nonneg hd] using digits_mul m d.toNat hn
  have nzg := not_zero_eq _ _ nz eq
  rcases eq with ⟨hle, hm⟩ | ⟨hle, hm⟩
  · rw [hm, aux nz (by omega)]; omega
  · rw [hm, aux nzg (by omega)]; omega

theorem inc_digits_m_correct (f : bfloat) (d : Positive) (nz : not_zero f) :
    Zdigits (inc_digits_m f d).Fnum = Zdigits f.Fnum + d.val :=
  Zdigits_mul_pow2 _ d nz

theorem dec_digits_m_correct (f : bfloat) (d : Positive) {g : bfloat} (nz : not_zero f)
    (h : dec_digits_m f d = some g) : Zdigits g.Fnum = Zdigits f.Fnum - d.val := by
  have he := inc_e_correct f d h
  have ht := total_digits nz (inc_e_eq f d h)
  omega

theorem shift_digits_m_correct (f : bfloat) (d : Int) {g : bfloat} (nz : f.Fnum ≠ 0)
    (h : shift_digits_m f d = some g) : Zdigits g.Fnum = Zdigits f.Fnum + d := by
  have he := shift_e_correct f (-d) h
  have ht := total_digits nz (shift_e_eq f (-d) h)
  omega

theorem set_digits_m_correct (f : bfloat) (d : Int) {g : bfloat} (nz : not_zero f)
    (h : set_digits_m f d = some g) : Zdigits g.Fnum = d := by
  have := shift_digits_m_correct f _ nz h
  omega

theorem inc_digits_m_eq (f : bfloat) (d : Positive) : float_eq f (inc_digits_m f d) :=
  dec_e_eq f d
theorem dec_digits_m_eq (f : bfloat) (d : Positive) {g : bfloat} :
    dec_digits_m f d = some g → float_eq f g := inc_e_eq f d
theorem shift_digits_m_eq (f : bfloat) (d : Int) {g : bfloat} :
    shift_digits_m f d = some g → float_eq f g := shift_e_eq f (-d)
theorem set_digits_m_eq (f : bfloat) (d : Int) {g : bfloat} :
    set_digits_m f d = some g → float_eq f g := shift_digits_m_eq f _

theorem exponent_unique_fnum (f g : bfloat) (eq : float_eq f g) (he : f.Fexp = g.Fexp) :
    f.Fnum = g.Fnum := by
  rcases eq with ⟨_, h⟩ | ⟨_, h⟩
  · simpa [he, pow2, zpowNat] using h.symm
  · simpa [he, pow2, zpowNat] using h

theorem exponent_unique (f g : bfloat) (eq : float_eq f g) (he : f.Fexp = g.Fexp) : f = g :=
  bfloat.ext (exponent_unique_fnum f g eq he) he

theorem Zdigits_m_unique_fexp (f g : bfloat) (nz : not_zero f) (eq : float_eq f g)
    (hd : Zdigits f.Fnum = Zdigits g.Fnum) : f.Fexp = g.Fexp := by
  have := total_digits nz eq; omega

theorem Zdigits_m_unique (f g : bfloat) (nz : not_zero f) (eq : float_eq f g)
    (hd : Zdigits f.Fnum = Zdigits g.Fnum) : f = g :=
  exponent_unique f g eq (Zdigits_m_unique_fexp f g nz eq hd)

theorem Zdigits_Zpos_log_inf (p : Positive) : Zdigits (p.val : Int) = (p.val.log2 : Int) + 1 := rfl
theorem Zdigits_Zneg_log_inf (p : Positive) : Zdigits (-(p.val : Int)) = (p.val.log2 : Int) + 1 := by
  simp [Zdigits]

theorem valid_float_closed_form (p e : Int) (f : bfloat) (nz : not_zero f) (hp : 0 < p)
    (he : p < e) : valid_float p e f = true ↔
      (Zdigits f.Fnum < p ∧ f.Fexp = 3 - e - p) ∨
      (Zdigits f.Fnum = p ∧ 3 - e - p ≤ f.Fexp ∧ f.Fexp ≤ e - p) := by
  have h : 0 < f.Fnum.natAbs := Int.natAbs_pos.mpr nz
  simpa [valid_float, h, Zdigits] using bounded_closed_form p e hp he ⟨_, h⟩ f.Fexp

theorem not_None_iff_exists_Some {A : Type u} {x : Option A} : x ≠ none ↔ ∃ y, x = some y := by
  cases x <;> simp

theorem float_eq_trans_l (f g k : bfloat) (fg : float_eq f g) (fk : float_eq f k) :
    float_eq g k := float_eq_trans (float_eq_sym fg) fk

theorem float_eq_set_e (f g : bfloat) (eq : float_eq f g) : set_e f g.Fexp = some g := by
  cases h : set_e f g.Fexp with
  | some k =>
      exact congrArg some (exponent_unique k g (float_eq_trans_l f k g (set_e_eq _ _ h) eq)
        (set_e_correct _ _ h))
  | none =>
      unfold set_e shift_e at h
      split at h
      · rename_i hp
        have hm : f.Fnum = g.Fnum * (2 : Int) ^ (g.Fexp - f.Fexp).toNat := by
          rcases eq with ⟨hle, _⟩ | ⟨_, hm⟩
          · omega
          · simpa [pow2, zpowNat, not_lt.mpr hp.le] using hm
        have hd : (2 : Int) ^ (g.Fexp - f.Fexp).toNat ∣ f.Fnum :=
          ⟨g.Fnum, hm.trans (mul_comm _ _)⟩
        simp [inc_e, Int.emod_eq_zero_of_dvd hd] at h
      · split at h <;> cases h

theorem float_eq_set_digits_m (f g : bfloat) (nz : not_zero f) (eq : float_eq f g) :
    set_digits_m f (Zdigits g.Fnum) = some g := by
  have ht := total_digits nz eq
  unfold set_digits_m shift_digits_m
  rw [show -(Zdigits g.Fnum - Zdigits f.Fnum) = g.Fexp - f.Fexp by omega]
  exact float_eq_set_e f g eq

theorem set_e_definition (f : bfloat) (e : Int) {g : bfloat} :
    set_e f e = some g ↔ float_eq f g ∧ g.Fexp = e :=
  ⟨fun h ↦ ⟨set_e_eq f e h, set_e_correct f e h⟩, fun ⟨eq, he⟩ ↦ he ▸ float_eq_set_e f g eq⟩

theorem set_digits_m_definition (f : bfloat) (d : Int) {g : bfloat} (nz : not_zero f) :
    set_digits_m f d = some g ↔ float_eq f g ∧ Zdigits g.Fnum = d :=
  ⟨fun h ↦ ⟨set_digits_m_eq f d h, set_digits_m_correct f d nz h⟩,
    fun ⟨eq, hd⟩ ↦ hd ▸ float_eq_set_digits_m f g nz eq⟩

theorem normalize_correct (p e : Int) (f : bfloat) (nz : not_zero f) (hp : 0 < p) (he : p < e)
    {nf : bfloat} : normalize_float p e f = some nf ↔ float_eq f nf ∧ valid_float p e nf = true := by
  let lo := 3 - e - p
  have hlo : 3 - e - p = lo := rfl
  have range : lo ≤ e - p := by dsimp [lo]; omega
  constructor
  · intro h
    cases h₁ : set_e f lo with
    | none => simp [normalize_float, hlo, h₁] at h
    | some f₁ =>
      have eq₁ := set_e_eq f lo h₁
      have exp₁ := set_e_correct f lo h₁
      by_cases small : Zdigits f₁.Fnum ≤ p
      · have ident : f₁ = nf := by simpa [normalize_float, hlo, h₁, small] using h
        subst nf
        refine ⟨eq₁, (valid_float_closed_form p e _ (not_zero_eq _ _ nz eq₁) hp he).2 ?_⟩
        rcases lt_or_eq_of_le small with lt | eq
        · exact Or.inl ⟨lt, exp₁⟩
        · exact Or.inr ⟨eq, exp₁.ge, exp₁.le.trans range⟩
      · cases h₂ : set_digits_m f p with
        | none => simp [normalize_float, hlo, h₁, small, h₂] at h
        | some f₂ =>
          by_cases fits : lo ≤ f₂.Fexp ∧ f₂.Fexp ≤ e - p
          · have ident : f₂ = nf := by simpa [normalize_float, hlo, h₁, small, h₂, fits] using h
            subst nf
            have eq₂ := set_digits_m_eq _ _ h₂
            exact ⟨eq₂, (valid_float_closed_form p e _ (not_zero_eq _ _ nz eq₂) hp he).2
              (Or.inr ⟨set_digits_m_correct f p nz h₂, fits⟩)⟩
          · simp [normalize_float, hlo, h₁, small, h₂, fits] at h
  · rintro ⟨eq, valid⟩
    have nz' := not_zero_eq _ _ nz eq
    rcases (valid_float_closed_form p e _ nz' hp he).1 valid with ⟨hd, hi⟩ | ⟨hd, hi⟩
    · have h₁ : set_e f lo = some nf := (set_e_definition _ _).2 ⟨eq, hi⟩
      simp [normalize_float, hlo, h₁, hd.le]
    · change lo ≤ nf.Fexp ∧ nf.Fexp ≤ e - p at hi
      let f₁ := BFloat (nf.Fnum * pow2 (nf.Fexp - lo)) lo
      have eq₁ : float_eq nf f₁ := Or.inl ⟨hi.1, rfl⟩
      have h₁ : set_e f lo = some f₁ := float_eq_set_e _ _ (float_eq_trans eq eq₁)
      have h₂ : set_digits_m f p = some nf := (set_digits_m_definition _ _ nz).2 ⟨eq, hd⟩
      by_cases small : Zdigits f₁.Fnum ≤ p
      · have ht := total_digits nz' eq₁
        have exp₁ : f₁.Fexp = lo := rfl
        have same := exponent_unique nf f₁ eq₁ (by omega)
        simpa [normalize_float, hlo, h₁, small] using same.symm
      · simp [normalize_float, hlo, h₁, small, h₂, hi]

theorem normalize_correct' (p e : Int) (f : bfloat) (nz : not_zero f) (hp : 0 < p) (he : p < e) :
    match normalize_float p e f with
    | some nf => float_eq f nf ∧ valid_float p e nf = true
    | none => ∀ xf : bfloat, float_eq f xf → valid_float p e xf = false := by
  cases h : normalize_float p e f with
  | some nf => exact (normalize_correct p e f nz hp he).1 h
  | none =>
    intro xf eq
    cases hv : valid_float p e xf with
    | false => rfl
    | true =>
      have hf := (normalize_correct p e f nz hp he).2 ⟨eq, hv⟩
      simp [h] at hf

example : normalize_float 2 3 ⟨-12, -2⟩ = some ⟨-3, 0⟩ ∧
    normalize_float 2 3 ⟨-13, -2⟩ = none := by decide

-- 2⁻¹⁵⁰ is binary64-normal, but lies halfway between binary32 zero and its first subnormal.
example :
    let v : binary_float 53 1024 := .B754_finite false ⟨2 ^ 52, by decide⟩ (-202) (by decide)
    can_convert_float_to_float32 v = false := by decide

example : can_convert_float_to_float64 (.B754_finite true ⟨1, by decide⟩ (-1074) (by decide))
    = true := by decide

end Vellvm.Utils.ParserHelper
