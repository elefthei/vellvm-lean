module

public import Vellvm.Semantics.MemoryBytes.Digits
public import Vellvm.Utils.ListUtil
public import Vellvm.Numeric.Integers.Powers

@[expose] public section
namespace Vellvm.Theory.MemoryBytesFacts
open Semantics.MemoryBytes Utils.ListUtil Numeric.Integers

def extract_bit_N (x idx : Nat) : Nat := (x >>> idx) % 2

private theorem radix_step (a b c : Int) (hb : 0 ≤ b) :
    a % b + b * (a / b % c) = a % (b*c) := by
  simp only [Int.emod_def, Int.ediv_ediv_of_nonneg hb]
  rw [Int.mul_sub, ← Int.mul_assoc]; omega

theorem concat_bytes_Z_extract (k : Nat) (v : Int) (j : Nat) :
    concat_bytes_Z ((Nseq j k).map (fun i ↦ v / 2^(8*i) % 256)) = v / 2^(8*j) % 2^(8*k) := by
  induction k generalizing j with
  | zero => simp [Nseq, concat_bytes_Z]
  | succ k ih =>
    simp only [Nseq, List.map_cons, concat_bytes_Z, ih, Nat.mul_succ, Int.pow_add]
    rw [← Int.ediv_ediv_of_nonneg (Int.pow_nonneg (by decide : (0:Int) ≤ 2)), Int.mul_comm (2^(8*k))]
    exact radix_step _ 256 _ (by decide)

theorem extract_byte_vint_spec_lt {sz : Positive} (x : bit_int sz) (idx : Nat)
    (h : 8 * (idx : Int) < (sz.val : Int)) :
    extract_byte_vint x idx = unsigned x / 2^(8*idx) % 256 := by
  have hm : @modulus sz = ((2^sz.val : Nat) : Int) := modulus_def
  have hs : unsigned (@Numeric.Integers.repr sz ((idx : Int)*8)) = ((8*idx : Nat) : Int) := by
    rw [unsigned_repr _ ⟨by omega, by have := @wordsize_max_unsigned sz; change (sz.val : Int) ≤ _ at this; omega⟩]
    omega
  have shift : unsigned (shru x (Numeric.Integers.repr ((idx : Int)*8))) = unsigned x / 2^(8*idx) := by
    change (((x.bits >>> (Numeric.Integers.repr (w := sz) ((idx : Int)*8)).bits.toNat).toNat : Nat) : Int) = _
    change ((_ : Nat) : Int) = _ at hs
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Int.natCast_ediv, Int.natCast_pow,
      Int.ofNat_inj.mp hs]
    rfl
  let q := unsigned x / 2^(8*idx)
  have hx := unsigned_range x
  have hq : 0 ≤ q ∧ q < @modulus sz :=
    ⟨Int.ediv_nonneg hx.1 (Int.pow_nonneg (by decide)), Int.lt_of_le_of_lt (Int.ediv_le_self _ hx.1) hx.2⟩
  change unsigned (Numeric.Integers.repr ((unsigned (shru x (Numeric.Integers.repr ((idx : Int)*8)))).fmod (unsigned (Numeric.Integers.repr (w := sz) 256)))) = _
  rw [shift, Int.fmod_eq_emod_of_nonneg _ (unsigned_range _).1]
  change unsigned (Numeric.Integers.repr (w := sz) (q % unsigned (Numeric.Integers.repr (w := sz) 256))) = q % 256
  by_cases small : sz.val ≤ 8
  · have hd := Int.ofNat_dvd.mpr (Nat.pow_dvd_pow 2 small)
    have hmle := Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide : 0 < 2) small)
    change ((2^sz.val : Nat) : Int) ∣ 256 at hd
    change ((2^sz.val : Nat) : Int) ≤ 256 at hmle
    rw [unsigned_repr_eq 256, Int.fmod_eq_emod_of_nonneg _ (Int.le_of_lt modulus_pos), hm,
      Int.emod_eq_zero_of_dvd hd, Int.emod_zero, unsigned_repr _ ⟨hq.1, by unfold max_unsigned; omega⟩,
      Int.emod_eq_of_lt hq.1 (by rw [hm] at hq; omega)]
  · have hb : 256 < @modulus sz := by
      rw [hm]; exact Int.ofNat_lt.mpr (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega : 8 < sz.val))
    rw [unsigned_repr 256 ⟨by decide, by unfold max_unsigned; omega⟩]
    apply unsigned_repr
    exact ⟨Int.emod_nonneg _ (by decide), by have := Int.emod_lt_of_pos q (by decide : (0:Int)<256); unfold max_unsigned; omega⟩

theorem extract_byte_vint_spec {sz : Positive} (x : bit_int sz) (idx : Nat)
    (h : 8 * ((idx : Int) + 1) ≤ (sz.val : Int)) :
    extract_byte_vint x idx = unsigned x / 2^(8*idx) % 256 := extract_byte_vint_spec_lt x idx (by omega)

theorem extract_bit_N_spec {v : Int} (i : Nat) (h : 0 ≤ v) :
    (extract_bit_N v.toNat i : Int) = v / 2^i % 2 := by
  simp [extract_bit_N, Nat.shiftRight_eq_div_pow, Int.natCast_emod, Int.natCast_ediv,
    Int.toNat_of_nonneg h]

theorem concat_bits_Z_extract (n : Nat) (v : Int) (j : Nat) :
    concat_bits_Z ((Nseq j n).map (fun i ↦ v / 2^i % 2)) = v / 2^j % 2^n := by
  induction n generalizing j with
  | zero => simp [Nseq, concat_bits_Z]
  | succ n ih =>
    simp only [Nseq, List.map_cons, concat_bits_Z, ih, Int.pow_succ]
    rw [← Int.ediv_ediv_of_nonneg (Int.pow_nonneg (by decide : (0:Int) ≤ 2)), Int.mul_comm (2^n)]
    exact radix_step _ 2 _ (by decide)

theorem extract_byte_Z_spec (v : Int) (idx : Nat) : extract_byte_Z v idx = v / 2^(8*idx) % 256 := rfl

theorem concat_bytes_vint_Z (w : Positive) (zs : List Int) (h : 8 < @modulus w) :
    concat_bytes_vint (zs.map (@Numeric.Integers.repr w)) = Numeric.Integers.repr (concat_bytes_Z zs) := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    simp only [List.map_cons, concat_bytes_vint, concat_bytes_Z, ih]
    change add _ (shl _ (Numeric.Integers.repr 8)) = _
    rw [shl_mul_two_p, mul, add, unsigned_repr 8 ⟨by decide, by unfold max_unsigned; omega⟩]
    apply eqm_samerepr
    apply eqm_add _ _ _ _ (eqm_unsigned_repr_l _ _ (eqm_refl _))
    apply eqm_unsigned_repr_l
    rw [Int.mul_comm 256]
    exact eqm_mult _ _ _ _ (eqm_unsigned_repr_l _ _ (eqm_refl _)) (eqm_unsigned_repr_l _ _ (eqm_refl _))

end Vellvm.Theory.MemoryBytesFacts
