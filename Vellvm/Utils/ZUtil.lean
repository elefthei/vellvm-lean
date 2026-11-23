module

public import Vellvm.Types
public import Mathlib.Data.List.Basic
public import Mathlib.Algebra.Order.Ring.Int

@[expose] public section
namespace Vellvm.Utils.ZUtil

/-- `Z.pow` gives zero at every negative exponent, including for a unit base. -/
def zPow (a : Int) : Int → Int
  | .ofNat n => a ^ n
  | .negSucc _ => 0

/-- Negative `Z.shiftl` counts are arithmetic right shifts. -/
def shiftl (a : Int) : Int → Int
  | .ofNat n => a <<< n
  | .negSucc n => a >>> (n + 1)

def two_power_pos (p : Positive) : Int := (1 : Int) <<< p.val

theorem two_power_pos_eq (p : Positive) : two_power_pos p = zPow 2 (Int.ofNat p.val) := by
  simp [two_power_pos, Int.shiftLeft_eq, zPow]

theorem Z_gtb_irrefl (z : Int) : decide (z > z) = false := by simp

/-- Concatenate digits least-significant first, shifting the higher digits by `w` bits. -/
def concat_digits (w : Int) : List Int → Int
  | [] => 0
  | z :: l => z + shiftl (concat_digits w l) w

private theorem radix_pow (w k : Nat) : zPow 2 (Int.ofNat w * Int.ofNat k) = ((2 : Int) ^ w) ^ k :=
  pow_mul (2 : Int) w k

theorem concat_digits_range (w : Int) (l : List Int) (hw : 0 < w)
    (hl : List.Forall (fun z ↦ 0 ≤ z ∧ z < zPow 2 w) l) :
    0 ≤ concat_digits w l ∧ concat_digits w l < zPow 2 (w * Int.ofNat l.length) := by
  cases w with
  | negSucc _ => omega
  | ofNat n =>
    have hp : 0 < (2 : Int) ^ n := Int.pow_pos (by decide)
    induction l with
    | nil => simp [concat_digits, zPow]
    | cons z l ih =>
      obtain ⟨⟨hz₀, hz⟩, hl⟩ := (List.forall_cons _ _ _).mp hl
      obtain ⟨hc₀, hc⟩ := ih hl
      change z < (2 : Int) ^ n at hz
      rw [radix_pow] at hc
      have hs : concat_digits (.ofNat n) l + 1 ≤ ((2 : Int) ^ n) ^ l.length := by omega
      simp only [concat_digits, shiftl, Int.shiftLeft_eq, List.length_cons, radix_pow, pow_succ]
      refine ⟨Int.add_nonneg hz₀ (Int.mul_nonneg hc₀ hp.le), ?_⟩
      calc
        _ < (concat_digits (.ofNat n) l + 1) * (2 : Int) ^ n := by rw [add_mul, one_mul]; omega
        _ ≤ _ := Int.mul_le_mul_of_nonneg_right hs hp.le

theorem concat_digits_nth (w : Int) (l : List Int) (i : Nat) (hw : 0 < w)
    (hl : List.Forall (fun z ↦ 0 ≤ z ∧ z < zPow 2 w) l) (hi : i < l.length) :
    concat_digits w l / zPow 2 (w * Int.ofNat i) % zPow 2 w = l.getD i 0 := by
  cases w with
  | negSucc _ => omega
  | ofNat n =>
    have hp : 0 < (2 : Int) ^ n := Int.pow_pos (by decide)
    induction l generalizing i with
    | nil => simp at hi
    | cons z l ih =>
      obtain ⟨⟨hz₀, hz⟩, hl⟩ := (List.forall_cons _ _ _).mp hl
      change z < (2 : Int) ^ n at hz
      rw [radix_pow]
      simp only [concat_digits, shiftl, Int.shiftLeft_eq, zPow]
      cases i with
      | zero =>
        rw [pow_zero, Int.ediv_one, Int.add_mul_emod_self_right, Int.emod_eq_of_lt hz₀ hz,
          List.getD_cons_zero]
      | succ i =>
        rw [pow_succ', ← Int.ediv_ediv_of_nonneg hp.le, Int.add_mul_ediv_right _ _ hp.ne',
          Int.ediv_eq_zero_of_lt hz₀ hz, zero_add, List.getD_cons_succ]
        have ht := ih i (Nat.lt_of_succ_lt_succ hi) hl
        rwa [radix_pow] at ht

end Vellvm.Utils.ZUtil
