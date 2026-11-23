import PortChecks.SourceType
import Vellvm.Utils.ZUtil

open Vellvm Vellvm.Utils.ZUtil

#source_check "src/rocq/Utils/ZUtil.v|Vellvm.Utils.ZUtil|two_power_pos_eq"
  two_power_pos_eq : ∀ p : Positive, two_power_pos p = zPow 2 (Int.ofNat p.val)

#source_check "src/rocq/Utils/ZUtil.v|Vellvm.Utils.ZUtil|Z_gtb_irrefl"
  Z_gtb_irrefl : ∀ z : Int, decide (z > z) = false

#source_check "src/rocq/Utils/ZUtil.v|Vellvm.Utils.ZUtil|concat_digits_range"
  concat_digits_range : ∀ (w : Int) (l : List Int),
    0 < w → List.Forall (fun z ↦ 0 ≤ z ∧ z < zPow 2 w) l →
    0 ≤ concat_digits w l ∧ concat_digits w l < zPow 2 (w * Int.ofNat l.length)

#source_check "src/rocq/Utils/ZUtil.v|Vellvm.Utils.ZUtil|concat_digits_nth"
  concat_digits_nth : ∀ (w : Int) (l : List Int) (i : Nat),
    0 < w → List.Forall (fun z ↦ 0 ≤ z ∧ z < zPow 2 w) l → i < l.length →
    concat_digits w l / zPow 2 (w * Int.ofNat i) % zPow 2 w = l.getD i 0

example : zPow 1 (-1) = 0 := by decide
example : concat_digits (-1) [2, -5] = -1 := by decide
