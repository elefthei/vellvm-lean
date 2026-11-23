import PortChecks.SourceType
import Vellvm.Utils.StringUtil

open Vellvm Vellvm.Utils.StringUtil
universe u v

#source_check "src/rocq/Utils/StringUtil.v|Vellvm.Utils.StringUtil|showUint"
  showUint : Show Decimal.uint
#source_check "src/rocq/Utils/StringUtil.v|Vellvm.Utils.StringUtil|showInt"
  showInt : Show Decimal.signed_int
#source_check "src/rocq/Utils/StringUtil.v|Vellvm.Utils.StringUtil|showNat"
  showNat : Show Nat
#source_check "src/rocq/Utils/StringUtil.v|Vellvm.Utils.StringUtil|showBool"
  showBool : Show Bool
#source_check "src/rocq/Utils/StringUtil.v|Vellvm.Utils.StringUtil|showZ"
  showZ : Show Int
#source_check "src/rocq/Utils/StringUtil.v|Vellvm.Utils.StringUtil|showN"
  showN : Show Nat
#source_check "src/rocq/Utils/StringUtil.v|Vellvm.Utils.StringUtil|showString"
  showString : Show IRString
#source_check "src/rocq/Utils/StringUtil.v|Vellvm.Utils.StringUtil|showPair"
  showPair : ∀ {A : Type u} {B : Type v} [Show A] [Show B], Show (A × B)
#source_check "src/rocq/Utils/StringUtil.v|Vellvm.Utils.StringUtil|showOpt"
  showOpt : ∀ {A : Type u} [Show A], Show (Option A)
#source_check "src/rocq/Utils/StringUtil.v|Vellvm.Utils.StringUtil|showList"
  showList : ∀ {A : Type u} [Show A], Show (List A)

-- These examples compare raw bytes, including input that is not UTF-8.
example : («show» (from_list [0, 9, 10, 13, 34, 92, 32, 126, 127, 255])).data =
    "\"\\000\\t\\n\\r\\\"\\\\ ~\\127\\255\"".toUTF8.data := by decide
example : unthree_digit 57 57 57 = some 231 ∧ unthree_digit 47 48 49 = none := by decide
example : show_int (.Neg (.D0 (.D4 .Nil))) = "-04".toUTF8 := by decide
example : («show» ([some (⟨42, by decide⟩ : Positive), none], (-19 : Int))) =
    "([Some 42; None], -19)".toUTF8 := by decide +kernel
