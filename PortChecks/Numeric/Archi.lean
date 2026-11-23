import PortChecks.SourceType
import Vellvm.Numeric.Archi

open Vellvm Vellvm.Numeric Vellvm.Numeric.Archi

#source_check "src/rocq/Numeric/Archi.v|Vellvm.Numeric.Archi|splitlong_ptr32"
  splitlong_ptr32 : ∀ a : Archi, splitlong a = true → ptr64 = false

#source_check "src/rocq/Numeric/Archi.v|Vellvm.Numeric.Archi|choose_nan_64_idem"
  choose_nan_64_idem : ∀ n : Bool × Positive, choose_nan_64 [n, n] = choose_nan_64 [n]

#source_check "src/rocq/Numeric/Archi.v|Vellvm.Numeric.Archi|choose_nan_32_idem"
  choose_nan_32_idem : ∀ n : Bool × Positive, choose_nan_32 [n, n] = choose_nan_32 [n]
