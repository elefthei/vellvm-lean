import PortChecks.SourceType
import Vellvm.Numeric.Floats.BitsFacts

open Vellvm.Numeric.Floats Vellvm.Numeric.Integers

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|of_to_bits"
  Vellvm.Numeric.Floats.Float.of_to_bits : ∀ f : float, Float.of_bits (Float.to_bits f) = f

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float|to_of_bits"
  Vellvm.Numeric.Floats.Float.to_of_bits : ∀ b : bit_int w64, Float.to_bits (Float.of_bits b) = b

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|of_to_bits"
  Vellvm.Numeric.Floats.Float32.of_to_bits : ∀ f : float32, Float32.of_bits (Float32.to_bits f) = f

#source_check "src/rocq/Numeric/Floats.v|Vellvm.Numeric.Floats.Float32|to_of_bits"
  Vellvm.Numeric.Floats.Float32.to_of_bits : ∀ b : bit_int w32, Float32.to_bits (Float32.of_bits b) = b
