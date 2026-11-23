/-
The Compcert verified compiler
Xavier Leroy and Jacques-Henri Jourdan, INRIA Paris-Rocquencourt

Copyright Institut National de Recherche en Informatique et en Automatique.
All rights reserved. This file is distributed under the terms of the GNU Lesser
General Public License as published by the Free Software Foundation, either
version 2.1 of the License, or (at your option) any later version.
This file is also distributed under the terms of the INRIA Non-Commercial
License Agreement.
-/
import Vellvm.Numeric.Floats.Raw

namespace Vellvm.Numeric.Floats
open Vellvm.Numeric.Integers Vellvm.Numeric.Flocq

namespace Float

theorem of_to_bits (f : float) : of_bits (to_bits f) = f := by
  unfold of_bits to_bits
  rw [unsigned_repr, b64_of_bits_of_b64]
  have h := bits_of_b64_range f
  exact ⟨h.1, Int.le_sub_one_of_lt h.2⟩

theorem to_of_bits (b : bit_int w64) : to_bits (of_bits b) = b := by
  unfold to_bits of_bits
  rw [bits_of_b64_of_bits _ (unsigned_range b), repr_unsigned]

end Float
namespace Float32

theorem of_to_bits (f : float32) : of_bits (to_bits f) = f := by
  unfold of_bits to_bits
  rw [unsigned_repr, b32_of_bits_of_b32]
  have h := bits_of_b32_range f
  exact ⟨h.1, Int.le_sub_one_of_lt h.2⟩

theorem to_of_bits (b : bit_int w32) : to_bits (of_bits b) = b := by
  unfold to_bits of_bits
  rw [bits_of_b32_of_bits _ (unsigned_range b), repr_unsigned]

end Float32
end Vellvm.Numeric.Floats
