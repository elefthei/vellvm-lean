/-
The Compcert verified compiler. Xavier Leroy and Jacques-Henri Jourdan, INRIA Paris-Rocquencourt.
Copyright Institut National de Recherche en Informatique et en Automatique. All rights reserved.
Distributed under the GNU Lesser General Public License, version 2.1 or later, and also under
 the terms of the INRIA Non-Commercial License Agreement.
-/
import Vellvm.Numeric.Flocq.Bits
import Vellvm.Numeric.Integers.Basic

namespace Vellvm.Numeric.Floats
open Flocq Integers

abbrev float := binary_float 53 1024
abbrev float32 := binary_float 24 128

def Float.to_bits (f : float) := @Integers.repr w64 (bits_of_b64 f)
def Float.of_bits (b : bit_int w64) := b64_of_bits (unsigned b)
def Float32.to_bits (f : float32) := @Integers.repr w32 (bits_of_b32 f)
def Float32.of_bits (b : bit_int w32) := b32_of_bits (unsigned b)

end Vellvm.Numeric.Floats
