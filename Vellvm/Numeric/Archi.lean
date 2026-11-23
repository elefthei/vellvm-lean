/-
The Compcert verified compiler
Xavier Leroy and Jacques-Henri Jourdan, INRIA Paris-Rocquencourt
Copyright Institut National de Recherche en Informatique et en Automatique. All rights reserved.
This file is distributed under the terms of the GNU Lesser General Public License as published by
 the Free Software Foundation, either version 2.1 of the License, or (at your option) any later
version. This file is also distributed under the terms of the INRIA Non-Commercial License Agreement.
-/
module

public import Vellvm.Types

@[expose] public section
namespace Vellvm.Numeric

structure Archi where
  ppc64 : Bool

namespace Archi

def ptr64 := false
def big_endian := true
def align_int64 : Int := 8
def align_float64 : Int := 8
def splitlong (a : Archi) := !a.ppc64

theorem splitlong_ptr32 (a : Archi) : splitlong a = true → ptr64 = false := fun _ ↦ rfl

def default_nan_64 : Bool × Positive := (false, ⟨2 ^ 51, by decide⟩)
def default_nan_32 : Bool × Positive := (false, ⟨2 ^ 22, by decide⟩)
def choose_nan_64 (l : List (Bool × Positive)) := l.headD default_nan_64
def choose_nan_32 (l : List (Bool × Positive)) := l.headD default_nan_32

theorem choose_nan_64_idem (n : Bool × Positive) : choose_nan_64 [n, n] = choose_nan_64 [n] := rfl
theorem choose_nan_32_idem (n : Bool × Positive) : choose_nan_32 [n, n] = choose_nan_32 [n] := rfl

def fma_order {A : Type u} (x y z : A) := ((x, z), y)
def fma_invalid_mul_is_nan := false
def float_of_single_preserves_sNaN := true

end Archi
end Vellvm.Numeric
