/-
The Compcert verified compiler. Xavier Leroy and Jacques-Henri Jourdan, INRIA Paris-Rocquencourt.
Copyright Institut National de Recherche en Informatique et en Automatique. All rights reserved.
Distributed under the GNU Lesser General Public License, version 2.1 or later, and also under
 the terms of the INRIA Non-Commercial License Agreement.
-/
import Vellvm.Numeric.Floats.NaN
import Vellvm.Numeric.Floats.Fused

namespace Vellvm.Numeric.Floats
open Flocq Integers

def cmp_of_comparison : comparison → Option Ordering → Bool
  | .Ceq, x => x == some .eq
  | .Cne, x => x != some .eq
  | .Clt, x => x == some .lt
  | .Cle, some .eq | .Cle, some .lt => true
  | .Cgt, x => x == some .gt
  | .Cge, some .eq | .Cge, some .gt => true
  | _, _ => false

def ordered_of_comparison (x : Option Ordering) := x.isSome

theorem cmp_of_comparison_swap (c : comparison) (x : Option Ordering) :
    cmp_of_comparison (swap_comparison c) x = cmp_of_comparison c (x.map Ordering.swap) := by
  cases c <;> rcases x with _ | (_ | _ | _) <;> rfl

theorem cmp_of_comparison_ne_eq (x : Option Ordering) :
    cmp_of_comparison Cne x = !cmp_of_comparison Ceq x := rfl

theorem cmp_of_comparison_lt_eq_false (x : Option Ordering) :
    cmp_of_comparison Clt x = true → cmp_of_comparison Ceq x = true → False := by
  rcases x with _ | (_ | _ | _) <;> decide

theorem cmp_of_comparison_le_lt_eq (x : Option Ordering) :
    cmp_of_comparison Cle x = (cmp_of_comparison Clt x || cmp_of_comparison Ceq x) := by
  rcases x with _ | (_ | _ | _) <;> rfl

theorem cmp_of_comparison_gt_eq_false (x : Option Ordering) :
    cmp_of_comparison Cgt x = true → cmp_of_comparison Ceq x = true → False := by
  rcases x with _ | (_ | _ | _) <;> decide

theorem cmp_of_comparison_ge_gt_eq (x : Option Ordering) :
    cmp_of_comparison Cge x = (cmp_of_comparison Cgt x || cmp_of_comparison Ceq x) := by
  rcases x with _ | (_ | _ | _) <;> rfl

theorem cmp_of_comparison_lt_gt_false (x : Option Ordering) :
    cmp_of_comparison Clt x = true → cmp_of_comparison Cgt x = true → False := by
  rcases x with _ | (_ | _ | _) <;> decide

private def absolute {p e : Int} : binary_float p e → binary_float p e
  | .B754_zero _ => .B754_zero false
  | .B754_infinity _ => .B754_infinity false
  | .B754_nan _ m h => .B754_nan false m h
  | .B754_finite _ m i h => .B754_finite false m i h

open IEEE754_extra (BofZ Bconv Bparse ZofB_range Bexact_inverse Beq_dec)

namespace Float

def zero : float := .B754_zero false
def eq_dec := Beq_dec 53 1024
def neg := @Flocq.neg 53 1024
def abs := @absolute 53 1024
def sqrt := sqrtNE (by decide) (by decide) unop_nan
def add := Bplus 53 1024 (by decide) (by decide) binop_nan .mode_NE
def sub := Bminus 53 1024 (by decide) (by decide) binop_nan .mode_NE
def mul := Bmult 53 1024 (by decide) (by decide) binop_nan .mode_NE
def div := Bdiv 53 1024 (by decide) (by decide) binop_nan .mode_NE
def fma := fusedNE (by decide) (by decide) fma_nan
def compare := @Bcompare 53 1024
def cmp (c : comparison) (x y : float) := cmp_of_comparison c (compare x y)
def ordered (x y : float) := ordered_of_comparison (compare x y)

def of_single := Bconv 24 128 53 1024 (by decide) (by decide) of_single_nan .mode_NE
def to_single := Bconv 53 1024 24 128 (by decide) (by decide) to_single_nan .mode_NE

def to_int (x : float) := (ZofB_range 53 1024 x (@min_signed w32) (@max_signed w32)).map (@Integers.repr w32)
def to_intu (x : float) := (ZofB_range 53 1024 x 0 (@max_unsigned w32)).map (@Integers.repr w32)
def to_long (x : float) := (ZofB_range 53 1024 x (@min_signed w64) (@max_signed w64)).map (@Integers.repr w64)
def to_longu (x : float) := (ZofB_range 53 1024 x 0 (@max_unsigned w64)).map (@Integers.repr w64)

def of_int (n : bit_int w32) := BofZ 53 1024 (by decide) (by decide) (Integers.signed n)
def of_intu (n : bit_int w32) := BofZ 53 1024 (by decide) (by decide) (unsigned n)
def of_long (n : bit_int w64) := BofZ 53 1024 (by decide) (by decide) (Integers.signed n)
def of_longu (n : bit_int w64) := BofZ 53 1024 (by decide) (by decide) (unsigned n)

def from_parsed := Bparse 53 1024 (by decide) (by decide)
def from_words (hi lo : bit_int w32) := of_bits (ofwords hi lo)

def exact_inverse := Bexact_inverse 53 1024 (by decide) (by decide)
def ox8000_0000 := @Integers.repr w32 (@half_modulus w32)
def ox7FFF_FFFF := @Integers.repr w32 (@max_signed w32)
def ox4330_0000 := @Integers.repr w32 1127219200
def ox4530_0000 := @Integers.repr w32 1160773632

end Float

namespace Float32

def zero : float32 := .B754_zero false
def eq_dec := Beq_dec 24 128
def neg := @Flocq.neg 24 128
def abs := @absolute 24 128
def sqrt := sqrtNE (by decide) (by decide) unop_nan
def add := Bplus 24 128 (by decide) (by decide) binop_nan .mode_NE
def sub := Bminus 24 128 (by decide) (by decide) binop_nan .mode_NE
def mul := Bmult 24 128 (by decide) (by decide) binop_nan .mode_NE
def div := Bdiv 24 128 (by decide) (by decide) binop_nan .mode_NE
def fma := fusedNE (by decide) (by decide) fma_nan
def compare := @Bcompare 24 128
def cmp (c : comparison) (x y : float32) := cmp_of_comparison c (compare x y)
def ordered (x y : float32) := ordered_of_comparison (compare x y)

def of_double := Float.to_single
def to_double := Float.of_single

def to_int (x : float32) := (ZofB_range 24 128 x (@min_signed w32) (@max_signed w32)).map (@Integers.repr w32)
def to_intu (x : float32) := (ZofB_range 24 128 x 0 (@max_unsigned w32)).map (@Integers.repr w32)
def to_long (x : float32) := (ZofB_range 24 128 x (@min_signed w64) (@max_signed w64)).map (@Integers.repr w64)
def to_longu (x : float32) := (ZofB_range 24 128 x 0 (@max_unsigned w64)).map (@Integers.repr w64)

def of_int (n : bit_int w32) := BofZ 24 128 (by decide) (by decide) (Integers.signed n)
def of_intu (n : bit_int w32) := BofZ 24 128 (by decide) (by decide) (unsigned n)
def of_long (n : bit_int w64) := BofZ 24 128 (by decide) (by decide) (Integers.signed n)
def of_longu (n : bit_int w64) := BofZ 24 128 (by decide) (by decide) (unsigned n)

def from_parsed := Bparse 24 128 (by decide) (by decide)

def exact_inverse := Bexact_inverse 24 128 (by decide) (by decide)

end Float32
end Vellvm.Numeric.Floats
