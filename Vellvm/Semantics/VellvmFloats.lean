/- Translated from Vellvm's Semantics/VellvmFloats.v (see LICENSE.md). -/
import Vellvm.Numeric.Floats.Basic
import Vellvm.Syntax.LLVMAst

namespace Vellvm.Semantics.VellvmFloats
open Numeric Numeric.Floats Syntax.LLVMAst

class VFloat (FP : Type u) where
  Build_VFloat ::
  denote_fp_syntax : float_syntax → Option FP
export VFloat (Build_VFloat denote_fp_syntax)

def uint_is_zero (us : Decimal.uint) : Bool := us.toNat == 0

def xx : Decimal.uint := .D1 (.D2 (.D3 .Nil))

/-- The exponent counts written digits, including leading zeroes in the fraction. -/
private def fraction (ys : Decimal.uint) : Nat × Nat := go ys 0 0
where
  go : Decimal.uint → Nat → Nat → Nat × Nat
    | .Nil, m, n => (m, n)
    | .D0 t, m, n => go t (10 * m) (n + 1)
    | .D1 t, m, n => go t (10 * m + 1) (n + 1)
    | .D2 t, m, n => go t (10 * m + 2) (n + 1)
    | .D3 t, m, n => go t (10 * m + 3) (n + 1)
    | .D4 t, m, n => go t (10 * m + 4) (n + 1)
    | .D5 t, m, n => go t (10 * m + 5) (n + 1)
    | .D6 t, m, n => go t (10 * m + 6) (n + 1)
    | .D7 t, m, n => go t (10 * m + 7) (n + 1)
    | .D8 t, m, n => go t (10 * m + 8) (n + 1)
    | .D9 t, m, n => go t (10 * m + 9) (n + 1)

private def positiveDecimal {α : Type} (zero : α) (fromParsed : Positive → Int → α)
    (xs ys : Decimal.uint) (exp : Decimal.signed_int) : α :=
  let (frac, digits) := fraction ys
  match xs.toNat, frac with
  | 0, 0 => zero
  | x+1, 0 => fromParsed ⟨x+1, by omega⟩ exp.toInt
  | 0, y+1 => fromParsed ⟨y+1, by omega⟩ (exp.toInt - digits)
  | x+1, y+1 => fromParsed ⟨(x+1) * 10^digits + (y+1), by omega⟩ (exp.toInt - digits)

private def zeroExponent : Decimal.signed_int := .Pos (.D0 .Nil)

def positive_decimal_decimal_signed_to_float32 :=
  positiveDecimal Floats.Float32.zero (Floats.Float32.from_parsed ⟨10, by decide⟩)

def positive_decimal_decimal_to_float32 (xs ys : Decimal.uint) : float32 :=
  positive_decimal_decimal_signed_to_float32 xs ys zeroExponent

def positive_decimal_decimal_signed_to_float :=
  positiveDecimal Floats.Float.zero (Floats.Float.from_parsed ⟨10, by decide⟩)

def positive_decimal_decimal_to_float (xs ys : Decimal.uint) : float :=
  positive_decimal_decimal_signed_to_float xs ys zeroExponent

def hexadecimal_uint_to_float32 (h : Hexadecimal.uint) : Option float32 :=
  float_to_float32 (Flocq.b64_of_bits h.toNat)

private def readSyntax {α : Type} (decimal : Decimal.uint → Decimal.uint → Decimal.signed_int → α)
    (neg : α → α) (hex : Hexadecimal.uint → Option α) : float_syntax → Option α
  | .FS_decimal (.Decimal x y) => some (signedDecimal x y zeroExponent)
  | .FS_decimal (.DecimalExp x y e) => some (signedDecimal x y e)
  | .FS_hex .FH_X h => hex h
  | .FS_hex _ _ => none
where
  signedDecimal : Decimal.signed_int → Decimal.uint → Decimal.signed_int → α
    | .Pos x, y, e => decimal x y e
    | .Neg x, y, e => neg (decimal x y e)

def float32_of_float_syntax :=
  readSyntax positive_decimal_decimal_signed_to_float32 Floats.Float32.neg hexadecimal_uint_to_float32

theorem hexadecimal_uint_to_bit_int_obligation_1 (b : Positive) (h : Hexadecimal.uint) :
    let z : Int := h.toNat
    (h.toNat : Int) < @Integers.modulus b → -1 < z ∧ z < @Integers.modulus b := by
  dsimp only
  omega

def hexadecimal_uint_to_bit_int {b : Positive} (h : Hexadecimal.uint) : Option (Integers.bit_int b) :=
  let z : Int := h.toNat
  if hz : z < @Integers.modulus b then
    some (Integers.mkint z (hexadecimal_uint_to_bit_int_obligation_1 b h hz))
  else none

def hexadecimal_uint_to_float (h : Hexadecimal.uint) : Option float :=
  (hexadecimal_uint_to_bit_int h).map Floats.Float.of_bits

def h : Hexadecimal.uint := .D3 (.D1 .Nil)

def float_of_float_syntax :=
  readSyntax positive_decimal_decimal_signed_to_float Floats.Float.neg hexadecimal_uint_to_float

example : float_of_float_syntax (.FS_decimal (.Decimal (.Neg (.D0 .Nil)) .Nil)) =
    some (.B754_zero true) := rfl
example : @hexadecimal_uint_to_bit_int ⟨4, by decide⟩ (.D1 (.D0 .Nil)) = none := by decide
example : fraction (.D0 (.D1 .Nil)) = (1, 2) := rfl

end Vellvm.Semantics.VellvmFloats
