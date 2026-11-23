/-
Flocq binary floating-point arithmetic, https://flocq.gitlabpages.inria.fr/
Copyright (C) 2010–2018 Sylvie Boldo and Guillaume Melquiond.
This library is free software; you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation; either version 3 of the License, or (at your option) any later version.
This library is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.

The exponent and bounded-mantissa equations are also in Rocq's SpecFloat:
Copyright INRIA, CNRS and contributors, The Rocq Development Team;
GNU Lesser General Public License version 2.1.
-/
module

public import Vellvm.Types
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Int.Bitwise
public import Mathlib.Data.Int.Log
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic

@[expose] public section

namespace Vellvm.Numeric.Flocq

abbrev Radix := { b : Int // 2 ≤ b }

def zpowNat (b i : Int) : Int := if i < 0 then 0 else b ^ i.toNat
abbrev pow2 := zpowNat 2

def log2 (x : Int) : Int := Nat.log 2 x.toNat
def log2up (x : Int) : Int := Nat.clog 2 x.toNat

def emin (p e : Int) := 3 - e - p
def FLT_exp (lower p i : Int) := max (i - p) lower
abbrev fexp (p e : Int) := FLT_exp (emin p e) p

def digits2_pos (m : Positive) : Positive := ⟨Nat.log 2 m.val + 1, Nat.succ_pos _⟩

def bounded (p e : Int) (m : Positive) (i : Int) : Bool :=
  decide (fexp p e ((digits2_pos m).val + i) = i ∧ i ≤ e - p)

def nan_pl (p : Int) (m : Positive) := decide (((digits2_pos m).val : Int) < p)

inductive full_float where
  | F754_zero (s : Bool)
  | F754_infinity (s : Bool)
  | F754_nan (s : Bool) (pl : Positive)
  | F754_finite (s : Bool) (m : Positive) (i : Int)
  deriving DecidableEq

inductive binary_float (prec emax : Int) where
  | B754_zero (s : Bool)
  | B754_infinity (s : Bool)
  | B754_nan (s : Bool) (pl : Positive) (valid : nan_pl prec pl = true)
  | B754_finite (s : Bool) (m : Positive) (i : Int) (valid : bounded prec emax m i = true)
  deriving DecidableEq

variable {p e : Int}

def B2FF : binary_float p e → full_float
  | .B754_zero s => .F754_zero s
  | .B754_infinity s => .F754_infinity s
  | .B754_nan s pl _ => .F754_nan s pl
  | .B754_finite s m i _ => .F754_finite s m i

def Bsign : binary_float p e → Bool
  | .B754_zero s | .B754_infinity s | .B754_nan s .. | .B754_finite s .. => s

def is_finite : binary_float p e → Bool
  | .B754_zero _ | .B754_finite .. => true
  | _ => false

def is_finite_strict : binary_float p e → Bool
  | .B754_finite .. => true
  | _ => false

def is_nan : binary_float p e → Bool
  | .B754_nan .. => true
  | _ => false

abbrev Nan₂ (p e : Int) := binary_float p e → binary_float p e → {x : binary_float p e // is_nan x = true}
abbrev ConvNaN (p e q f : Int) := binary_float p e → {x : binary_float q f // is_nan x = true}

section Field
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

def signed (s : Bool) (x : K) := if s then -x else x

def B2F : binary_float p e → K
  | .B754_finite s m i _ => signed s ((m.val : K) * (2 : K) ^ i)
  | _ => 0

def Ztrunc (x : K) : Int := if x < 0 then ⌈x⌉ else ⌊x⌋

def Znearest (choice : Int → Bool) (x : K) : Int :=
  let l := ⌊x⌋
  if x - l < 1 / 2 then l else if 1 / 2 < x - l then ⌈x⌉ else if choice l then ⌈x⌉ else l

def Zrnd_odd (x : K) : Int := if (⌊x⌋ : K) = x ∨ ⌊x⌋ % 2 = 1 then ⌊x⌋ else ⌈x⌉

inductive Mode where | mode_NE | mode_ZR | mode_DN | mode_UP | mode_NA deriving DecidableEq

def round_mode : Mode → K → Int
  | .mode_NE => Znearest (fun n ↦ decide (n % 2 ≠ 0))
  | .mode_ZR => Ztrunc
  | .mode_DN => Int.floor
  | .mode_UP => Int.ceil
  | .mode_NA => Znearest (fun n ↦ decide (0 ≤ n))

def cexp (ex : Int → Int) (x : K) := ex (Int.log 2 |x| + 1)

def round (ex : Int → Int) (rnd : K → Int) (x : K) : K :=
  let i := cexp ex x
  (rnd (x / (2 : K) ^ i) : K) * (2 : K) ^ i

end Field

noncomputable abbrev B2R (x : binary_float p e) : ℝ := B2F x
abbrev B2Q (x : binary_float p e) : ℚ := B2F x

noncomputable def generic_format (ex : Int → Int) (x : ℝ) := x = round ex Ztrunc x

def overflow_to_inf : Mode → Bool → Bool
  | .mode_NE, _ | .mode_NA, _ => true
  | .mode_ZR, _ => false
  | .mode_UP, s => !s
  | .mode_DN, s => s

def binary_overflow (p e : Int) (m : Mode) (s : Bool) : full_float :=
  if overflow_to_inf m s then .F754_infinity s else
    .F754_finite s ⟨max 1 (pow2 p - 1).toNat, by omega⟩ (e - p)

def shiftr (x i : Int) : Int := if i < 0 then x * pow2 (-i) else x / pow2 i
def shiftl (x i : Int) : Int := shiftr x (-i)
def testbit (x i : Int) : Bool := decide (0 ≤ i) && Int.testBit x i.toNat

end Vellvm.Numeric.Flocq
