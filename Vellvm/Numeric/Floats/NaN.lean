/-
The Compcert verified compiler. Xavier Leroy and Jacques-Henri Jourdan, INRIA Paris-Rocquencourt.
Copyright Institut National de Recherche en Informatique et en Automatique. All rights reserved.
Distributed under the GNU Lesser General Public License, version 2.1 or later, and also under
 the terms of the INRIA Non-Commercial License Agreement.
-/
import Vellvm.Numeric.Floats.Raw
import Vellvm.Numeric.IEEE754_extra

namespace Vellvm.Numeric.Floats
open Flocq

def is_float_representable_as_float32 : float → Bool
  | .B754_zero _ | .B754_infinity _ => true
  | .B754_nan _ p _ => p.val % 2^29 == 0
  | .B754_finite _ m i _ =>
      let e := i + 52
      decide (-149 ≤ e ∧ e ≤ 127) && m.val % 2^53 % 2^(max 29 (-97 - e)).toNat == 0

theorem integer_representable_n (n : Int) : -(2^53) ≤ n ∧ n ≤ 2^53 →
    IEEE754_extra.integer_representable 53 1024 n :=
  IEEE754_extra.integer_representable_n 53 1024 (by decide) (by decide) n

/-- Rocq `Z.to_pos`: zero and negative inputs give `xH`. -/
def toPositive (z : Int) : Positive := ⟨max 1 z.toNat, by omega⟩

theorem normalized_nan (prec : Int) (n : Nat) (p : Positive) (h : (n : Int) = prec - 1)
    (hp : 1 < prec) : nan_pl prec (toPositive (Zbits.P_mod_two_p p n)) = true := by
  have hn : n ≠ 0 := by omega
  have h₁ : 1 < (2 : Nat)^n := one_lt_pow₀ (by decide) hn
  have h₂ := Zbits.P_mod_two_p_range n p
  change 0 ≤ _ ∧ Zbits.P_mod_two_p p n < (↑(2^n : Nat) : Int) at h₂
  have h₃ : (toPositive (Zbits.P_mod_two_p p n)).val < 2^n := by
    change max 1 (Zbits.P_mod_two_p p n).toNat < 2^n
    omega
  have h₄ := Nat.log_lt_of_lt_pow (toPositive (Zbits.P_mod_two_p p n)).property.ne' h₃
  simp only [nan_pl, digits2_pos, decide_eq_true_eq, Nat.cast_add, Nat.cast_one]; omega

private def quietPayload (p : Positive) (n : Nat) :=
  let q : Positive := ⟨p.val ||| 2^(n-1), lt_of_lt_of_le p.property (Nat.left_le_or ..)⟩
  toPositive (Zbits.P_mod_two_p q n)

def quiet_nan_64_payload (p : Positive) := quietPayload p 52
def quiet_nan_32_payload (p : Positive) := quietPayload p 23

theorem quiet_nan_64_proof (p : Positive) : nan_pl 53 (quiet_nan_64_payload p) = true :=
  normalized_nan 53 52 _ rfl (by decide)

theorem quiet_nan_32_proof (p : Positive) : nan_pl 24 (quiet_nan_32_payload p) = true :=
  normalized_nan 24 23 _ rfl (by decide)

def quiet_nan_64 (sp : Bool × Positive) : {x : float // is_nan x = true} :=
  ⟨.B754_nan sp.1 (quiet_nan_64_payload sp.2) (quiet_nan_64_proof sp.2), rfl⟩

def quiet_nan_32 (sp : Bool × Positive) : {x : float32 // is_nan x = true} :=
  ⟨.B754_nan sp.1 (quiet_nan_32_payload sp.2) (quiet_nan_32_proof sp.2), rfl⟩

def default_nan_64 := quiet_nan_64 Archi.default_nan_64
def default_nan_32 := quiet_nan_32 Archi.default_nan_32

def narrow_nan_32_payload (p : Positive) :=
  toPositive (Zbits.P_mod_two_p (toPositive (p.val >>> 29 : Nat)) 23)

theorem narrow_nan_32_proof (p : Positive) : nan_pl 24 (narrow_nan_32_payload p) = true :=
  normalized_nan 24 23 _ rfl (by decide)

def narrow_nan_32 : ConvNaN 53 1024 24 128
  | .B754_nan s p _ => ⟨.B754_nan s (narrow_nan_32_payload p) (narrow_nan_32_proof p), rfl⟩
  | _ => default_nan_32

def float_to_float32 (f : float) : Option float32 :=
  if is_float_representable_as_float32 f then
    some (IEEE754_extra.Bconv 53 1024 24 128 (by decide) (by decide) narrow_nan_32 .mode_NE f)
  else none

namespace Float

private def expandPayload (p : Positive) (k : Nat) : Positive :=
  ⟨p.val * 2^k, Nat.mul_pos p.property (by positivity)⟩

private theorem expand_valid (p : Positive) (prec : Int) (k : Nat) (h : nan_pl prec p = true) :
    nan_pl (prec + k) (expandPayload p k) = true := by
  have shifted (n : Nat) : Nat.log 2 (p.val * 2^n) = Nat.log 2 p.val + n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ← Nat.mul_assoc, Nat.log_mul_base (by decide) (Nat.mul_ne_zero
        p.property.ne' (pow_ne_zero _ (by decide))), ih]
      omega
  change decide ((↑(Nat.log 2 p.val + 1) : Int) < prec) = true at h
  change decide ((↑(Nat.log 2 (p.val * 2^k) + 1) : Int) < prec + k) = true
  rw [shifted k]
  simp only [decide_eq_true_eq, Nat.cast_add, Nat.cast_one] at h ⊢
  omega

def expand_nan_payload (p : Positive) := expandPayload p 29

theorem expand_nan_proof (p : Positive) : nan_pl 24 p = true →
    nan_pl 53 (expand_nan_payload p) = true := expand_valid p 24 29

def expand_nan (s : Bool) (p : Positive) (h : nan_pl 24 p = true) : {x : float // is_nan x = true} :=
  ⟨.B754_nan s (expand_nan_payload p) (expand_nan_proof p h), rfl⟩

def of_single_nan : ConvNaN 24 128 53 1024
  | .B754_nan s p h => if Archi.float_of_single_preserves_sNaN then expand_nan s p h
      else quiet_nan_64 (s, expand_nan_payload p)
  | _ => default_nan_64

def reduce_nan_payload (p : Positive) := toPositive ((quiet_nan_64_payload p).val >>> 29 : Nat)

def to_single_nan : ConvNaN 53 1024 24 128
  | .B754_nan s p _ => quiet_nan_32 (s, reduce_nan_payload p)
  | _ => default_nan_32

end Float

private abbrev NanValue (p e : Int) := {x : binary_float p e // is_nan x = true}

private def signedNan {p e : Int} (sign : Bool → Bool) (fallback : NanValue p e) : ConvNaN p e p e
  | .B754_nan s pl h => ⟨.B754_nan (sign s) pl h, rfl⟩
  | _ => fallback

private def consPayload {p e : Int} (x : binary_float p e) (rest : List (Bool × Positive)) :=
  match x with | .B754_nan s pl _ => (s, pl) :: rest | _ => rest

private def fmaNan₁ {p e : Int} (choose : List (Bool × Positive) → Bool × Positive)
    (quiet : Bool × Positive → NanValue p e) (x y z : binary_float p e) :=
  let ((a, b), c) := Archi.fma_order x y z
  quiet (choose (consPayload a (consPayload b (consPayload c []))))

private def fmaNan {p e : Int} (d : Bool × Positive) (choose : List (Bool × Positive) → Bool × Positive)
    (quiet : Bool × Positive → NanValue p e) (x y z : binary_float p e) :=
  match x, y with
  | .B754_infinity _, .B754_zero _ | .B754_zero _, .B754_infinity _ =>
      if Archi.fma_invalid_mul_is_nan then quiet (choose (d :: consPayload z []))
      else fmaNan₁ choose quiet x y z
  | _, _ => fmaNan₁ choose quiet x y z

namespace Float

def neg_nan := signedNan (!·) default_nan_64
def abs_nan := signedNan (fun _ ↦ false) default_nan_64
def cons_pl := @consPayload 53 1024
def unop_nan (x : float) := quiet_nan_64 (Archi.choose_nan_64 (cons_pl x []))
def binop_nan (x y : float) := quiet_nan_64 (Archi.choose_nan_64 (cons_pl x (cons_pl y [])))
def fma_nan_1 := fmaNan₁ Archi.choose_nan_64 quiet_nan_64
def fma_nan := fmaNan Archi.default_nan_64 Archi.choose_nan_64 quiet_nan_64

end Float

namespace Float32

def neg_nan := signedNan (!·) default_nan_32
def abs_nan := signedNan (fun _ ↦ false) default_nan_32
def cons_pl := @consPayload 24 128
def unop_nan (x : float32) := quiet_nan_32 (Archi.choose_nan_32 (cons_pl x []))
def binop_nan (x y : float32) := quiet_nan_32 (Archi.choose_nan_32 (cons_pl x (cons_pl y [])))
def fma_nan_1 := fmaNan₁ Archi.choose_nan_32 quiet_nan_32
def fma_nan := fmaNan Archi.default_nan_32 Archi.choose_nan_32 quiet_nan_32

end Float32
end Vellvm.Numeric.Floats
