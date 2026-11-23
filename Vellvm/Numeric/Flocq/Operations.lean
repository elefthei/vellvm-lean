/-
Flocq binary floating-point arithmetic, https://flocq.gitlabpages.inria.fr/
Copyright (C) 2010–2018 Sylvie Boldo and Guillaume Melquiond.
GNU Lesser General Public License version 3 or (at your option) any later version.
Distributed without any warranty of merchantability or fitness for a particular purpose.
-/
import Vellvm.Numeric.Flocq.Normalize

namespace Vellvm.Numeric.Flocq

variable (p e : Int) (hp : 0 < p) (he : p < e) (nan : Nan₂ p e) (md : Mode)

def Bplus (x y : binary_float p e) : binary_float p e :=
  match x, y with
  | .B754_nan .., _ | _, .B754_nan .. => (nan x y).val
  | .B754_infinity a, .B754_infinity b => if a = b then x else (nan x y).val
  | .B754_infinity _, _ => x
  | _, .B754_infinity _ => y
  | .B754_zero a, .B754_zero b => .B754_zero (if a = b then a else decide (md = .mode_DN))
  | .B754_zero _, _ => y
  | _, .B754_zero _ => x
  | .B754_finite .., .B754_finite .. => ofRat p e hp he md (B2Q x + B2Q y) (decide (md = .mode_DN))

def neg {p e : Int} : binary_float p e → binary_float p e
  | .B754_zero s => .B754_zero (!s)
  | .B754_infinity s => .B754_infinity (!s)
  | .B754_nan s m h => .B754_nan (!s) m h
  | .B754_finite s m i h => .B754_finite (!s) m i h

def Bminus (x y : binary_float p e) : binary_float p e :=
  Bplus p e hp he (fun _ _ ↦ nan x y) md x (neg y)

def Bmult (x y : binary_float p e) : binary_float p e :=
  let s := xor (Bsign x) (Bsign y)
  match x, y with
  | .B754_nan .., _ | _, .B754_nan .. => (nan x y).val
  | .B754_infinity _, .B754_zero _ | .B754_zero _, .B754_infinity _ => (nan x y).val
  | .B754_infinity _, _ | _, .B754_infinity _ => .B754_infinity s
  | .B754_zero _, _ | _, .B754_zero _ => .B754_zero s
  | .B754_finite .., .B754_finite .. => ofRat p e hp he md (B2Q x * B2Q y) s

def Bdiv (x y : binary_float p e) : binary_float p e :=
  let s := xor (Bsign x) (Bsign y)
  match x, y with
  | .B754_nan .., _ | _, .B754_nan .. => (nan x y).val
  | .B754_infinity _, .B754_infinity _ | .B754_zero _, .B754_zero _ => (nan x y).val
  | .B754_infinity _, _ | _, .B754_zero _ => .B754_infinity s
  | _, .B754_infinity _ | .B754_zero _, _ => .B754_zero s
  | .B754_finite .., .B754_finite .. => ofRat p e hp he md (B2Q x / B2Q y) s

def Bcompare {p e : Int} (x y : binary_float p e) : Option Ordering :=
  match x, y with
  | .B754_nan .., _ | _, .B754_nan .. => none
  | .B754_infinity a, .B754_infinity b => some (compare b a)
  | .B754_infinity s, _ => some (if s then .lt else .gt)
  | _, .B754_infinity s => some (if s then .gt else .lt)
  | _, _ => some (compare (B2Q x) (B2Q y))

end Vellvm.Numeric.Flocq
