/-
Flocq binary floating-point arithmetic, https://flocq.gitlabpages.inria.fr/
Copyright (C) 2010–2018 Sylvie Boldo and Guillaume Melquiond.
Distributed under the GNU Lesser General Public License, version 3 or later.
-/
import Vellvm.Numeric.Flocq.Normalize

namespace Vellvm.Numeric.Floats
open Flocq

variable {p e : Int} (hp : 0 < p) (he : p < e)

/-- A finite product is not rounded (and cannot overflow) before adding `z`. -/
def fusedNE (nan : (x y z : binary_float p e) → {v : binary_float p e // is_nan v = true})
    (x y z : binary_float p e) : binary_float p e :=
  let s := xor (Bsign x) (Bsign y)
  match x, y, z with
  | .B754_nan .., _, _ | _, .B754_nan .., _ | _, _, .B754_nan ..
  | .B754_infinity _, .B754_zero _, _ | .B754_zero _, .B754_infinity _, _ => (nan x y z).val
  | .B754_infinity _, _, .B754_infinity sz | _, .B754_infinity _, .B754_infinity sz =>
      if s = sz then z else (nan x y z).val
  | .B754_infinity _, _, _ | _, .B754_infinity _, _ => .B754_infinity s
  | _, _, .B754_infinity _ => z
  | .B754_zero _, _, .B754_zero sz | _, .B754_zero _, .B754_zero sz => .B754_zero (s && sz)
  | .B754_zero _, _, _ | _, .B754_zero _, _ => z
  | .B754_finite .., .B754_finite .., _ =>
      ofRat p e hp he .mode_NE (B2Q x * B2Q y + B2Q z) (s && Bsign z)

/-- Round the exact root to the nearest target grid point. Squared midpoints compare
    exactly using integers even when the root is irrational. -/
def sqrtNE (nan : ConvNaN p e p e) (x : binary_float p e) : binary_float p e :=
  match x with
  | .B754_zero _ | .B754_infinity false => x
  | .B754_nan .. | .B754_infinity true | .B754_finite true .. => (nan x).val
  | .B754_finite false m i _ =>
      let binade := ((m.val.log2 : Int) + i) / 2
      let j := max (binade + 1 - p) (emin p e)
      let k := i - 2 * j
      let a := m.val <<< k.toNat
      let b := 2 ^ (-k).toNat
      let r := Nat.sqrt (a / b)
      let m' := match compare (4 * a) (b * (2*r + 1)^2) with
        | .lt => r
        | .eq => r + r % 2
        | .gt => r + 1
      if h : 0 < m' then pack p e hp he .mode_NE false ⟨m', h⟩ j (le_max_right ..)
      else .B754_zero false

end Vellvm.Numeric.Floats
