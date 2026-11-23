/-
The Compcert verified compiler
Xavier Leroy, INRIA Paris-Rocquencourt

Copyright Institut National de Recherche en Informatique et en Automatique.
All rights reserved. This file is distributed under the terms of the GNU Lesser
General Public License as published by the Free Software Foundation, either
version 2.1 of the License, or (at your option) any later version.
This file is also distributed under the terms of the INRIA Non-Commercial
License Agreement.
-/
module

public import Vellvm.Numeric.Zbits
public import Vellvm.Numeric.Archi
public import Init.Data.BitVec.Lemmas
import Mathlib.Tactic.Ring

@[expose] public section
namespace Vellvm.Numeric.Integers
open Vellvm.Numeric.Rocqlib

inductive comparison where
  | Ceq | Cne | Clt | Cle | Cgt | Cge
  deriving DecidableEq, Repr
export comparison (Ceq Cne Clt Cle Cgt Cge)

universe u
def comparison_rect (P : comparison → Sort u) (e : P Ceq) (n : P Cne)
    (l : P Clt) (le : P Cle) (g : P Cgt) (ge : P Cge) (c : comparison) : P c :=
  match c with | Ceq => e | Cne => n | Clt => l | Cle => le | Cgt => g | Cge => ge
abbrev comparison_ind := comparison_rect.{0}
abbrev comparison_rec := comparison_rect.{1}
abbrev comparison_sind := comparison_rect.{0}

def negate_comparison : comparison → comparison
  | Ceq => Cne | Cne => Ceq | Clt => Cge | Cle => Cgt | Cgt => Cle | Cge => Clt

def swap_comparison : comparison → comparison
  | Ceq => Ceq | Cne => Cne | Clt => Cgt | Cle => Cge | Cgt => Clt | Cge => Cle

structure WORDSIZE where
  wordsize : Nat
  wordsize_not_zero : wordsize ≠ 0

def WORDSIZE.ofPositive (w : Positive) : WORDSIZE := ⟨w.val, Nat.ne_of_gt w.property⟩

-- Positive widths already have a binary Nat projection in Lean; no unary conversion is needed.
abbrev pos_to_nat_memo (w : Positive) := w.val
def two_power_pos_memo (w : Positive) : Int :=
  match w.val with
  | 1 => 2 | 8 => 256 | 16 => 65536 | 32 => 4294967296 | 64 => 18446744073709551616
  | 128 => 340282366920938463463374607431768211456 | _ => two_power_pos w

def half_two_power_pos_memo (w : Positive) :=
  match w.val with
  | 1 => 1 | 8 => 128 | 16 => 32768 | 32 => 2147483648 | 64 => 9223372036854775808
  | 128 => 170141183460469231731687303715884105728 | _ => (two_power_pos w).fdiv 2

theorem pos_to_nat_memo_eq (w : Positive) : pos_to_nat_memo w = w.val := rfl
theorem two_power_pos_memo_eq (w : Positive) : two_power_pos_memo w = two_power_pos w := by
  unfold two_power_pos_memo two_power_pos
  split <;> simp_all [two_power_nat]
theorem half_two_power_pos_memo_eq (w : Positive) :
    half_two_power_pos_memo w = (two_power_pos w).fdiv 2 := by
  unfold half_two_power_pos_memo two_power_pos <;> split <;> simp_all [two_power_nat]

variable {w : Positive}
abbrev zwordsize {w : Positive} := Int.ofNat w.val
abbrev natwordsize {w : Positive} := pos_to_nat_memo w
def modulus {w : Positive} := two_power_pos_memo w
def half_modulus {w : Positive} := half_two_power_pos_memo w
abbrev max_unsigned {w : Positive} := @modulus w - 1
abbrev max_signed {w : Positive} := @half_modulus w - 1
abbrev min_signed {w : Positive} := - @half_modulus w

theorem natwordsize_def : @natwordsize w = w.val := rfl
theorem modulus_def : @modulus w = two_power_pos w := two_power_pos_memo_eq w
theorem half_modulus_def : @half_modulus w = (@modulus w).fdiv 2 := by
  rw [modulus_def, half_modulus, half_two_power_pos_memo_eq]
theorem modulus_two_power_nat : @modulus w = two_power_nat (@natwordsize w) := modulus_def
theorem wordsize_pos : @zwordsize w > 0 := Int.ofNat_lt.mpr w.property
theorem modulus_power : @modulus w = two_p (@zwordsize w) := modulus_def
theorem modulus_pos : @modulus w > 0 := modulus_def.symm ▸ two_power_nat_pos w.val

structure bit_int (w : Positive) where
  ofBits :: bits : BitVec w.val
  deriving DecidableEq, Repr, Inhabited

theorem bit_int.ext_bits {x y : bit_int w} (h : x.bits = y.bits) : x = y := by
  cases x; cases y; cases h; rfl

def intval (x : bit_int w) := Int.ofNat x.bits.toNat
theorem intrange (x : bit_int w) : -1 < intval x ∧ intval x < @modulus w := by
  rw [modulus_def]
  exact ⟨lt_of_lt_of_le (by decide : (-1 : Int) < 0) (Int.natCast_nonneg _),
    Int.ofNat_lt.mpr x.bits.isLt⟩

def mkint (i : Int) (_h : -1 < i ∧ i < @modulus w) : bit_int w := ⟨BitVec.ofInt w.val i⟩

abbrev P_mod_two_p := Zbits.P_mod_two_p
def Z_mod_modulus {w : Positive} (x : Int) := Zbits.Z_mod_two_p x w.val

theorem P_mod_two_p_range : ∀ n p, 0 ≤ P_mod_two_p p n ∧ P_mod_two_p p n < two_power_nat n := Zbits.P_mod_two_p_range
theorem P_mod_two_p_eq : ∀ n p, P_mod_two_p p n = (Int.ofNat p.val).fmod (two_power_nat n) := Zbits.P_mod_two_p_eq
theorem Z_mod_modulus_range (x : Int) : 0 ≤ @Z_mod_modulus w x ∧ @Z_mod_modulus w x < @modulus w := by
  rw [modulus_def]; exact Zbits.Z_mod_two_p_range _ _
theorem Z_mod_modulus_range' (x : Int) : -1 < @Z_mod_modulus w x ∧ @Z_mod_modulus w x < @modulus w := by
  have := @Z_mod_modulus_range w x; omega
theorem Z_mod_modulus_eq (x : Int) : @Z_mod_modulus w x = x.fmod (@modulus w) := by
  rw [modulus_def]; exact Zbits.Z_mod_two_p_eq _ _

def unsigned (x : bit_int w) := intval x
def signed (x : bit_int w) :=
  if unsigned x < @half_modulus w then unsigned x else unsigned x - @modulus w

def repr (x : Int) : bit_int w := ⟨BitVec.ofInt w.val x⟩
def zero : bit_int w := repr 0
def one : bit_int w := repr 1
def mone : bit_int w := repr (-1)
def iwordsize : bit_int w := repr (@zwordsize w)

theorem mkint_eq (x y : Int) (Px Py) (h : x = y) : @mkint w x Px = mkint y Py := by subst y; rfl
def eq_dec (x y : bit_int w) : PSum (x = y) (x ≠ y) := decideSum (x = y)

def eq (x y : bit_int w) := decide (x = y)
def lt (x y : bit_int w) := decide (signed x < signed y)
def ltu (x y : bit_int w) := decide (unsigned x < unsigned y)
def neg (x : bit_int w) : bit_int w := repr (-unsigned x)
def add (x y : bit_int w) : bit_int w := repr (unsigned x + unsigned y)
def sub (x y : bit_int w) : bit_int w := repr (unsigned x - unsigned y)
def mul (x y : bit_int w) : bit_int w := repr (unsigned x * unsigned y)
def divs (x y : bit_int w) : bit_int w := repr ((signed x).tdiv (signed y))
def mods (x y : bit_int w) : bit_int w := repr ((signed x).tmod (signed y))
def divu (x y : bit_int w) : bit_int w := repr ((unsigned x).fdiv (unsigned y))
def modu (x y : bit_int w) : bit_int w := repr ((unsigned x).fmod (unsigned y))

def and (x y : bit_int w) : bit_int w := ⟨x.bits &&& y.bits⟩
def or (x y : bit_int w) : bit_int w := ⟨x.bits ||| y.bits⟩
def xor (x y : bit_int w) : bit_int w := ⟨x.bits ^^^ y.bits⟩
def not (x : bit_int w) : bit_int w := ⟨~~~x.bits⟩
def shl (x y : bit_int w) : bit_int w := ⟨x.bits <<< y.bits.toNat⟩

-- BitVec shifts an unbounded Nat before truncating it. Avoid that allocation on overshifts.
def shlBounded (x y : bit_int w) : bit_int w :=
  if y.bits.toNat < w.val then ⟨x.bits <<< y.bits.toNat⟩ else ⟨0#(w.val)⟩

@[csimp] theorem shl_eq_bounded : @shl = @shlBounded := by
  funext w x y
  unfold shl shlBounded
  split <;> rename_i h
  · rfl
  · rw [BitVec.shiftLeft_eq_zero (Nat.le_of_not_lt h)]

def shru (x y : bit_int w) : bit_int w := ⟨x.bits >>> y.bits.toNat⟩
def shr (x y : bit_int w) : bit_int w := ⟨x.bits.sshiftRight y.bits.toNat⟩
def rol (x y : bit_int w) : bit_int w := ⟨x.bits.rotateLeft y.bits.toNat⟩
def ror (x y : bit_int w) : bit_int w := ⟨x.bits.rotateRight y.bits.toNat⟩
def rolm (x a m : bit_int w) := and (rol x a) m
def shrx (x y : bit_int w) := divs x (shl one y)
def mulhu (x y : bit_int w) : bit_int w := repr ((unsigned x * unsigned y).fdiv (@modulus w))
def mulhs (x y : bit_int w) : bit_int w := repr ((signed x * signed y).fdiv (@modulus w))

def negative (x : bit_int w) : bit_int w := if lt x zero then one else zero
def add_carry (x y cin : bit_int w) : bit_int w :=
  if unsigned x + unsigned y + unsigned cin < @modulus w then zero else one
def add_overflow (x y cin : bit_int w) : bit_int w :=
  let s := signed x + signed y + signed cin
  if @min_signed w ≤ s ∧ s ≤ @max_signed w then zero else one
def sub_borrow (x y bin : bit_int w) : bit_int w :=
  if unsigned x - unsigned y - unsigned bin < 0 then one else zero
def sub_overflow (x y bin : bit_int w) : bit_int w :=
  let s := signed x - signed y - signed bin
  if @min_signed w ≤ s ∧ s ≤ @max_signed w then zero else one
def shr_carry (x y : bit_int w) : bit_int w :=
  if lt x zero && !eq (and x (sub (shl one y) one)) zero then one else zero

abbrev Zshiftin := Zbits.Zshiftin
abbrev Zzero_ext := Zbits.Zzero_ext
abbrev Zsign_ext := Zbits.Zsign_ext
def zero_ext (n : Int) (x : bit_int w) : bit_int w := repr (Zzero_ext n (unsigned x))
def sign_ext (n : Int) (x : bit_int w) : bit_int w := repr (Zsign_ext n (unsigned x))
abbrev Z_one_bits := Zbits.Z_one_bits
def one_bits (x : bit_int w) : List (bit_int w) := (Z_one_bits w.val (unsigned x) 0).map repr
def is_power2 (x : bit_int w) : Option (bit_int w) :=
  match Z_one_bits w.val (unsigned x) 0 with
  | [i] => some (repr i)
  | _ => none

def cmp (c : comparison) (x y : bit_int w) :=
  match c with
  | Ceq => eq x y | Cne => !eq x y | Clt => lt x y | Cle => !lt y x
  | Cgt => lt y x | Cge => !lt x y

def cmpu (c : comparison) (x y : bit_int w) :=
  match c with
  | Ceq => eq x y | Cne => !eq x y | Clt => ltu x y | Cle => !ltu y x
  | Cgt => ltu y x | Cge => !ltu x y

def is_false (x : bit_int w) := x = zero
def is_true (x : bit_int w) := x ≠ zero
def notbool (x : bit_int w) : bit_int w := if eq x zero then one else zero

def divmodu2 (nhi nlo d : bit_int w) : Option (bit_int w × bit_int w) :=
  if d = zero then none else
    let n := unsigned nhi * @modulus w + unsigned nlo
    let q := n.fdiv (unsigned d)
    if q ≤ @max_unsigned w then some (repr q, repr (n.fmod (unsigned d))) else none

def divmods2 (nhi nlo d : bit_int w) : Option (bit_int w × bit_int w) :=
  if d = zero then none else
    let n := signed nhi * @modulus w + unsigned nlo
    let q := n.tdiv (signed d)
    if @min_signed w ≤ q ∧ q ≤ @max_signed w then some (repr q, repr (n.tmod (signed d))) else none

abbrev eqmod := Zbits.eqmod
abbrev eqm {w : Positive} := eqmod (@modulus w)
def testbit (x : bit_int w) (i : Int) := Zbits.testbit (unsigned x) i
abbrev powerserie := Zbits.powerserie
def int_of_one_bits : List (bit_int w) → bit_int w
  | [] => zero
  | a :: as => add (shl one a) (int_of_one_bits as)

def no_overlap (ofs1 : bit_int w) (sz1 : Int) (ofs2 : bit_int w) (sz2 : Int) :=
  let x := unsigned ofs1; let y := unsigned ofs2
  decide (x + sz1 < @modulus w) && decide (y + sz2 < @modulus w) &&
    (decide (x + sz1 ≤ y) || decide (y + sz2 ≤ x))

abbrev Zsize := Zbits.Zsize
def size (x : bit_int w) := Zsize (unsigned x)
abbrev w32 : Positive := ⟨32, by decide⟩
abbrev w64 : Positive := ⟨64, by decide⟩
def loword (n : bit_int w64) : bit_int w32 := repr (unsigned n)
def hiword (n : bit_int w64) : bit_int w32 := repr (unsigned (shru n (repr 32)))
def ofwords (hi lo : bit_int w32) : bit_int w64 :=
  or (shl (repr (unsigned hi)) (repr 32)) (repr (unsigned lo))

theorem half_modulus_power : @half_modulus w = two_p (@zwordsize w - 1) := by
  rw [half_modulus_def, modulus_def]
  rcases w with ⟨_ | n, hw⟩
  · omega
  · change (Int.ofNat (2^(n+1))).fdiv 2 = two_p ((n+1 : Nat) - (1 : Int))
    rw [show ((n+1 : Nat) : Int) - 1 = Int.ofNat n by simp]
    simp [two_p, two_power_nat, Nat.pow_succ, Int.fdiv_eq_ediv_of_nonneg]

theorem half_modulus_modulus : @modulus w = 2 * @half_modulus w := by
  rw [half_modulus_power, modulus_def]
  rcases w with ⟨_ | n, hw⟩
  · omega
  · change Int.ofNat (2^(n+1)) = 2 * two_p (((n+1 : Nat) : Int) - 1)
    rw [show ((n+1 : Nat) : Int) - 1 = Int.ofNat n by simp]
    simp [two_p, two_power_nat, Nat.pow_succ, mul_comm]

theorem half_modulus_pos : @half_modulus w > 0 := by
  have := @half_modulus_modulus w; have := @modulus_pos w; omega
theorem min_signed_neg : @min_signed w < 0 := neg_lt_zero.mpr half_modulus_pos
theorem max_signed_pos : @max_signed w ≥ 0 := by
  have := @half_modulus_pos w; unfold max_signed; omega
theorem wordsize_max_unsigned : @zwordsize w ≤ @max_unsigned w := by
  have h := two_p_strict _ (@wordsize_pos w).le
  unfold max_unsigned; rw [modulus_power]; omega
theorem two_wordsize_max_unsigned : 2 * @zwordsize w - 1 ≤ @max_unsigned w := by
  have h := two_p_strict_2 _ (@wordsize_pos w).le
  unfold max_unsigned; rw [modulus_power]; omega
theorem max_signed_unsigned : @max_signed w < @max_unsigned w := by
  have := @half_modulus_modulus w; have := @half_modulus_pos w
  unfold max_signed max_unsigned; omega

theorem unsigned_repr_eq (x : Int) : unsigned (@repr w x) = x.fmod (@modulus w) := by
  rw [modulus_def, Int.fmod_eq_emod_of_nonneg _ (two_power_nat_pos _).le]
  exact Int.toNat_of_nonneg (Int.emod_nonneg _ (two_power_nat_pos w.val).ne')

theorem signed_repr_eq (x : Int) : signed (@repr w x) =
    chooseSide (zlt (x.fmod (@modulus w)) (@half_modulus w)) (x.fmod (@modulus w))
      (x.fmod (@modulus w) - @modulus w) := by
  unfold signed
  rw [unsigned_repr_eq]
  unfold zlt; split <;> rfl

theorem eqmod_refl : ∀ m x, eqmod m x x := Zbits.eqmod_refl
theorem eqmod_refl2 : ∀ m x y, x = y → eqmod m x y := Zbits.eqmod_refl2
theorem eqmod_sym : ∀ m x y, eqmod m x y → eqmod m y x := Zbits.eqmod_sym
theorem eqmod_trans : ∀ m x y z, eqmod m x y → eqmod m y z → eqmod m x z := Zbits.eqmod_trans
theorem eqmod_small_eq : ∀ m x y, eqmod m x y → 0 ≤ x ∧ x < m → 0 ≤ y ∧ y < m → x = y :=
  Zbits.eqmod_small_eq
theorem eqmod_mod_eq : ∀ m : Int, m > 0 → ∀ x y, eqmod m x y → x.fmod m = y.fmod m :=
  Zbits.eqmod_mod_eq
theorem eqmod_mod : ∀ m x, eqmod m x (x.fmod m) := Zbits.eqmod_mod
theorem eqmod_add : ∀ m a b c d, eqmod m a b → eqmod m c d → eqmod m (a+c) (b+d) := Zbits.eqmod_add
theorem eqmod_neg : ∀ m x y, eqmod m x y → eqmod m (-x) (-y) := Zbits.eqmod_neg
theorem eqmod_sub : ∀ m a b c d, eqmod m a b → eqmod m c d → eqmod m (a-c) (b-d) := Zbits.eqmod_sub
theorem eqmod_mult : ∀ m a b c d, eqmod m a c → eqmod m b d → eqmod m (a*b) (c*d) := Zbits.eqmod_mult
theorem eqmod_divides : ∀ n m x y, eqmod n x y → m ∣ n → eqmod m x y := Zbits.eqmod_divides

theorem eqm_refl : ∀ x, @eqm w x x := eqmod_refl _
theorem eqm_refl2 : ∀ x y, x = y → @eqm w x y := eqmod_refl2 _
theorem eqm_sym : ∀ x y, @eqm w x y → @eqm w y x := eqmod_sym _
theorem eqm_trans : ∀ x y z, @eqm w x y → @eqm w y z → @eqm w x z := eqmod_trans _
theorem eqm_small_eq : ∀ x y, @eqm w x y → 0 ≤ x ∧ x < @modulus w →
    0 ≤ y ∧ y < @modulus w → x = y := eqmod_small_eq _
theorem eqm_add : ∀ a b c d, @eqm w a b → @eqm w c d → @eqm w (a+c) (b+d) := eqmod_add _
theorem eqm_neg : ∀ x y, @eqm w x y → @eqm w (-x) (-y) := eqmod_neg _
theorem eqm_sub : ∀ a b c d, @eqm w a b → @eqm w c d → @eqm w (a-c) (b-d) := eqmod_sub _
theorem eqm_mult : ∀ a b c d, @eqm w a c → @eqm w b d → @eqm w (a*b) (c*d) := eqmod_mult _

theorem bit_int.ext_unsigned {x y : bit_int w} (e : unsigned x = unsigned y) : x = y :=
  bit_int.ext_bits (BitVec.eq_of_toNat_eq (Int.ofNat_inj.mp e))

theorem eqm_samerepr (x y : Int) (h : @eqm w x y) : @repr w x = repr y := by
  apply bit_int.ext_unsigned; rw [unsigned_repr_eq, unsigned_repr_eq]
  exact eqmod_mod_eq _ modulus_pos _ _ h
theorem eqm_unsigned_repr (z : Int) : @eqm w z (unsigned (@repr w z)) := by
  rw [unsigned_repr_eq]; exact eqmod_mod _ _
theorem eqm_unsigned_repr_l (a b : Int) (h : @eqm w a b) : @eqm w (unsigned (@repr w a)) b :=
  eqm_trans _ _ _ (eqm_sym _ _ (eqm_unsigned_repr _)) h
theorem eqm_unsigned_repr_r (a b : Int) (h : @eqm w a b) : @eqm w a (unsigned (@repr w b)) :=
  eqm_trans _ _ _ h (eqm_unsigned_repr _)
theorem eqm_signed_unsigned (x : bit_int w) : @eqm w (signed x) (unsigned x) := by
  unfold signed; split
  · apply eqm_refl
  · exact ⟨-1, by ring⟩

theorem unsigned_range (i : bit_int w) : 0 ≤ unsigned i ∧ unsigned i < @modulus w :=
  ⟨Int.natCast_nonneg _, (intrange i).2⟩
theorem unsigned_range_2 (i : bit_int w) : 0 ≤ unsigned i ∧ unsigned i ≤ @max_unsigned w := by
  have := unsigned_range i; unfold max_unsigned; omega
theorem signed_range (i : bit_int w) : @min_signed w ≤ signed i ∧ signed i ≤ @max_signed w := by
  have := unsigned_range i; have := @half_modulus_modulus w; have := @half_modulus_pos w
  unfold signed min_signed max_signed; split <;> omega
theorem repr_unsigned (i : bit_int w) : repr (unsigned i) = i := by
  apply bit_int.ext_unsigned
  rw [unsigned_repr_eq, Zmod_small _ _ (unsigned_range i)]
theorem repr_signed (i : bit_int w) : repr (signed i) = i :=
  (eqm_samerepr _ _ (eqm_signed_unsigned i)).trans (repr_unsigned i)
theorem eqm_repr_eq (x : Int) (y : bit_int w) (h : @eqm w x (unsigned y)) : repr x = y :=
  (eqm_samerepr _ _ h).trans (repr_unsigned y)

theorem unsigned_repr (z : Int) (h : 0 ≤ z ∧ z ≤ @max_unsigned w) : unsigned (@repr w z) = z := by
  unfold max_unsigned at h; rw [unsigned_repr_eq]; apply Zmod_small; omega

@[simp] theorem intval_mkint (i : Int) (hi : -1 < i ∧ i < @modulus w) : intval (mkint i hi) = i := by
  change unsigned (@repr w i) = i
  apply unsigned_repr
  unfold max_unsigned; omega

@[simp] theorem mkint_intval (x : bit_int w) : mkint (intval x) (intrange x) = x :=
  repr_unsigned x

theorem signed_eq_toInt (x : bit_int w) : signed x = x.bits.toInt := by
  have hm := @half_modulus_modulus w
  rw [modulus_def] at hm
  unfold signed BitVec.toInt unsigned intval
  rw [modulus_def]; change Int.ofNat (2^w.val) = 2 * @half_modulus w at hm
  simp only [Int.ofNat_eq_natCast] at hm ⊢
  split <;> split <;> first | rfl | omega

theorem signed_repr (z : Int) (h : @min_signed w ≤ z ∧ z ≤ @max_signed w) : signed (@repr w z) = z := by
  have := @half_modulus_modulus w; have := @half_modulus_pos w
  unfold min_signed max_signed at h
  unfold signed
  by_cases hz : 0 ≤ z
  · rw [unsigned_repr z (by unfold max_unsigned; omega), if_pos (by omega)]
  · have hu : unsigned (@repr w z) = z + @modulus w := by
      rw [unsigned_repr_eq]
      apply Zmod_unique _ _ (-1) _ <;> omega
    rw [hu, if_neg (by omega)]; omega
theorem signed_eq_unsigned (x : bit_int w) (h : unsigned x ≤ @max_signed w) : signed x = unsigned x := by
  unfold max_signed at h; unfold signed; rw [if_pos (by omega)]
theorem signed_positive (x : bit_int w) : signed x ≥ 0 ↔ unsigned x ≤ @max_signed w := by
  have := unsigned_range x
  unfold signed max_signed; split <;> omega
theorem unsigned_zero : unsigned (@zero w) = 0 := unsigned_repr _ ⟨by decide, by
  have := @modulus_pos w; unfold max_unsigned; omega⟩
theorem unsigned_one : unsigned (@one w) = 1 := unsigned_repr _ ⟨by decide, by
  have := @half_modulus_modulus w; have := @half_modulus_pos w; unfold max_unsigned; omega⟩
theorem unsigned_mone : unsigned (@mone w) = @modulus w - 1 := by
  rw [mone, unsigned_repr_eq]; have := @modulus_pos w
  apply Zmod_unique _ _ (-1) _ <;> omega
theorem signed_zero : signed (@zero w) = 0 := by
  rw [signed, unsigned_zero, if_pos half_modulus_pos]
theorem signed_one (h : @zwordsize w > 1) : signed (@one w) = 1 := by
  rw [signed, unsigned_one, if_pos]
  rw [half_modulus_power]; exact two_p_monotone_strict 0 _ (by omega)
theorem signed_mone : signed (@mone w) = -1 := by
  have := @half_modulus_modulus w; have := @half_modulus_pos w
  rw [signed, unsigned_mone, if_neg (by omega)]; omega
theorem one_not_zero : @one w ≠ zero := by
  intro e; have he := congrArg unsigned e; rw [unsigned_one, unsigned_zero] at he; omega
theorem unsigned_repr_wordsize : unsigned (@iwordsize w) = @zwordsize w :=
  unsigned_repr _ ⟨wordsize_pos.le, wordsize_max_unsigned⟩

theorem eq_sym (x y : bit_int w) : eq x y = eq y x := by simp [eq, eq_comm]
theorem eq_spec (x y : bit_int w) : if eq x y then x = y else x ≠ y := by
  by_cases h : x = y <;> simp [eq, h]
theorem eq_true (x : bit_int w) : eq x x = true := by simp [eq]
theorem eq_false (x y : bit_int w) (h : x ≠ y) : eq x y = false := by simp [eq, h]
theorem eq_signed (x y : bit_int w) :
    eq x y = chooseSide (zeq (signed x) (signed y)) true false := by
  by_cases h : x = y
  · subst y; simp [eq, zeq, decideSum, chooseSide]
  · have hs : signed x ≠ signed y := fun e ↦ h ((repr_signed x).symm.trans
        ((congrArg (@repr w) e).trans (repr_signed y)))
    simp [eq, h, zeq, decideSum, chooseSide, hs]

end Vellvm.Numeric.Integers
