module

public import Vellvm.Numeric.Integers.Basic
public import Vellvm.Semantics.EOU
public import Vellvm.Syntax.DynamicTypes
public import Mathlib.Data.Int.Bitwise

@[expose] public section
namespace Vellvm.Semantics.VellvmIntegers
open Numeric Syntax.DynamicTypes EOU

class VMemInt (I : Type u) where
  Build_VMemInt ::
  mequ : I → I → Bool
  mcmp : Integers.comparison → I → I → Bool
  mcmpu : Integers.comparison → I → I → Bool
  msamesign : I → I → Bool
  mbitwidth : Option Positive
  mzero : I
  mone : I
  madd : I → I → EOU I
  madd_carry : I → I → I → I
  madd_overflow : I → I → I → I
  msub : I → I → EOU I
  msub_borrow : I → I → I → I
  msub_overflow : I → I → I → I
  mmul : I → I → EOU I
  mdivu : I → I → I
  mdivs : I → I → EOU I
  mmodu : I → I → I
  mmods : I → I → EOU I
  mshl : I → I → EOU I
  mshr : I → I → I
  mshru : I → I → I
  mnegative : I → EOU I
  mand : I → I → I
  mor : I → I → I
  mxor : I → I → I
  mmin_signed : Option Int
  mmax_signed : Option Int
  mmax_unsigned : Option Int
  munsigned : I → Int
  msigned : I → Int
  mrepr : Int → EOU I
  mdtyp_of_int : dtyp_base

export VMemInt (Build_VMemInt mequ mcmp mcmpu msamesign mbitwidth mzero mone madd madd_carry
  madd_overflow msub msub_borrow msub_overflow mmul mdivu mdivs mmodu mmods mshl mshr mshru
  mnegative mand mor mxor mmin_signed mmax_signed mmax_unsigned munsigned msigned mrepr mdtyp_of_int)

def mequ_Z (x y : Int) : Bool := x == y

def mcmp_Z (c : Integers.comparison) (x y : Int) : Bool :=
  match c with
  | .Ceq => x == y
  | .Cne => x != y
  | .Clt => decide (x < y)
  | .Cle => decide (x ≤ y)
  | .Cgt => decide (x > y)
  | .Cge => decide (x ≥ y)

def mcmpu_Z := mcmp_Z

def msamesign_Z (x y : Int) : Bool := decide (x < 0) == decide (y < 0)

instance VMemInt_Z : VMemInt Int where
  mequ := mequ_Z
  mcmp := mcmp_Z
  mcmpu := mcmpu_Z
  msamesign := msamesign_Z
  mbitwidth := none
  mzero := 0
  mone := 1
  madd x y := raise_ret (x + y)
  madd_carry _ _ _ := 0
  madd_overflow _ _ _ := 0
  msub x y := raise_ret (x - y)
  msub_borrow _ _ _ := 0
  msub_overflow _ _ _ := 0
  mmul x y := raise_ret (x * y)
  mdivu := Int.fdiv
  mdivs x y := raise_ret (x.fdiv y)
  mmodu := Int.fmod
  mmods x y := raise_ret (x.fmod y)
  mshl x y := raise_ret (x <<< y)
  mshr x y := x >>> y
  mshru x y := x >>> y
  mnegative x := raise_ret (-x)
  mand := Int.land
  mor := Int.lor
  mxor := Int.xor
  mmin_signed := none
  mmax_signed := none
  mmax_unsigned := none
  munsigned := id
  msigned := id
  mrepr := raise_ret
  mdtyp_of_int := DTYPE_Iptr

abbrev int1 := Integers.bit_int ⟨1, by decide⟩
abbrev int8 := Integers.bit_int ⟨8, by decide⟩
abbrev int16 := Integers.bit_int ⟨16, by decide⟩
abbrev int32 := Integers.bit_int Integers.w32
abbrev int64 := Integers.bit_int Integers.w64

class VInt (I : Type u) where
  Build_VInt ::
  equ : I → I → Bool
  cmp : Integers.comparison → I → I → Bool
  cmpu : Integers.comparison → I → I → Bool
  samesign : I → I → Bool
  bitwidth : Positive
  zero : I
  one : I
  add : I → I → I
  add_carry : I → I → I → I
  add_overflow : I → I → I → I
  sub : I → I → I
  sub_borrow : I → I → I → I
  sub_overflow : I → I → I → I
  mul : I → I → I
  divu : I → I → I
  divs : I → I → I
  modu : I → I → I
  mods : I → I → I
  shl : I → I → I
  shr : I → I → I
  shru : I → I → I
  negative : I → I
  and : I → I → I
  or : I → I → I
  xor : I → I → I
  min_signed : Int
  max_signed : Int
  max_unsigned : Int
  unsigned : I → Int
  signed : I → Int
  repr : Int → I

export VInt (Build_VInt equ cmp cmpu samesign bitwidth zero one add add_carry add_overflow sub
  sub_borrow sub_overflow mul divu divs modu mods shl shr shru negative and or xor min_signed
  max_signed max_unsigned unsigned signed repr)

instance VInt_Bounded (sz : Positive) : VInt (Integers.bit_int sz) where
  equ := Integers.eq
  cmp := Integers.cmp
  cmpu := Integers.cmpu
  samesign x y := Integers.cmp .Clt x Integers.zero == Integers.cmp .Clt y Integers.zero
  bitwidth := sz
  zero := Integers.zero
  one := Integers.one
  add := Integers.add
  add_carry := Integers.add_carry
  add_overflow := Integers.add_overflow
  sub := Integers.sub
  sub_borrow := Integers.sub_borrow
  sub_overflow := Integers.sub_overflow
  mul := Integers.mul
  divu := Integers.divu
  divs := Integers.divs
  modu := Integers.modu
  mods := Integers.mods
  shl := Integers.shl
  shr := Integers.shr
  shru := Integers.shru
  negative := Integers.negative
  and := Integers.and
  or := Integers.or
  xor := Integers.xor
  min_signed := @Integers.min_signed sz
  max_signed := @Integers.max_signed sz
  max_unsigned := @Integers.max_unsigned sz
  unsigned := Integers.unsigned
  signed := Integers.signed
  repr := Integers.repr

instance VIntVMemInt {I : Type u} [v : VInt I] : VMemInt I where
  mequ := v.equ
  mcmp := v.cmp
  mcmpu := v.cmpu
  msamesign := v.samesign
  mbitwidth := some v.bitwidth
  mzero := v.zero
  mone := v.one
  madd x y := raise_ret (v.add x y)
  madd_carry := v.add_carry
  madd_overflow := v.add_overflow
  msub x y := raise_ret (v.sub x y)
  msub_borrow := v.sub_borrow
  msub_overflow := v.sub_overflow
  mmul x y := raise_ret (v.mul x y)
  mdivu := v.divu
  mdivs x y := raise_ret (v.divs x y)
  mmodu := v.modu
  mmods x y := raise_ret (v.mods x y)
  mshl x y := raise_ret (v.shl x y)
  mshr := v.shr
  mshru := v.shru
  mnegative x := raise_ret (v.negative x)
  mand := v.and
  mor := v.or
  mxor := v.xor
  mmin_signed := some v.min_signed
  mmax_signed := some v.max_signed
  mmax_unsigned := some v.max_unsigned
  munsigned := v.unsigned
  msigned := v.signed
  mrepr x := raise_ret (v.repr x)
  mdtyp_of_int := DTYPE_I v.bitwidth

end Vellvm.Semantics.VellvmIntegers
