/-
Lexical numeral types translated from Rocq 9.2 Corelib.Init.{Decimal,Hexadecimal,Number}.
Copyright INRIA, CNRS and contributors. GNU Lesser General Public License Version 2.1.
-/
module

@[expose] public section
namespace Vellvm

namespace Decimal

/-- Big-endian digits. `Nil` is distinct from `D0 Nil`. -/
inductive uint where
  | Nil
  | D0 (rest : uint)
  | D1 (rest : uint)
  | D2 (rest : uint)
  | D3 (rest : uint)
  | D4 (rest : uint)
  | D5 (rest : uint)
  | D6 (rest : uint)
  | D7 (rest : uint)
  | D8 (rest : uint)
  | D9 (rest : uint)
  deriving DecidableEq

export uint (Nil D0 D1 D2 D3 D4 D5 D6 D7 D8 D9)

inductive signed_int where
  | Pos (d : uint)
  | Neg (d : uint)
  deriving DecidableEq

export signed_int (Pos Neg)
abbrev int := signed_int

inductive decimal where
  | Decimal (i : signed_int) (f : uint)
  | DecimalExp (i : signed_int) (f : uint) (e : signed_int)
  deriving DecidableEq

export decimal (Decimal DecimalExp)

def uint.toNat (d : uint) : Nat := go d 0
where
  go : uint → Nat → Nat
    | .Nil, acc => acc
    | .D0 rest, acc => go rest (acc * 10)
    | .D1 rest, acc => go rest (acc * 10 + 1)
    | .D2 rest, acc => go rest (acc * 10 + 2)
    | .D3 rest, acc => go rest (acc * 10 + 3)
    | .D4 rest, acc => go rest (acc * 10 + 4)
    | .D5 rest, acc => go rest (acc * 10 + 5)
    | .D6 rest, acc => go rest (acc * 10 + 6)
    | .D7 rest, acc => go rest (acc * 10 + 7)
    | .D8 rest, acc => go rest (acc * 10 + 8)
    | .D9 rest, acc => go rest (acc * 10 + 9)

def signed_int.toInt : signed_int → Int
  | .Pos d => Int.ofNat d.toNat
  | .Neg d => -Int.ofNat d.toNat

def uint.prependDigit : Fin 10 → uint → uint
  | 0 => .D0
  | 1 => .D1
  | 2 => .D2
  | 3 => .D3
  | 4 => .D4
  | 5 => .D5
  | 6 => .D6
  | 7 => .D7
  | 8 => .D8
  | 9 => .D9

/-- Canonical decimal spelling, with one digit for zero. -/
def uint.ofNat (n : Nat) : uint := go n .Nil
where
  go (n : Nat) (rest : uint) : uint :=
    let next := prependDigit ⟨n % 10, Nat.mod_lt _ (by decide)⟩ rest
    if h : n < 10 then next else go (n / 10) next
  termination_by n
  decreasing_by omega

end Decimal

namespace Hexadecimal

/-- Big-endian digits. `Nil` is distinct from `D0 Nil`. -/
inductive uint where
  | Nil
  | D0 (rest : uint)
  | D1 (rest : uint)
  | D2 (rest : uint)
  | D3 (rest : uint)
  | D4 (rest : uint)
  | D5 (rest : uint)
  | D6 (rest : uint)
  | D7 (rest : uint)
  | D8 (rest : uint)
  | D9 (rest : uint)
  | Da (rest : uint)
  | Db (rest : uint)
  | Dc (rest : uint)
  | Dd (rest : uint)
  | De (rest : uint)
  | Df (rest : uint)
  deriving DecidableEq

export uint (Nil D0 D1 D2 D3 D4 D5 D6 D7 D8 D9 Da Db Dc Dd De Df)

inductive signed_int where
  | Pos (d : uint)
  | Neg (d : uint)
  deriving DecidableEq

export signed_int (Pos Neg)
abbrev int := signed_int

def uint.toNat (d : uint) : Nat := go d 0
where
  go : uint → Nat → Nat
    | .Nil, acc => acc
    | .D0 rest, acc => go rest (acc * 16)
    | .D1 rest, acc => go rest (acc * 16 + 1)
    | .D2 rest, acc => go rest (acc * 16 + 2)
    | .D3 rest, acc => go rest (acc * 16 + 3)
    | .D4 rest, acc => go rest (acc * 16 + 4)
    | .D5 rest, acc => go rest (acc * 16 + 5)
    | .D6 rest, acc => go rest (acc * 16 + 6)
    | .D7 rest, acc => go rest (acc * 16 + 7)
    | .D8 rest, acc => go rest (acc * 16 + 8)
    | .D9 rest, acc => go rest (acc * 16 + 9)
    | .Da rest, acc => go rest (acc * 16 + 10)
    | .Db rest, acc => go rest (acc * 16 + 11)
    | .Dc rest, acc => go rest (acc * 16 + 12)
    | .Dd rest, acc => go rest (acc * 16 + 13)
    | .De rest, acc => go rest (acc * 16 + 14)
    | .Df rest, acc => go rest (acc * 16 + 15)

def signed_int.toInt : signed_int → Int
  | .Pos d => Int.ofNat d.toNat
  | .Neg d => -Int.ofNat d.toNat

end Hexadecimal

namespace Number

inductive signed_int where
  | IntDecimal (i : Decimal.int)
  | IntHexadecimal (i : Hexadecimal.int)
  deriving DecidableEq

export signed_int (IntDecimal IntHexadecimal)
abbrev int := signed_int

/-- `BinIntDef.Z.of_num_int` is signed magnitude in both radices. -/
def signed_int.toInt : signed_int → Int
  | .IntDecimal i => i.toInt
  | .IntHexadecimal i => i.toInt

/-- `BinIntDef.Z.to_num_int` chooses canonical decimal syntax. -/
def signed_int.ofInt (n : Int) : signed_int :=
  let d := Decimal.uint.ofNat n.natAbs
  .IntDecimal (if n < 0 then .Neg d else .Pos d)

end Number
end Vellvm
