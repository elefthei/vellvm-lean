module

public import Vellvm.Syntax.Number
public import Vellvm.Utils.DList

@[expose] public section
namespace Vellvm.Utils.StringUtil

abbrev string_fold_left {A : Type u} := @DList.string_fold_left A
abbrev rev_string := DList.rev_string
abbrev string_of_list_ascii_tail_rec := DList.string_of_list_ascii_tail_rec
abbrev list_ascii_of_string_tail_rec := DList.list_ascii_of_string_tail_rec

/-- Render list contents without brackets (as in the QuickChick printer used by Vellvm). -/
def contents (render : A → IRString) : List A → IRString
  | [] => .empty
  | x :: xs => xs.foldl (fun out y ↦ out ++ "; ".toUTF8 ++ render y) (render x)

class Show (A : Type u) where
  Build_Show ::
  «show» : A → IRString

export Show (Build_Show «show»)

def writeUint : Decimal.uint → ByteArray → ByteArray
  | .Nil, out => out
  | .D0 d, out => writeUint d (out.push 48)
  | .D1 d, out => writeUint d (out.push 49)
  | .D2 d, out => writeUint d (out.push 50)
  | .D3 d, out => writeUint d (out.push 51)
  | .D4 d, out => writeUint d (out.push 52)
  | .D5 d, out => writeUint d (out.push 53)
  | .D6 d, out => writeUint d (out.push 54)
  | .D7 d, out => writeUint d (out.push 55)
  | .D8 d, out => writeUint d (out.push 56)
  | .D9 d, out => writeUint d (out.push 57)

def show_uint (d : Decimal.uint) : IRString := writeUint d .empty

def show_int : Decimal.signed_int → IRString
  | .Pos d => show_uint d
  | .Neg d => writeUint d "-".toUTF8

def show_nat (n : Nat) : IRString := show_uint (.ofNat n)
def show_bool (b : Bool) : IRString := if b then "true".toUTF8 else "false".toUTF8
def show_Z : Int → IRString
  | .ofNat n => show_nat n
  | .negSucc n => show_int (.Neg (.ofNat (n+1)))
def show_N := show_nat

instance showUint : Show Decimal.uint := ⟨show_uint⟩
instance showInt : Show Decimal.signed_int := ⟨show_int⟩
instance showNat : Show Nat := ⟨show_nat⟩
instance showBool : Show Bool := ⟨show_bool⟩
instance showZ : Show Int := ⟨show_Z⟩
-- Rocq's N and nat both port to Nat, with the same canonical decimal spelling.
instance (priority := low) showN : Show Nat := ⟨show_N⟩
instance showPositive : Show Positive := ⟨fun p ↦ show_N p.val⟩

abbrev from_list := string_of_list_ascii_tail_rec

def unit_digit (n : Nat) : UInt8 := UInt8.ofNat (n % 10 + 48)

def pushThreeDigits (out : ByteArray) (n : Nat) : ByteArray :=
  ((out.push (unit_digit (n / 100))).push (unit_digit (n / 10))).push (unit_digit n)

def three_digit := pushThreeDigits ByteArray.empty

def digit_of_ascii (c : UInt8) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48) else none

/-- Like `ascii_of_nat`, three decimal digits wrap modulo 256, including 256–999. -/
def unthree_digit (c₂ c₁ c₀ : UInt8) : Option UInt8 := do
  let n₂ ← digit_of_ascii c₂
  let n₁ ← digit_of_ascii c₁
  let n₀ ← digit_of_ascii c₀
  return UInt8.ofNat (100*n₂ + 10*n₁ + n₀)

def pushQuotedByte (out : ByteArray) (b : UInt8) : ByteArray :=
  match b with
  | 9 => (out.push 92).push 116
  | 10 => (out.push 92).push 110
  | 13 => (out.push 92).push 114
  | 34 => (out.push 92).push 34
  | 92 => (out.push 92).push 92
  | c => if c < 32 || 126 < c then pushThreeDigits (out.push 92) c.toNat else out.push c

def finishQuote (s out : IRString) : IRString := (s.foldl pushQuotedByte out).push 34

/-- The recursive source printer includes the closing quote, but not the opening quote. -/
def show_quoted_string (s : IRString) : IRString := finishQuote s (.emptyWithCapacity (s.size + 1))

instance showString : Show IRString :=
  ⟨fun s ↦ finishQuote s ((ByteArray.emptyWithCapacity (s.size + 2)).push 34)⟩
instance showPair {A : Type u} {B : Type v} [Show A] [Show B] : Show (A × B) :=
  ⟨fun (a, b) ↦ "(".toUTF8 ++ «show» a ++ ", ".toUTF8 ++ «show» b ++ ")".toUTF8⟩
instance showOpt {A : Type u} [Show A] : Show (Option A) :=
  ⟨fun | some x => "Some ".toUTF8 ++ «show» x | none => "None".toUTF8⟩
instance showList {A : Type u} [Show A] : Show (List A) :=
  ⟨fun xs ↦ "[".toUTF8 ++ contents «show» xs ++ "]".toUTF8⟩

def newline : IRString := "\n".toUTF8

/-- Three-digit escaping has a left inverse on the whole byte domain. -/
theorem unthree_digit_unit_digits (b : UInt8) :
    unthree_digit (unit_digit (b.toNat / 100)) (unit_digit (b.toNat / 10)) (unit_digit b.toNat) =
      some b := by
  have digit (n : Nat) : digit_of_ascii (unit_digit n) = some (n % 10) := by
    simp [digit_of_ascii, unit_digit]
    omega
  have h : b.toNat < 256 := b.toNat_lt
  have he : 100 * (b.toNat / 100 % 10) + 10 * (b.toNat / 10 % 10) + b.toNat % 10 = b.toNat := by omega
  simp only [unthree_digit, digit, bind, Option.bind, pure, he, UInt8.ofNat_toNat]

end Vellvm.Utils.StringUtil
