module

public import Vellvm.Semantics.VellvmIntegers

@[expose] public section
namespace Vellvm.Semantics.MemoryBytes
open VellvmIntegers

variable {I : Type u} [VInt I]

def extract_bit_vint (i : I) (idx : Nat) : Int :=
  VInt.unsigned (modu (shru i (VInt.repr idx)) (VInt.repr 2))

def concat_bits_vint : List I → I
  | [] => VInt.repr 0
  | b :: bs => add b (shl (concat_bits_vint bs) (VInt.repr 1))

def extract_byte_vint (i : I) (idx : Nat) : Int :=
  VInt.unsigned (modu (shru i (VInt.repr ((idx : Int) * 8))) (VInt.repr 256))

def concat_bytes_vint : List I → I
  | [] => VInt.repr 0
  | b :: bs => add b (shl (concat_bytes_vint bs) (VInt.repr 8))

def extract_bit_Z (x : Int) (idx : Nat) : Int := (x / 2^idx) % 2

def concat_bits_Z_vint (bits : List Int) : I := concat_bits_vint (bits.map VInt.repr)

def extract_byte_Z (x : Int) (idx : Nat) : Int := (x / 2^(8 * idx)) % 256

def concat_bytes_Z_vint (bytes : List Int) : I := concat_bytes_vint (bytes.map VInt.repr)

def concat_bits_Z : List Int → Int
  | [] => 0
  | b :: bs => b + 2 * concat_bits_Z bs

def concat_bytes_Z : List Int → Int
  | [] => 0
  | b :: bs => b + 256 * concat_bytes_Z bs

end Vellvm.Semantics.MemoryBytes
