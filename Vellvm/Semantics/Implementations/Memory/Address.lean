module

public import Vellvm.Semantics.Interfaces.Params

@[expose] public section
namespace Vellvm.Semantics.Implementations.Memory
open Interfaces.Params Interfaces.IPtr Interfaces.Sizeof Syntax.DynamicTypes EOU Utils.ListUtil

variable [Pa : Params]

def ptr_byte_offset (a : Pa.PTR.ptr) (ix : Pa.IPTR.iptr) : EOU Pa.PTR.ptr :=
  let stride := Int.ofNat (alloc_size_dtyp (DTYPE_B ⟨8, by decide⟩))
  Pa.P2I.int_to_ptr (Pa.P2I.ptr_to_int a + stride * Pa.IPTR.to_Z ix) (Pa.PTR.ptr_provenance a)

def get_consecutive_ptrs (p : Pa.PTR.ptr) (size : Nat) : EOU (List Pa.PTR.ptr) := do
  let ixs ← intptr_seq (P := Pa.IPTR) 0 size
  map_monad_acc (ptr_byte_offset p) ixs

end Vellvm.Semantics.Implementations.Memory
