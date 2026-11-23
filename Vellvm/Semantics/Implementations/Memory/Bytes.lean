import Vellvm.Semantics.Implementations.Memory.Address
import Vellvm.Semantics.Interfaces.Memory
import Vellvm.Semantics.MemoryBytes

namespace Vellvm.Semantics.Implementations.Memory
open Interfaces.Params Interfaces.Memory Interfaces.Sizeof Syntax.DynamicTypes DynamicValues MemoryBytes
open Utils.ListUtil

universe u v w z r
variable [Pa : Params] [MMP : MemoryModelPrimitives.{u,v,w,z,r}]

def read_bytes (p : Pa.PTR.ptr) (size : Nat) : memM (List memory_byte) := do
  let ptrs ← lift (get_consecutive_ptrs p size)
  map_monad_acc MMP.read_byte ptrs

def read_dvalue (dt : dtyp) (p : Pa.PTR.ptr) : memM dvalue := do
  let bytes ← read_bytes p (Pa.SIZE.store_size_dtyp dt)
  lift (memory_bytes_to_dvalue bytes dt)

def write_bytes (p : Pa.PTR.ptr) (bytes : List memory_byte) : memM Unit := do
  let ptrs ← lift (get_consecutive_ptrs p bytes.length)
  loop_monad (fun (addr, b) ↦ MMP.write_byte addr b) (zip_acc ptrs bytes)

def write_dvalue (p : Pa.PTR.ptr) (dt : dtyp) (v : dvalue) : memM Unit := do
  let bytes ← lift (dvalue_to_memory_bytes dt v none)
  write_bytes p bytes

def generate_num_poison_bytes_h (_start_ix num : Nat) : List (memory_byte (Pa := Pa)) :=
  List.replicate num poison_memory_byte

def generate_num_poison_bytes (num : Nat) : List (memory_byte (Pa := Pa)) :=
  generate_num_poison_bytes_h 0 num

def generate_poison_bytes (dt : dtyp) : List (memory_byte (Pa := Pa)) :=
  generate_num_poison_bytes (Pa.SIZE.store_size_dtyp dt)

def allocate_bytes (init_bytes : List memory_byte) (align : Nat) : memM Pa.PTR.ptr := do
  let pr ← fresh_prov ()
  MMP.allocate_bytes_with_pr init_bytes align pr

def allocate_dtyp (dt : dtyp) (num_elements align : Nat) : memM Pa.PTR.ptr := do
  if dtyp_eqb dt DTYPE_Void then mub "allocating void type".toUTF8
  else allocate_bytes (generate_num_poison_bytes (num_elements * Pa.SIZE.store_size_dtyp dt)) align

end Vellvm.Semantics.Implementations.Memory
