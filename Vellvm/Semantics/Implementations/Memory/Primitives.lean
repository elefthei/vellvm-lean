module

public import Vellvm.Semantics.Implementations.Memory.Basic
public import Vellvm.Semantics.Implementations.Memory.Address
public import Vellvm.Utils.IntMaps.Operations

@[expose] public section
namespace Vellvm.Semantics.Implementations.Memory
open Interfaces.Params Interfaces.Memory EOU MemoryBytes

variable [Pa : Params]

def read_byte_raw_mem (mem : memory) (phys_ptr : Int) : Option byte :=
  Utils.IntMaps.lookup phys_ptr mem

def set_byte_raw_mem (mem : memory) (phys_ptr : Int) (b : byte) : memory :=
  Utils.IntMaps.add phys_ptr b mem

def memory_bytes_to_bytes (aid : Pa.PROV.allocationId) (bytes : List memory_byte) : List byte :=
  bytes.map fun b ↦ (b, aid)

def add_to_frame (m : Memory_stack) (k : Pa.PTR.ptr) : Memory_stack :=
  { m with Memory_stack_frame_stack := match m.Memory_stack_frame_stack with
    | .Singleton f => .Singleton (k :: f)
    | .Snoc s f => .Snoc s (k :: f) }

def add_all_to_frame (ks : List Pa.PTR.ptr) (m : Memory_stack) : Memory_stack :=
  ks.foldl add_to_frame m

def add_to_heap (m : Memory_stack) (root p : Pa.PTR.ptr) : Memory_stack :=
  let h := Utils.IntMaps.add_with (Pa.P2I.ptr_to_int root) p (fun v ↦ [v]) List.cons m.Memory_stack_heap
  { m with Memory_stack_heap := h }

def add_all_to_heap' (m : Memory_stack) (root : Pa.PTR.ptr) (ks : List Pa.PTR.ptr) : Memory_stack :=
  ks.foldl (fun ms k ↦ add_to_heap ms root k) m

def add_all_to_heap (ks : List Pa.PTR.ptr) (m : Memory_stack) : Memory_stack :=
  match ks with
  | [] => m
  | root :: _ => add_all_to_heap' m root ks

def get_frame_stack : memM Framestack := do
  let s : State ← Interfaces.Memory.get
  pure s.state_memory_stack.Memory_stack_frame_stack

def get_frame : memM Frame := do
  match ← get_frame_stack with
  | .Singleton f | .Snoc _ f => pure f

def get_mem : memM memory := do
  let s : State ← Interfaces.Memory.get
  pure s.state_memory_stack.Memory_stack_memory

def get_framestack : memM Framestack := get_frame_stack

def get_provenance : memM Pa.PROV.provenance := do
  let s : State ← Interfaces.Memory.get
  pure s.state_provenance

def get_heap : memM Heap := do
  let s : State ← Interfaces.Memory.get
  pure s.state_memory_stack.Memory_stack_heap

def app_state (f : State → State) : memM Unit := do
  Interfaces.Memory.put (f (← Interfaces.Memory.get))

def app_provenance (f : Pa.PROV.provenance → Pa.PROV.provenance) : memM Unit :=
  app_state fun s ↦ { s with state_provenance := f s.state_provenance }

def app_mem_stack (f : Memory_stack → Memory_stack) : memM Unit :=
  app_state fun s ↦ { s with state_memory_stack := f s.state_memory_stack }

def upd_provenance (p : Pa.PROV.provenance) : memM Unit := app_provenance (fun _ ↦ p)

def upd_mem_stack (m : Memory_stack) : memM Unit := app_mem_stack (fun _ ↦ m)

def app_mem (f : memory → memory) : memM Unit :=
  app_mem_stack fun m ↦ { m with Memory_stack_memory := f m.Memory_stack_memory }

def upd_mem (m : memory) : memM Unit := app_mem (fun _ ↦ m)

def app_heap (f : Heap → Heap) : memM Unit :=
  app_mem_stack fun m ↦ { m with Memory_stack_heap := f m.Memory_stack_heap }

def upd_heap (h : Heap) : memM Unit := app_heap (fun _ ↦ h)

def app_frame_stack (f : Framestack → Framestack) : memM Unit :=
  app_mem_stack fun m ↦ { m with Memory_stack_frame_stack := f m.Memory_stack_frame_stack }

def upd_frame_stack (fs : Framestack) : memM Unit := app_frame_stack (fun _ ↦ fs)

def app_frame_stack_eob (f : Framestack → EOU Framestack) : memM Unit := do
  let fs ← get_framestack
  let fs' ← lift (f fs)
  upd_frame_stack fs'

def push_frame_stack (f : Frame) (fs : Framestack) : Framestack := Snoc fs f

def pop_frame_stack : Framestack → EOU Framestack
  | .Singleton _ => raise_error "Last frame, cannot pop.".toUTF8
  | .Snoc s _ => pure s

def read_byte_raw (msg : IRString) (phys_ptr : Int) : memM byte := do
  let m ← get_mem
  match read_byte_raw_mem m phys_ptr with
  | some b => pure b
  | none => mub msg

def set_byte_raw (phys_addr : Int) (b : byte) : memM Unit := do
  let m ← get_mem
  upd_mem (set_byte_raw_mem m phys_addr b)

def add_block (aid : Pa.PROV.allocationId) (p : Pa.PTR.ptr) (_ptrs : List Pa.PTR.ptr)
    (init_bytes : List memory_byte) : memM Unit := do
  let m ← get_mem
  let bytes := memory_bytes_to_bytes aid init_bytes
  upd_mem (Utils.IntMaps.add_all_index_acc bytes (Pa.P2I.ptr_to_int p) m)

def add_ptrs_to_frame (ptrs : List Pa.PTR.ptr) : memM Unit := app_mem_stack (add_all_to_frame ptrs)

def add_ptrs_to_heap (ptrs : List Pa.PTR.ptr) : memM Unit := app_mem_stack (add_all_to_heap ptrs)

def add_block_to_stack (aid : Pa.PROV.allocationId) (p : Pa.PTR.ptr) (ptrs : List Pa.PTR.ptr)
    (init_bytes : List memory_byte) : memM Unit := do
  add_block aid p ptrs init_bytes
  add_ptrs_to_frame ptrs

def add_block_to_heap (aid : Pa.PROV.allocationId) (p : Pa.PTR.ptr) (ptrs : List Pa.PTR.ptr)
    (init_bytes : List memory_byte) : memM Unit := do
  add_block aid p ptrs init_bytes
  add_ptrs_to_heap ptrs

def Read_byte (p : Pa.PTR.ptr) : memM memory_byte := do
  let (b, aid) ← read_byte_raw "Reading from unallocated memory.".toUTF8 (Pa.P2I.ptr_to_int p)
  if Pa.PROV.access_allowed (Pa.PTR.ptr_provenance p) aid then pure b
  else mub "Read from memory with invalid provenance".toUTF8

def Write_byte (p : Pa.PTR.ptr) (b : memory_byte) : memM Unit := do
  let addr := Pa.P2I.ptr_to_int p
  let (_, aid) ← read_byte_raw "Writing to unallocated memory".toUTF8 addr
  if Pa.PROV.access_allowed (Pa.PTR.ptr_provenance p) aid then set_byte_raw addr (b, aid)
  else mub "Trying to write to memory with invalid provenance".toUTF8

def get_free_block (size align : Nat) (pr : Pa.PROV.provenance) : memM (Pa.PTR.ptr × List Pa.PTR.ptr) := do
  let aid := Pa.PROV.provenance_to_allocation_id pr
  let addr ← next_key size align
  let ptr ← lift (Pa.P2I.int_to_ptr addr (Pa.PROV.allocation_id_to_prov aid))
  let ptrs ← lift (get_consecutive_ptrs ptr size)
  pure (ptr, ptrs)

/-- A choice produces a raw integer. A rejected address aborts before any byte is registered. -/
theorem get_free_block_oom (size align : Nat) (pr : Pa.PROV.provenance) :
    ∃ k : Int → memM (Pa.PTR.ptr × List Pa.PTR.ptr),
      get_free_block size align pr = Mnext_key size align k ∧
      ∀ addr msg, Pa.P2I.int_to_ptr addr
        (Pa.PROV.allocation_id_to_prov (Pa.PROV.provenance_to_allocation_id pr)) = raise_oom msg →
        k addr = Moom msg := by
  refine ⟨_, rfl, ?_⟩
  intro addr msg h
  change memS_bind (lift (Pa.P2I.int_to_ptr addr _)) _ = Moom msg
  rw [h]
  rfl

def Allocate_bytes_with_pr (init_bytes : List memory_byte) (align : Nat) (pr : Pa.PROV.provenance) :
    memM Pa.PTR.ptr := do
  let (ptr, ptrs) ← get_free_block init_bytes.length align pr
  add_block_to_stack (Pa.PROV.provenance_to_allocation_id pr) ptr ptrs init_bytes
  pure ptr

def Malloc_bytes_with_pr (init_bytes : List memory_byte) (align : Nat) (pr : Pa.PROV.provenance) :
    memM Pa.PTR.ptr := do
  let (ptr, ptrs) ← get_free_block init_bytes.length align pr
  add_block_to_heap (Pa.PROV.provenance_to_allocation_id pr) ptr ptrs init_bytes
  pure ptr

def Mempush : memM Unit := app_frame_stack (push_frame_stack [])

def free_byte (b : Int) (m : memory) : memory := Utils.IntMaps.delete b m

def free_frame_memory (f : Frame) (m : memory) : memory :=
  f.foldl (fun mem key ↦ free_byte (Pa.P2I.ptr_to_int key) mem) m

def Mempop : memM Unit := do
  let f ← get_frame
  app_frame_stack_eob pop_frame_stack
  app_mem (free_frame_memory f)

def free_block_memory (b : block) (m : memory) : memory := free_frame_memory b m

def Free (p : Pa.PTR.ptr) : memM Unit := do
  let addr := Pa.P2I.ptr_to_int p
  let h ← get_heap
  match Utils.IntMaps.lookup addr h with
  | none => mub "Attempt to free non-heap allocated address.".toUTF8
  | some b =>
    app_mem (free_block_memory b)
    upd_heap (Utils.IntMaps.delete addr h)

instance MemoryModelPrimitivesV : MemoryModelPrimitives where
  mm_state := MemoryModelStateV
  read_byte := Read_byte
  write_byte := Write_byte
  allocate_bytes_with_pr := Allocate_bytes_with_pr
  malloc_bytes_with_pr := Malloc_bytes_with_pr
  free := Free
  mempush := Mempush
  mempop := Mempop

end Vellvm.Semantics.Implementations.Memory
