module

public import Vellvm.Semantics.EOU
public import Vellvm.Semantics.Interfaces.Params
public import Vellvm.Semantics.MemoryBytes.Basic

@[expose] public section
namespace Vellvm.Semantics.Interfaces.Memory

open Vellvm.Semantics.EOU
universe u v w z r

inductive memC where
  | Cnext_key (size align : Nat)
  | Cfresh_prov
  | Cexposed_prov
  deriving DecidableEq

export memC (Cnext_key Cfresh_prov Cexposed_prov)

def memCType {P : Type} : memC → Type
  | .Cnext_key _ _ => Int
  | .Cfresh_prov => P
  | .Cexposed_prov => Option P

inductive memS (S : Type u) (A : Type v) (P : Type) (X : Type w) : Type (max u w) where
  | Mret (x : X)
  | Moom (s : IRString)
  | Mub (s : IRString)
  | Merr (s : IRString)
  | Mget (k : S → memS S A P X)
  | Mput (s : S) (k : Unit → memS S A P X)
  | Mchoose (c : memC) (k : memCType (P := P) c → memS S A P X)

export memS (Mret Moom Mub Merr Mget Mput Mchoose)

variable {S : Type u} {A : Type v} {P : Type} {X : Type w} {Y : Type z}

@[elab_as_elim] def memS_rect (Q : memS S A P X → Type r)
    (ret : ∀ x, Q (Mret x)) (oom : ∀ s, Q (Moom s)) (ub : ∀ s, Q (Mub s))
    (err : ∀ s, Q (Merr s)) (get : ∀ k, (∀ s, Q (k s)) → Q (Mget k))
    (put : ∀ s k, (∀ t, Q (k t)) → Q (Mput s k))
    (choose : ∀ c k, (∀ a, Q (k a)) → Q (Mchoose c k)) : ∀ m, Q m
  | .Mret x => ret x
  | .Moom s => oom s
  | .Mub s => ub s
  | .Merr s => err s
  | .Mget k => get k (fun s ↦ memS_rect Q ret oom ub err get put choose (k s))
  | .Mput s k => put s k (fun t ↦ memS_rect Q ret oom ub err get put choose (k t))
  | .Mchoose c k => choose c k (fun a ↦ memS_rect Q ret oom ub err get put choose (k a))

@[elab_as_elim] abbrev memS_rec (Q : memS S A P X → Type) := memS_rect Q
@[elab_as_elim] theorem memS_ind (Q : memS S A P X → Prop) :
    (∀ x, Q (Mret x)) → (∀ s, Q (Moom s)) → (∀ s, Q (Mub s)) → (∀ s, Q (Merr s)) →
    (∀ k, (∀ s, Q (k s)) → Q (Mget k)) →
    (∀ s k, (∀ t, Q (k t)) → Q (Mput s k)) →
    (∀ c k, (∀ a, Q (k a)) → Q (Mchoose c k)) → ∀ m, Q m := memS.rec (motive := Q)

@[elab_as_elim] alias memS_sind := memS_ind

def Mnext_key (size align : Nat) (k : Int → memS S A P X) : memS S A P X :=
  Mchoose (Cnext_key size align) k

def Mfresh_prov (k : P → memS S A P X) : memS S A P X := Mchoose Cfresh_prov k

def Mexposed_prov (k : Option P → memS S A P X) : memS S A P X := Mchoose Cexposed_prov k

def memS_bind (m : memS S A P X) (k : X → memS S A P Y) : memS S A P Y :=
  match m with
  | .Mret x => k x
  | .Moom s => Moom s
  | .Mub s => Mub s
  | .Merr s => Merr s
  | .Mget g => Mget (fun s ↦ memS_bind (g s) k)
  | .Mput s g => Mput s (fun _ ↦ memS_bind (g ()) k)
  | .Mchoose c g => Mchoose c (fun a ↦ memS_bind (g a) k)

instance memS_mon : Monad (memS S A P) where
  pure := Mret
  bind := memS_bind

@[simp] theorem memS_bind_Mret (x : X) (k : X → memS S A P Y) : memS_bind (Mret x) k = k x := rfl

@[simp] theorem memS_bind_ret (m : memS S A P X) : memS_bind m Mret = m := by
  induction m <;> simp [memS_bind, *]

theorem memS_bind_assoc {Z : Type r} (m : memS S A P X) (f : X → memS S A P Y)
    (g : Y → memS S A P Z) :
    memS_bind (memS_bind m f) g = memS_bind m (fun x ↦ memS_bind (f x) g) := by
  induction m <;> simp [memS_bind, *]

def lift : EOU X → memS S A P X
  | .raise_ret x => Mret x
  | .raise_error s => Merr s
  | .raise_oom s => Moom s
  | .raise_ub s => Mub s

def mub (s : IRString) : memS S A P X := Mub s
def merr (s : IRString) : memS S A P X := Merr s
def moom (s : IRString) : memS S A P X := Moom s
def put (s : S) : memS S A P Unit := Mput s (fun _ ↦ Mret ())
def get : memS S A P S := Mget Mret
def next_key (size align : Nat) : memS S A P Int := Mnext_key size align Mret
def fresh_prov (_ : Unit) : memS S A P P := Mfresh_prov Mret
def exposed_prov (_ : Unit) : memS S A P (Option P) := Mexposed_prov Mret

open Interfaces.Params

class MemoryModelState [Pa : Params] where
  Build_MemoryModelState ::
  state : Type u
  memory_stack : Type v
  frame : Type w
  framestack : Type z
  heap : Type r
  state_get_memory : state → memory_stack
  state_get_provenance : state → Pa.PROV.provenance
  memory_stack_framestack : memory_stack → framestack
  memory_stack_heap : memory_stack → heap
  state_put_memory : state → memory_stack → state
  initial_state : state
  initial_frame : frame
  initial_heap : heap

export MemoryModelState (Build_MemoryModelState state memory_stack frame framestack heap
  state_get_memory state_get_provenance memory_stack_framestack memory_stack_heap state_put_memory
  initial_state initial_frame initial_heap)

abbrev memM [Pa : Params] [MMS : MemoryModelState] := memS MMS.state Pa.PTR.ptr Pa.PROV.provenance

class MemoryModelPrimitives [Pa : Params] where
  Build_MemoryModelPrimitives ::
  mm_state : MemoryModelState.{u, v, w, z, r}
  read_byte : Pa.PTR.ptr → memM (MMS := mm_state) MemoryBytes.memory_byte
  write_byte : Pa.PTR.ptr → MemoryBytes.memory_byte → memM (MMS := mm_state) Unit
  allocate_bytes_with_pr : List MemoryBytes.memory_byte → Nat → Pa.PROV.provenance →
    memM (MMS := mm_state) Pa.PTR.ptr
  malloc_bytes_with_pr : List MemoryBytes.memory_byte → Nat → Pa.PROV.provenance →
    memM (MMS := mm_state) Pa.PTR.ptr
  free : Pa.PTR.ptr → memM (MMS := mm_state) Unit
  mempush : memM (MMS := mm_state) Unit
  mempop : memM (MMS := mm_state) Unit

export MemoryModelPrimitives (Build_MemoryModelPrimitives mm_state read_byte write_byte
  allocate_bytes_with_pr malloc_bytes_with_pr free mempush mempop)
attribute [instance] MemoryModelPrimitives.mm_state

end Vellvm.Semantics.Interfaces.Memory
