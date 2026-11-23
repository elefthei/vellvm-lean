module

public import Vellvm.Semantics.Denotation.Basic
public import Vellvm.Semantics.DynamicValues.Canonical
public import Vellvm.Semantics.Simulation
public import Vellvm.Tree.Catch
public import Vellvm.Utils.IntMaps.Basic

@[expose] public section
namespace Vellvm.Semantics.Denotation
open ITree (Effect Subeffect)
open Tree Interfaces.Params DynamicValues Syntax.LLVMAst Syntax.CFG Syntax.DynamicTypes
open LLVMEvents (MemoryE StackE CFGtop CFGEtop exc)
open Utils.IntMaps (IntMap)

variable [Pa : Params]

def exc_of_event : CFGEtop.I → Option exc
  | .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl (.LLVMExc v))))))))) => some v
  | _ => none

def combine_lists_varargs {A : Type u} {B : Type w} : List A → List B → EOU.EOU (List (A × B) × List B)
  | [], ys => .raise_ret ([], ys)
  | _ :: _, [] => .raise_error "combine_lists_varargs: too few arguments".toUTF8
  | x :: xs, y :: ys => do
    let (ps, vs) ← combine_lists_varargs xs ys
    pure ((x, y) :: ps, vs)

namespace Worker
variable {M : Effect → Effect → Type → Type v}

abbrev function_denotation (M : Effect → Effect → Type → Type v) [Params] :=
  cconv → dtyp → List (dtyp × dvalue) → M CFGEtop NoChoice (exc ⊕ dvalue)

def lookup_defn (dv : dvalue) (m : IntMap (function_denotation M)) : Option (function_denotation M) :=
  (dvalue_ptr_address dv).bind fun addr ↦ Utils.IntMaps.lookup addr m

def run_exc [Catch M] {A} (t : M CFGEtop NoChoice A) : M CFGEtop NoChoice (exc ⊕ A) :=
  Catch.run exc_of_event t

variable [Runtime M]

def pop_call_frame {E B : Effect} [MemoryE -< E] [StackE -< E] : M E B Unit := do
  LLVMEvents.Worker.stack_pop
  LLVMEvents.Worker.mem_pop

def push_call_frame [Instrumentation.Diagnostics M] (df : definition dtyp (cfg dtyp))
    (args : List (dtyp × dvalue)) : M CFGEtop NoChoice Pa.PTR.ptr := do
  let (bs, vs) ← LLVMEvents.Worker.EOU_to_itree (combine_lists_varargs df.df_args args)
  let dt := dtyp.DTYPE_Struct true (vs.map Prod.fst)
  LLVMEvents.Worker.mem_push
  LLVMEvents.Worker.stack_push (bs.map fun (x, _, v) ↦ (x, v))
  let vargs ← LLVMEvents.Worker.alloca dt 1 none
  LLVMEvents.Worker.store dt vargs (canonicalize_agg dt (vs.map Prod.snd))
  match vargs with
  | .DVALUE_Base (.DVALUE_Pointer p) => pure p
  | _ => LLVMEvents.Worker.«raise» "Non-address returned from alloca of varargs".toUTF8

end Worker

abbrev function_denotation [Params] := Worker.function_denotation CTree.CTree

def lookup_defn (dv : dvalue) (m : IntMap function_denotation) : Option function_denotation :=
  Worker.lookup_defn dv m

def run_exc {A} (t : CFGtop A) : CFGtop (exc ⊕ A) := Worker.run_exc t

def pop_call_frame {E B : Effect} [MemoryE -< E] [StackE -< E] : CTree.CTree E B Unit :=
  Worker.pop_call_frame

def push_call_frame (df : definition dtyp (cfg dtyp)) (args : List (dtyp × dvalue)) :
    CFGtop Pa.PTR.ptr := Worker.push_call_frame df args

section Simulation
variable {M : Effect → Effect → Type → Type v} {N : Effect → Effect → Type → Type w}
variable [Runtime M] [Runtime N] [Instrumentation.Diagnostics M] [Instrumentation.Diagnostics N]
variable [Instrumentation.Snapshots M] [Instrumentation.Snapshots N] [Catch M] [Catch N]

/-- The only additional congruence needed by a function's unwind boundary. -/
def CatchCompatible (sim : Simulation M N) : Prop :=
  ∀ {E B : Effect} {X A : Type} (select : E.I → Option X) {l : M E B A} {r : N E B A},
    sim.R l r → sim.R (Catch.run select l) (Catch.run select r)

namespace Worker

theorem pop_call_frame_related (sim : Simulation M N) {E B : Effect} [MemoryE -< E] [StackE -< E] :
    sim.R (E := E) (B := B) pop_call_frame pop_call_frame := by
  unfold pop_call_frame
  exact sim.bind (sim.emit (E := StackE) LLVMEvents.StackPop)
    fun _ ↦ sim.emit (E := MemoryE) LLVMEvents.MemPop

theorem push_call_frame_related (sim : Simulation M N) (df : definition dtyp (cfg dtyp))
    (args : List (dtyp × dvalue)) : sim.R (push_call_frame df args) (push_call_frame df args) := by
  unfold push_call_frame
  apply sim.bind (sim.liftEOU _)
  rintro ⟨bs, vs⟩
  apply sim.bind (sim.emit (E := MemoryE) LLVMEvents.MemPush)
  intro _
  apply sim.bind (sim.emit (E := StackE) (.StackPush _))
  intro _
  apply sim.bind (sim.emit (E := MemoryE) (.Alloca _ _ _))
  intro vargs
  apply sim.bind (sim.emit (E := MemoryE) (.Store _ _ _))
  intro _
  cases vargs with
  | DVALUE_Base b => cases b <;> first | exact sim.pure _ | exact sim.raise _
  | _ => exact sim.raise _

end Worker

end Simulation
end Vellvm.Semantics.Denotation
