module

public import Vellvm.Semantics.LLVMEvents
public import Vellvm.Utils.ListUtil

@[expose] public section
namespace Vellvm.Semantics
open ITree (Effect Subeffect)
open Tree Interfaces.Params Instrumentation

/-- Congruence needed by the shared LLVM workers. Instantiated for producer meaning and trace erasure. -/
structure Simulation (M : Effect → Effect → Type → Type v) (N : Effect → Effect → Type → Type w)
    [Runtime M] [Runtime N] [Diagnostics M] [Diagnostics N] [Pa : Params]
    [Snapshots M] [Snapshots N] where
  R {E B : Effect} {X : Type} : M E B X → N E B X → Prop
  pure {E B X} (x : X) : R (E := E) (B := B) (pure x) (pure x)
  bind {E B X Y} {l : M E B X} {r : N E B X} {k : X → M E B Y} {j : X → N E B Y} :
    R l r → (∀ x, R (k x) (j x)) → R (l >>= k) (r >>= j)
  map {E B X Y} (f : X → Y) {l : M E B X} {r : N E B X} : R l r → R (f <$> l) (f <$> r)
  trigger {E B} (e : E.I) : R (E := E) (B := B) (Runtime.trigger e) (Runtime.trigger e)
  branch {E B} (b : B.I) : R (E := E) (B := B) (Runtime.branch b) (Runtime.branch b)
  iter {E B X Y} {l : X → M E B (X ⊕ Y)} {r : X → N E B (X ⊕ Y)} (x : X) :
    (∀ a, R (l a) (r a)) → R (Runtime.iter l x) (Runtime.iter r x)
  translate {E F B : Effect} {X : Type} (h : (e : E.I) → (f : F.I) × (F.O f → E.O e))
    {l : M E B X} {r : N E B X} : R l r → R (Runtime.translate h l) (Runtime.translate h r)
  interp {E F B D X} [B -< D] {h : (e : E.I) → M F D (E.O e)} {g : (e : E.I) → N F D (E.O e)}
    {l : M E B X} {r : N E B X} : (∀ e, R (h e) (g e)) → R l r → R (Runtime.interp h l) (Runtime.interp g r)
  state {E F B D X S} [B -< D] {h : (e : E.I) → S → M F D (E.O e × S)}
    {g : (e : E.I) → S → N F D (E.O e × S)} {l : M E B X} {r : N E B X} (s : S) :
    (∀ e a, R (h e a) (g e a)) → R l r → R (Runtime.interp_state h l s) (Runtime.interp_state g r s)
  mrec {D E B X} {h : (d : D.I) → M (D ⊕ₑ E) B (D.O d)}
    {g : (d : D.I) → N (D ⊕ₑ E) B (D.O d)} {l : M (D ⊕ₑ E) B X} {r : N (D ⊕ₑ E) B X} :
    (∀ d, R (h d) (g d)) → R l r → R (Runtime.interp_mrec h l) (Runtime.interp_mrec g r)
  loc {E B} (v : Option Syntax.LLVMAst.file_info) :
    R (E := E) (B := B) (Diagnostics.setLoc v) (Diagnostics.setLoc v)
  msg {E B} (v : IRString) : R (E := E) (B := B) (Diagnostics.diagnostic v) (Diagnostics.diagnostic v)
  record {E B} (v : TraceRequest) : R (E := E) (B := B) (Snapshots.record v) (Snapshots.record v)

namespace Simulation
open LLVMEvents

variable {M : Effect → Effect → Type → Type v} {N : Effect → Effect → Type → Type w}
  [Runtime M] [Runtime N] [Diagnostics M] [Diagnostics N] [Pa : Params] [Snapshots M] [Snapshots N]
  (sim : Simulation M N) {E F B : Effect} {X Y : Type}

theorem emit [i : E -< F] (e : E.I) :
    sim.R (B := B) (Runtime.emit (M := M) (E := E) (F := F) e) (Runtime.emit (E := E) e) := by
  unfold Runtime.emit
  exact sim.map _ (sim.trigger _)

theorem raiseLLVM [LLVMExcE -< E] (x : exc) :
    sim.R (B := B) (X := X) (Worker.raiseLLVM (E := E) x) (Worker.raiseLLVM x) :=
  sim.bind (sim.emit (E := LLVMExcE) (LLVMExc x)) (fun a ↦ nomatch a)

theorem «raise» [FailureE -< E] (msg : IRString) :
    sim.R (B := B) (X := X) (Worker.«raise» (E := E) msg) (Worker.«raise» msg) :=
  sim.bind (sim.msg msg) (fun _ ↦ sim.bind (sim.emit (E := FailureE) (Throw ())) (fun a ↦ nomatch a))

theorem raiseUB [UBE -< E] (msg : IRString) :
    sim.R (B := B) (X := X) (Worker.raiseUB (E := E) msg) (Worker.raiseUB msg) :=
  sim.bind (sim.msg msg) (fun _ ↦ sim.bind (sim.emit (E := UBE) (ThrowUB ())) (fun a ↦ nomatch a))

theorem raiseOOM [OOME -< E] (msg : IRString) :
    sim.R (B := B) (X := X) (Worker.raiseOOM (E := E) msg) (Worker.raiseOOM msg) :=
  sim.bind (sim.msg msg) (fun _ ↦ sim.bind (sim.emit (E := OOME) (ThrowOOM ())) (fun a ↦ nomatch a))

theorem liftEOU [FailureE -< E] [UBE -< E] [OOME -< E] (x : EOU.EOU X) :
    sim.R (B := B) (Worker.EOU_to_itree (E := E) x) (Worker.EOU_to_itree x) := by
  cases x with
  | raise_ret x => exact sim.pure x
  | raise_error s => exact sim.«raise» s
  | raise_ub s => exact sim.raiseUB s
  | raise_oom s => exact sim.raiseOOM s

theorem withCall {t : M MCFGEtop B X} {s : N MCFGEtop B X} (h : sim.R t s) :
    sim.R (Worker.withCall t) (Worker.withCall s) := sim.translate _ h

open Syntax.LLVMAst Syntax.DynamicTypes DynamicValues

theorem gwrite [GlobalE -< E] (id : raw_id) (dv : dvalue) :
    sim.R (B := B) (Worker.gwrite (E := E) id dv) (Worker.gwrite id dv) :=
  sim.emit (E := GlobalE) (GlobalWrite id dv)

theorem gread [GlobalE -< E] (id : raw_id) :
    sim.R (B := B) (Worker.gread (E := E) id) (Worker.gread id) :=
  sim.emit (E := GlobalE) (GlobalRead id)

theorem lwrite [LocalE -< E] (id : raw_id) (dv : dvalue) :
    sim.R (B := B) (Worker.lwrite (E := E) id dv) (Worker.lwrite id dv) :=
  sim.emit (E := LocalE) (LocalWrite id dv)

theorem lread [LocalE -< E] (id : raw_id) :
    sim.R (B := B) (Worker.lread (E := E) id) (Worker.lread id) :=
  sim.emit (E := LocalE) (LocalRead id)

theorem stack_push [StackE -< E] (args : List (raw_id × dvalue)) :
    sim.R (B := B) (Worker.stack_push (E := E) args) (Worker.stack_push args) :=
  sim.emit (E := StackE) (StackPush args)

theorem stack_pop [StackE -< E] :
    sim.R (B := B) (Worker.stack_pop (E := E)) (Worker.stack_pop) :=
  sim.emit (E := StackE) (StackPop)

theorem stack_raise [StackE -< E] (x : exc) :
    sim.R (B := B) (Worker.stack_raise (E := E) x) (Worker.stack_raise x) :=
  sim.emit (E := StackE) (StackRaise x)

theorem stack_get_exc [StackE -< E] :
    sim.R (B := B) (Worker.stack_get_exc (E := E)) (Worker.stack_get_exc) :=
  sim.emit (E := StackE) (StackGetExc)

theorem mem_push [MemoryE -< E] :
    sim.R (B := B) (Worker.mem_push (E := E)) (Worker.mem_push) :=
  sim.emit (E := MemoryE) (MemPush)

theorem mem_pop [MemoryE -< E] :
    sim.R (B := B) (Worker.mem_pop (E := E)) (Worker.mem_pop) :=
  sim.emit (E := MemoryE) (MemPop)

theorem alloca [MemoryE -< E] (t : dtyp) (num_elements : Nat) (align : Option Nat) :
    sim.R (B := B) (Worker.alloca (E := E) t num_elements align) (Worker.alloca t num_elements align) :=
  sim.emit (E := MemoryE) (Alloca t num_elements align)

theorem load [MemoryE -< E] (t : dtyp) (a : dvalue) :
    sim.R (B := B) (Worker.load (E := E) t a) (Worker.load t a) :=
  sim.emit (E := MemoryE) (Load t a)

theorem store [MemoryE -< E] (t : dtyp) (a : dvalue) (v : dvalue) :
    sim.R (B := B) (Worker.store (E := E) t a v) (Worker.store t a v) :=
  sim.emit (E := MemoryE) (Store t a v)

theorem conv [MemoryE -< E] (cv : impure_conversion) (t_from : dtyp) (v : dvalue) (t_to : dtyp) :
    sim.R (B := B) (Worker.conv (E := E) cv t_from v t_to) (Worker.conv cv t_from v t_to) :=
  sim.emit (E := MemoryE) (Conv cv t_from v t_to)

theorem draw [DrawE -< E] (t : dtyp) :
    sim.R (B := B) (Worker.draw (E := E) t) (Worker.draw t) :=
  sim.emit (E := DrawE) (Draw t)

theorem call [CallE -< E] (t : dtyp) (cc : cconv) (f : dvalue) (args : List (dtyp × dvalue)) :
    sim.R (B := B) (Worker.call (E := E) t cc f args) (Worker.call t cc f args) :=
  sim.emit (E := CallE) (Call t cc f args)

theorem external_call [ExternalCallE -< E] (t : dtyp) (f : dvalue) (args : List (dtyp × dvalue)) :
    sim.R (B := B) (Worker.external_call (E := E) t f args) (Worker.external_call t f args) :=
  sim.emit (E := ExternalCallE) (ExternalCall t f args)

theorem io_stdout [ExternalCallE -< E] (bytes : List VellvmIntegers.int8) :
    sim.R (B := B) (Worker.io_stdout (E := E) bytes) (Worker.io_stdout bytes) :=
  sim.emit (E := ExternalCallE) (IO_stdout bytes)

theorem io_stderr [ExternalCallE -< E] (bytes : List VellvmIntegers.int8) :
    sim.R (B := B) (Worker.io_stderr (E := E) bytes) (Worker.io_stderr bytes) :=
  sim.emit (E := ExternalCallE) (IO_stderr bytes)

theorem intrinsic [IntrinsicE -< E] (t : dtyp) (f : IRString) (args : List (dtyp × dvalue)) (vararg : Option Pa.PTR.ptr) :
    sim.R (B := B) (Worker.intrinsic (E := E) t f args vararg) (Worker.intrinsic t f args vararg) :=
  sim.emit (E := IntrinsicE) (Intrinsic t f args vararg)

theorem debug [DebugE -< E] (s : IRString) :
    sim.R (B := B) (Worker.debug (E := E) s) (Worker.debug s) :=
  sim.bind (sim.msg s) (fun _ ↦ sim.emit (E := DebugE) (Debug ()))

theorem map_monad {A : Type z} {f : A → M E B X} {g : A → N E B X}
    (h : ∀ a, sim.R (f a) (g a)) (xs : List A) :
    sim.R (Utils.ListUtil.map_monad f xs) (Utils.ListUtil.map_monad g xs) := by
  induction xs with
  | nil => exact sim.pure []
  | cons x xs ih => exact sim.bind (h x) (fun b ↦ sim.bind ih (fun bs ↦ sim.pure (b :: bs)))

theorem loop_monad {A : Type z} {f : A → M E B X} {g : A → N E B X}
    (h : ∀ a, sim.R (f a) (g a)) (xs : List A) :
    sim.R (Utils.ListUtil.loop_monad f xs) (Utils.ListUtil.loop_monad g xs) := by
  induction xs with
  | nil => exact sim.pure PUnit.unit
  | cons x xs ih => exact sim.bind (h x) (fun _ ↦ ih)


end Simulation

end Vellvm.Semantics
