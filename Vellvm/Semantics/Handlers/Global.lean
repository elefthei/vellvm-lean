/- Port of Vellvm's Semantics/Handlers/Global.v. -/
module

public import Vellvm.Semantics.LLVMEvents
public import Vellvm.Semantics.Handlers.StateLaws
public import Vellvm.Semantics.Simulation
public import Vellvm.Syntax.ShowAST

@[expose] public section
namespace Vellvm.Semantics.Handlers.Global
open ITree (Effect Subeffect)
open CTree (CTree)
open Vellvm.Tree Interfaces.Params DynamicValues LLVMEvents Syntax.RawIdMaps
open Instrumentation (Diagnostics Snapshots)

variable [Pa : Params]

abbrev global_env := rmap dvalue

structure debug_globals where
  mk_debug_globals ::
  globals_set : global_env → Unit
  globals_get : Unit → global_env
export debug_globals (mk_debug_globals globals_set globals_get)

def globals_object : debug_globals := ⟨fun _ ↦ (), fun _ ↦ RM.empty _⟩

abbrev Effin (E F G : Effect) := E ⊕ₑ F ⊕ₑ GlobalE ⊕ₑ G
abbrev Effout (E F G : Effect) := E ⊕ₑ F ⊕ₑ G

namespace Worker
variable {M : Effect → Effect → Type → Type v} [Runtime M]

/-- Handle the source request without debugger synchronization. -/
def handle_global {E B : Effect} [FailureE -< E] [Diagnostics M] :
    (e : GlobalE.I) → global_env → M E B (GlobalE.O e × global_env)
  | .GlobalWrite k v, env => pure ((), RM.add k v env)
  | .GlobalRead k, env =>
    match RM.find k env with
    | some v => pure (v, env)
    | none => LLVMEvents.Worker.«raise»
      ("Could not look up global id ".toUTF8 ++ Utils.StringUtil.«show» k)

def update_globals_ref {E B : Effect} [Snapshots M] (_ : GlobalE.I) (s : global_env) :
    M E B (Unit × global_env) := do
  Snapshots.record (.globals s)
  pure ((), s)

def handle_global_debug {E B : Effect} [FailureE -< E] [Diagnostics M] [Snapshots M]
    (e : GlobalE.I) (s : global_env) : M E B (GlobalE.O e × global_env) := do
  let (x, s') ← handle_global e s
  let (_, s'') ← update_globals_ref e s'
  pure (x, s'')

def E_trigger (E F G : Effect) {B : Effect} {S : Type} (e : E.I) (s : S) :
    M (Effout E F G) B (E.O e × S) :=
  StateLaws.Worker.forward (E := Effout E F G) (Sum.inl e) s

def F_trigger (E F G : Effect) {B : Effect} {S : Type} (e : F.I) (s : S) :
    M (Effout E F G) B (F.O e × S) :=
  StateLaws.Worker.forward (E := Effout E F G) (.inr (.inl e)) s

def G_trigger (E F G : Effect) {B : Effect} {S : Type} (e : G.I) (s : S) :
    M (Effout E F G) B (G.O e × S) :=
  StateLaws.Worker.forward (E := Effout E F G) (.inr (.inr e)) s

variable {E F G B : Effect} [FailureE -< G] [Diagnostics M] [Snapshots M]

def interp_global_h : (e : (Effin E F G).I) → global_env → M (Effout E F G) B ((Effin E F G).O e × global_env)
  | .inl e => E_trigger E F G e
  | .inr (.inl f) => F_trigger E F G f
  | .inr (.inr (.inl e)) => handle_global_debug e
  | .inr (.inr (.inr g)) => G_trigger E F G g

def interp_global {X} (t : M (Effin E F G) B X) (s : global_env) : M (Effout E F G) B (X × global_env) :=
  Runtime.interp_state interp_global_h t s
end Worker

variable {E F G B : Effect}

def handle_global [FailureE -< E] (e : GlobalE.I) (s : global_env) : CTree E B (GlobalE.O e × global_env) :=
  Worker.handle_global e s

def update_globals_ref [FailureE -< E] (e : GlobalE.I) (s : global_env) : CTree E B (Unit × global_env) :=
  Worker.update_globals_ref e s

def handle_global_debug [FailureE -< E] (e : GlobalE.I) (s : global_env) : CTree E B (GlobalE.O e × global_env) :=
  Worker.handle_global_debug e s

def E_trigger (E F G : Effect) {S : Type} (e : E.I) (s : S) : CTree (Effout E F G) B (E.O e × S) :=
  Worker.E_trigger E F G e s

def F_trigger (E F G : Effect) {S : Type} (e : F.I) (s : S) : CTree (Effout E F G) B (F.O e × S) :=
  Worker.F_trigger E F G e s

def G_trigger (E F G : Effect) {S : Type} (e : G.I) (s : S) : CTree (Effout E F G) B (G.O e × S) :=
  Worker.G_trigger E F G e s

/-- A debug synchronization is private; it changes neither the answer nor the map. -/
theorem handle_global_debug_eq [FailureE -< E] (e : GlobalE.I) (s : global_env) :
    handle_global_debug (E := E) (B := B) e s = handle_global e s := by
  change (Worker.handle_global e s >>= fun p ↦
    ((pure () : CTree E B Unit) >>= fun _ ↦ pure ((), p.2)) >>= fun q ↦ pure (p.1, q.2)) = _
  simp only [pure_bind, Prod.mk.eta, bind_pure]
  rfl

theorem handle_global_read_after_write [FailureE -< E] (k : Syntax.LLVMAst.raw_id)
    (v : dvalue) (s : global_env) :
    handle_global (E := E) (B := B) (.GlobalRead k) (RM.add k v s) = pure (v, RM.add k v s) := by
  simp [handle_global, Worker.handle_global, RM.find_add]

variable [FailureE -< G]

def interp_global_h (e : (Effin E F G).I) (s : global_env) : CTree (Effout E F G) B ((Effin E F G).O e × global_env) :=
  Worker.interp_global_h e s

def interp_global {X} (t : CTree (Effin E F G) B X) (s : global_env) : CTree (Effout E F G) B (X × global_env) :=
  Worker.interp_global t s

local notation "Input" => CTree (Effin E F G) B

theorem interp_global_bind (R S : Type) (t : Input R) (k : R → Input S) (s : global_env) :
    eqit Eq false false (interp_global (t >>= k) s) (interp_global t s >>= fun p ↦ interp_global (k p.1) p.2) := by
  exact eqit_strict_iff_eq.mpr (CTree.interp_state_bind interp_global_h t k s)

theorem interp_global_ret (R : Type) (s : global_env) (x : R) :
    eqit Eq false false (interp_global (CTree.ret x : Input R) s) (CTree.ret (x, s)) :=
  eqit_strict_iff_eq.mpr (CTree.interp_state_ret interp_global_h x s)

theorem interp_global_Tau {R : Type} (t : Input R) (s : global_env) :
    eqit Eq false false (interp_global t.guard s) (interp_global t s).guard :=
  eqit_strict_iff_eq.mpr (CTree.interp_state_guard interp_global_h t s)

theorem interp_global_vis_eqit (s : global_env) (S : Type) (e : (Effin E F G).I)
    (k : (Effin E F G).O e → Input S) :
    eqit Eq false false (interp_global (CTree.vis e k) s) (interp_global_h e s >>= fun p ↦ (interp_global (k p.1) p.2).guard) :=
  eqit_strict_iff_eq.mpr (CTree.interp_state_vis interp_global_h e k s)

theorem interp_global_vis (s : global_env) (S : Type) (e : (Effin E F G).I)
    (k : (Effin E F G).O e → Input S) :
    eutt Eq (interp_global (CTree.vis e k) s) (interp_global_h e s >>= fun p ↦ interp_global (k p.1) p.2) :=
  StateLaws.vis_eutt interp_global_h e k s

theorem interp_global_trigger (s : global_env) (e : (Effin E F G).I) :
    eutt Eq (interp_global (B := B) (CTree.trigger e) s) (interp_global_h e s) :=
  StateLaws.trigger_eutt interp_global_h e s

theorem interp_global_bind_trigger_eqit (s : global_env) (S : Type) (e : (Effin E F G).I)
    (k : (Effin E F G).O e → Input S) :
    eqit Eq false false (interp_global (CTree.trigger e >>= k) s) (interp_global_h e s >>= fun p ↦ (interp_global (k p.1) p.2).guard) := by
  simpa only [CTree.trigger, CTree.vis_bind, pure_bind] using interp_global_vis_eqit s S e k

theorem interp_global_bind_trigger (s : global_env) (S : Type) (e : (Effin E F G).I)
    (k : (Effin E F G).O e → Input S) :
    eutt Eq (interp_global (CTree.trigger e >>= k) s) (interp_global_h e s >>= fun p ↦ interp_global (k p.1) p.2) := by
  simpa only [CTree.trigger, CTree.vis_bind, pure_bind] using interp_global_vis s S e k

theorem eutt_interp_global {R : Type} {b : Bool} (t u : Input R)
    (h : eqit Eq b b t u) (s s' : global_env) (hs : s = s') :
    eqit Eq b b (interp_global t s) (interp_global u s') := by
  subst s'
  exact StateLaws.interp_congr interp_global_h h s

namespace Worker
variable {M : Effect → Effect → Type → Type v} {N : Effect → Effect → Type → Type w}
variable [Runtime M] [Runtime N] [Diagnostics M] [Diagnostics N] [Snapshots M] [Snapshots N]
variable (sim : Simulation M N)

theorem handle_global_related [FailureE -< E] (e : GlobalE.I) (s : global_env) :
    sim.R (E := E) (B := B) (handle_global e s) (handle_global e s) := by
  cases e with
  | GlobalWrite k v => exact sim.pure _
  | GlobalRead k =>
    simp only [handle_global]
    cases RM.find k s with
    | some v => exact sim.pure _
    | none => exact sim.«raise» _

theorem update_globals_ref_related (e : GlobalE.I) (s : global_env) :
    sim.R (E := E) (B := B) (update_globals_ref e s) (update_globals_ref e s) :=
  sim.bind (sim.record _) (fun _ ↦ sim.pure _)

theorem handle_global_debug_related [FailureE -< E] (e : GlobalE.I) (s : global_env) :
    sim.R (E := E) (B := B) (handle_global_debug e s) (handle_global_debug e s) :=
  sim.bind (handle_global_related sim e s) fun (x,s') ↦
    sim.bind (update_globals_ref_related sim e s') fun (_,s'') ↦ sim.pure (x,s'')

theorem interp_global_h_related (e : (Effin E F G).I) (s : global_env) :
    sim.R (B := B) (interp_global_h e s) (interp_global_h e s) := by
  rcases e with e | (f | (v | g))
  · exact sim.bind (sim.trigger _) fun _ ↦ sim.pure _
  · exact sim.bind (sim.trigger _) fun _ ↦ sim.pure _
  · exact handle_global_debug_related sim v s
  · exact sim.bind (sim.trigger _) fun _ ↦ sim.pure _

/-- Preserves the entire result and environment for both cursor meaning and trace erasure. -/
theorem interp_global_related {X} {p : M (Effin E F G) B X} {q : N (Effin E F G) B X}
    (hpq : sim.R p q) (s : global_env) : sim.R (interp_global p s) (interp_global q s) :=
  sim.state s (interp_global_h_related sim) hpq
end Worker

end Vellvm.Semantics.Handlers.Global
