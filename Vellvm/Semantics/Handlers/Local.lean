/- Port of Vellvm's Semantics/Handlers/Local.v. -/
module

public import Vellvm.Semantics.LLVMEvents
public import Vellvm.Semantics.Handlers.StateLaws
public import Vellvm.Semantics.Simulation
public import Vellvm.Syntax.ShowAST

@[expose] public section
namespace Vellvm.Semantics.Handlers.Local
open ITree (Effect Subeffect)
open CTree (CTree)
open Vellvm.Tree Interfaces.Params DynamicValues LLVMEvents Syntax.RawIdMaps
open Instrumentation (Diagnostics Snapshots)

variable [Pa : Params]

abbrev local_env := rmap dvalue

structure debug_locals where
  mk_debug_locals ::
  locals_set : local_env → Unit
  locals_get : Unit → local_env
export debug_locals (mk_debug_locals locals_set locals_get)

def locals_object : debug_locals := ⟨fun _ ↦ (), fun _ ↦ RM.empty _⟩

abbrev Effin (E F G : Effect) := E ⊕ₑ F ⊕ₑ LocalE ⊕ₑ G
abbrev Effout (E F G : Effect) := E ⊕ₑ F ⊕ₑ G

namespace Worker
variable {M : Effect → Effect → Type → Type v} [Runtime M]

/-- Handle the source request without debugger synchronization. -/
def handle_local {E B : Effect} [FailureE -< E] [Diagnostics M] :
    (e : LocalE.I) → local_env → M E B (LocalE.O e × local_env)
  | .LocalWrite k v, env => pure ((), RM.add k v env)
  | .LocalRead k, env =>
    match RM.find k env with
    | some v => pure (v, env)
    | none => LLVMEvents.Worker.«raise»
      ("Could not look up id ".toUTF8 ++ Utils.StringUtil.«show» k)

def update_locals_ref {E B : Effect} [Snapshots M] (_ : LocalE.I) (s : local_env) :
    M E B (Unit × local_env) := do
  Snapshots.record (.locals s)
  pure ((), s)

def handle_local_debug {E B : Effect} [FailureE -< E] [Diagnostics M] [Snapshots M]
    (e : LocalE.I) (s : local_env) : M E B (LocalE.O e × local_env) := do
  let (x, s') ← handle_local e s
  let (_, s'') ← update_locals_ref e s'
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

def interp_local_h : (e : (Effin E F G).I) → local_env → M (Effout E F G) B ((Effin E F G).O e × local_env)
  | .inl e => E_trigger E F G e
  | .inr (.inl f) => F_trigger E F G f
  | .inr (.inr (.inl e)) => handle_local_debug e
  | .inr (.inr (.inr g)) => G_trigger E F G g

def interp_local {X} (t : M (Effin E F G) B X) (s : local_env) : M (Effout E F G) B (X × local_env) :=
  Runtime.interp_state interp_local_h t s
end Worker

variable {E F G B : Effect}

def handle_local [FailureE -< E] (e : LocalE.I) (s : local_env) : CTree E B (LocalE.O e × local_env) :=
  Worker.handle_local e s

def update_locals_ref [FailureE -< E] (e : LocalE.I) (s : local_env) : CTree E B (Unit × local_env) :=
  Worker.update_locals_ref e s

def handle_local_debug [FailureE -< E] (e : LocalE.I) (s : local_env) : CTree E B (LocalE.O e × local_env) :=
  Worker.handle_local_debug e s

def E_trigger (E F G : Effect) {S : Type} (e : E.I) (s : S) : CTree (Effout E F G) B (E.O e × S) :=
  Worker.E_trigger E F G e s

def F_trigger (E F G : Effect) {S : Type} (e : F.I) (s : S) : CTree (Effout E F G) B (F.O e × S) :=
  Worker.F_trigger E F G e s

def G_trigger (E F G : Effect) {S : Type} (e : G.I) (s : S) : CTree (Effout E F G) B (G.O e × S) :=
  Worker.G_trigger E F G e s

/-- A debug synchronization is private; it changes neither the answer nor the map. -/
theorem handle_local_debug_eq [FailureE -< E] (e : LocalE.I) (s : local_env) :
    handle_local_debug (E := E) (B := B) e s = handle_local e s := by
  change (Worker.handle_local e s >>= fun p ↦
    ((pure () : CTree E B Unit) >>= fun _ ↦ pure ((), p.2)) >>= fun q ↦ pure (p.1, q.2)) = _
  simp only [pure_bind, Prod.mk.eta, bind_pure]
  rfl

theorem handle_local_read_after_write [FailureE -< E] (k : Syntax.LLVMAst.raw_id)
    (v : dvalue) (s : local_env) :
    handle_local (E := E) (B := B) (.LocalRead k) (RM.add k v s) = pure (v, RM.add k v s) := by
  simp [handle_local, Worker.handle_local, RM.find_add]

variable [FailureE -< G]

def interp_local_h (e : (Effin E F G).I) (s : local_env) : CTree (Effout E F G) B ((Effin E F G).O e × local_env) :=
  Worker.interp_local_h e s

def interp_local {X} (t : CTree (Effin E F G) B X) (s : local_env) : CTree (Effout E F G) B (X × local_env) :=
  Worker.interp_local t s

local notation "Input" => CTree (Effin E F G) B

theorem interp_local_bind (R S : Type) (t : Input R) (k : R → Input S) (s : local_env) :
    eqit Eq false false (interp_local (t >>= k) s) (interp_local t s >>= fun p ↦ interp_local (k p.1) p.2) := by
  exact eqit_strict_iff_eq.mpr (CTree.interp_state_bind interp_local_h t k s)

theorem interp_local_ret (R : Type) (s : local_env) (x : R) :
    eqit Eq false false (interp_local (CTree.ret x : Input R) s) (CTree.ret (x, s)) :=
  eqit_strict_iff_eq.mpr (CTree.interp_state_ret interp_local_h x s)

theorem interp_local_Tau {R : Type} (t : Input R) (s : local_env) :
    eqit Eq false false (interp_local t.guard s) (interp_local t s).guard :=
  eqit_strict_iff_eq.mpr (CTree.interp_state_guard interp_local_h t s)

theorem interp_local_vis_eqit (s : local_env) (S : Type) (e : (Effin E F G).I)
    (k : (Effin E F G).O e → Input S) :
    eqit Eq false false (interp_local (CTree.vis e k) s) (interp_local_h e s >>= fun p ↦ (interp_local (k p.1) p.2).guard) :=
  eqit_strict_iff_eq.mpr (CTree.interp_state_vis interp_local_h e k s)

theorem interp_local_vis (s : local_env) (S : Type) (e : (Effin E F G).I)
    (k : (Effin E F G).O e → Input S) :
    eutt Eq (interp_local (CTree.vis e k) s) (interp_local_h e s >>= fun p ↦ interp_local (k p.1) p.2) :=
  StateLaws.vis_eutt interp_local_h e k s

theorem interp_local_trigger (s : local_env) (e : (Effin E F G).I) :
    eutt Eq (interp_local (B := B) (CTree.trigger e) s) (interp_local_h e s) :=
  StateLaws.trigger_eutt interp_local_h e s

theorem interp_local_bind_trigger_eqit (s : local_env) (S : Type) (e : (Effin E F G).I)
    (k : (Effin E F G).O e → Input S) :
    eqit Eq false false (interp_local (CTree.trigger e >>= k) s) (interp_local_h e s >>= fun p ↦ (interp_local (k p.1) p.2).guard) := by
  simpa only [CTree.trigger, CTree.vis_bind, pure_bind] using interp_local_vis_eqit s S e k

theorem interp_local_trigger_bind (s : local_env) (S : Type) (e : (Effin E F G).I)
    (k : (Effin E F G).O e → Input S) :
    eutt Eq (interp_local (CTree.trigger e >>= k) s) (interp_local_h e s >>= fun p ↦ interp_local (k p.1) p.2) := by
  simpa only [CTree.trigger, CTree.vis_bind, pure_bind] using interp_local_vis s S e k

theorem Proper_interp_local {R : Type} {b : Bool} (t u : Input R) (h : eqit Eq b b t u)
    (s : local_env) : eutt Eq (interp_local t s) (interp_local u s) := by
  cases b with
  | false => cases eqit_strict_iff_eq.mp h; exact eqit_refl true true _
  | true => exact StateLaws.interp_congr interp_local_h h s

theorem Proper_interp_local_pointwise {R : Type} {b : Bool} (t u : Input R)
    (h : eqit Eq b b t u) (s s' : local_env) (hs : s = s') :
    eqit Eq b b (interp_local t s) (interp_local u s') := by
  subst s'
  exact StateLaws.interp_congr interp_local_h h s

namespace Worker
variable {M : Effect → Effect → Type → Type v} {N : Effect → Effect → Type → Type w}
variable [Runtime M] [Runtime N] [Diagnostics M] [Diagnostics N] [Snapshots M] [Snapshots N]
variable (sim : Simulation M N)

theorem handle_local_related [FailureE -< E] (e : LocalE.I) (s : local_env) :
    sim.R (E := E) (B := B) (handle_local e s) (handle_local e s) := by
  cases e with
  | LocalWrite k v => exact sim.pure _
  | LocalRead k =>
    simp only [handle_local]
    cases RM.find k s with
    | some v => exact sim.pure _
    | none => exact sim.«raise» _

theorem update_locals_ref_related (e : LocalE.I) (s : local_env) :
    sim.R (E := E) (B := B) (update_locals_ref e s) (update_locals_ref e s) :=
  sim.bind (sim.record _) (fun _ ↦ sim.pure _)

theorem handle_local_debug_related [FailureE -< E] (e : LocalE.I) (s : local_env) :
    sim.R (E := E) (B := B) (handle_local_debug e s) (handle_local_debug e s) :=
  sim.bind (handle_local_related sim e s) fun (x,s') ↦
    sim.bind (update_locals_ref_related sim e s') fun (_,s'') ↦ sim.pure (x,s'')

theorem interp_local_h_related (e : (Effin E F G).I) (s : local_env) :
    sim.R (B := B) (interp_local_h e s) (interp_local_h e s) := by
  rcases e with e | (f | (v | g))
  · exact sim.bind (sim.trigger _) fun _ ↦ sim.pure _
  · exact sim.bind (sim.trigger _) fun _ ↦ sim.pure _
  · exact handle_local_debug_related sim v s
  · exact sim.bind (sim.trigger _) fun _ ↦ sim.pure _

/-- Preserves the entire result and environment for both cursor meaning and trace erasure. -/
theorem interp_local_related {X} {p : M (Effin E F G) B X} {q : N (Effin E F G) B X}
    (hpq : sim.R p q) (s : local_env) : sim.R (interp_local p s) (interp_local q s) :=
  sim.state s (interp_local_h_related sim) hpq
end Worker

end Vellvm.Semantics.Handlers.Local
