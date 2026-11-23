import PortChecks.SourceType
import Vellvm.Semantics.Handlers.Global
import Vellvm.Tree.Logged

open ITree (Effect Subeffect)
open CTree (CTree)
open Vellvm.Tree Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.LLVMEvents
open Vellvm.Semantics.Handlers.Global

private abbrev InRow [Params] (E F G : Effect) := E ⊕ₑ F ⊕ₑ GlobalE ⊕ₑ G
private abbrev OutRow (E F G : Effect) := E ⊕ₑ F ⊕ₑ G

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|global_env"
  global_env : ∀ [Pa : Params], Type

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|handle_global"
  handle_global : ∀ [Pa : Params] {E B : Effect} [FailureE -< E] (e : GlobalE.I),
    global_env → CTree E B (GlobalE.O e × global_env)

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|debug_globals"
  debug_globals : ∀ [Pa : Params], Type

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|mk_debug_globals"
  mk_debug_globals : ∀ [Pa : Params],
    (global_env → Unit) → (Unit → global_env) → debug_globals

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|globals_set"
  globals_set : ∀ [Pa : Params], debug_globals → global_env → Unit

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|globals_get"
  globals_get : ∀ [Pa : Params], debug_globals → Unit → global_env

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|globals_object"
  globals_object : ∀ [Pa : Params], debug_globals

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|update_globals_ref"
  update_globals_ref : ∀ [Pa : Params] {E B : Effect} [FailureE -< E],
    GlobalE.I → global_env → CTree E B (Unit × global_env)

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|handle_global_debug"
  handle_global_debug : ∀ [Pa : Params] {E B : Effect} [FailureE -< E] (e : GlobalE.I),
    global_env → CTree E B (GlobalE.O e × global_env)

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|E_trigger"
  E_trigger : ∀ {B : Effect.{0}} (E F G : Effect.{0}) {S : Type} (e : E.I),
    S → CTree (OutRow E F G) B (E.O e × S)

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|F_trigger"
  F_trigger : ∀ {B : Effect.{0}} (E F G : Effect.{0}) {S : Type} (e : F.I),
    S → CTree (OutRow E F G) B (F.O e × S)

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|G_trigger"
  G_trigger : ∀ {B : Effect.{0}} (E F G : Effect.{0}) {S : Type} (e : G.I),
    S → CTree (OutRow E F G) B (G.O e × S)

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|interp_global_h"
  interp_global_h : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G] (e : (InRow E F G).I),
    global_env → CTree (OutRow E F G) B ((InRow E F G).O e × global_env)

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|interp_global"
  interp_global : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G] {X : Type},
    CTree (InRow E F G) B X → global_env → CTree (OutRow E F G) B (X × global_env)

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|interp_global_bind"
  interp_global_bind : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    (R S : Type) (t : CTree (InRow E F G) B R) (k : R → CTree (InRow E F G) B S) (s : global_env),
    eqit Eq false false (interp_global (t >>= k) s)
      (interp_global t s >>= fun p ↦ interp_global (k p.1) p.2)

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|interp_global_ret"
  interp_global_ret : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    (R : Type) (s : global_env) (x : R),
    eqit Eq false false (interp_global (CTree.ret x : CTree (InRow E F G) B R) s) (CTree.ret (x, s))

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|interp_global_Tau"
  interp_global_Tau : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    {R : Type} (t : CTree (InRow E F G) B R) (s : global_env),
    eqit Eq false false (interp_global t.guard s) (interp_global t s).guard

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|interp_global_vis_eqit"
  interp_global_vis_eqit : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    (s : global_env) (S : Type) (e : (InRow E F G).I)
    (k : (InRow E F G).O e → CTree (InRow E F G) B S),
    eqit Eq false false (interp_global (CTree.vis e k) s)
      (interp_global_h (B := B) e s >>= fun p ↦ (interp_global (k p.1) p.2).guard)

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|interp_global_vis"
  interp_global_vis : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    (s : global_env) (S : Type) (e : (InRow E F G).I)
    (k : (InRow E F G).O e → CTree (InRow E F G) B S),
    eutt Eq (interp_global (CTree.vis e k) s)
      (interp_global_h (B := B) e s >>= fun p ↦ interp_global (k p.1) p.2)

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|interp_global_trigger"
  interp_global_trigger : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    (s : global_env) (e : (InRow E F G).I),
    eutt Eq (interp_global (B := B) (CTree.trigger e) s) (interp_global_h (B := B) e s)

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|interp_global_bind_trigger_eqit"
  interp_global_bind_trigger_eqit : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    (s : global_env) (S : Type) (e : (InRow E F G).I)
    (k : (InRow E F G).O e → CTree (InRow E F G) B S),
    eqit Eq false false (interp_global (CTree.trigger e >>= k) s)
      (interp_global_h (B := B) e s >>= fun p ↦ (interp_global (k p.1) p.2).guard)

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|interp_global_bind_trigger"
  interp_global_bind_trigger : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    (s : global_env) (S : Type) (e : (InRow E F G).I)
    (k : (InRow E F G).O e → CTree (InRow E F G) B S),
    eutt Eq (interp_global (CTree.trigger e >>= k) s)
      (interp_global_h (B := B) e s >>= fun p ↦ interp_global (k p.1) p.2)

#source_check "src/rocq/Semantics/Handlers/Global.v|Vellvm.Semantics.Handlers.Global|eutt_interp_global"
  eutt_interp_global : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    {R : Type} {b : Bool} (t u : CTree (InRow E F G) B R),
    eqit Eq b b t u → ∀ s s' : global_env, s = s' → eqit Eq b b (interp_global t s) (interp_global u s')

-- A successful global write publishes the new full map, not the old map or just the binding.
example [Pa : Params] (s : global_env) (k : Vellvm.Syntax.LLVMAst.raw_id)
    (v : Vellvm.Semantics.DynamicValues.dvalue) :
    let vars := Vellvm.Syntax.RawIdMaps.RM.add k v s
    let p := Vellvm.Semantics.Handlers.Global.Worker.handle_global_debug
      (M := Logged) (E := FailureE) (B := NoChoice) (.GlobalWrite k v) s
    ∃ resume, p.next p.initial = .vis (.inr (.globals vars)) resume ∧
      p.next (resume ()) = .ret ((), vars) := ⟨_, rfl, rfl⟩
