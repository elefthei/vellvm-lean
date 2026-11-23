import PortChecks.SourceType
import Vellvm.Semantics.Handlers.Local

open ITree (Effect Subeffect)
open CTree (CTree)
open Vellvm.Tree Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.LLVMEvents
open Vellvm.Semantics.Handlers.Local

private abbrev InRow [Params] (E F G : Effect) := E ⊕ₑ F ⊕ₑ LocalE ⊕ₑ G
private abbrev OutRow (E F G : Effect) := E ⊕ₑ F ⊕ₑ G

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|local_env"
  local_env : ∀ [Pa : Params], Type

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|handle_local"
  handle_local : ∀ [Pa : Params] {E B : Effect} [FailureE -< E] (e : LocalE.I),
    local_env → CTree E B (LocalE.O e × local_env)

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|debug_locals"
  debug_locals : ∀ [Pa : Params], Type

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|mk_debug_locals"
  mk_debug_locals : ∀ [Pa : Params],
    (local_env → Unit) → (Unit → local_env) → debug_locals

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|locals_set"
  locals_set : ∀ [Pa : Params], debug_locals → local_env → Unit

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|locals_get"
  locals_get : ∀ [Pa : Params], debug_locals → Unit → local_env

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|locals_object"
  locals_object : ∀ [Pa : Params], debug_locals

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|update_locals_ref"
  update_locals_ref : ∀ [Pa : Params] {E B : Effect} [FailureE -< E],
    LocalE.I → local_env → CTree E B (Unit × local_env)

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|handle_local_debug"
  handle_local_debug : ∀ [Pa : Params] {E B : Effect} [FailureE -< E] (e : LocalE.I),
    local_env → CTree E B (LocalE.O e × local_env)

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|E_trigger"
  E_trigger : ∀ {B : Effect.{0}} (E F G : Effect.{0}) {S : Type} (e : E.I),
    S → CTree (OutRow E F G) B (E.O e × S)

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|F_trigger"
  F_trigger : ∀ {B : Effect.{0}} (E F G : Effect.{0}) {S : Type} (e : F.I),
    S → CTree (OutRow E F G) B (F.O e × S)

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|G_trigger"
  G_trigger : ∀ {B : Effect.{0}} (E F G : Effect.{0}) {S : Type} (e : G.I),
    S → CTree (OutRow E F G) B (G.O e × S)

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|interp_local_h"
  interp_local_h : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G] (e : (InRow E F G).I),
    local_env → CTree (OutRow E F G) B ((InRow E F G).O e × local_env)

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|interp_local"
  interp_local : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G] {X : Type},
    CTree (InRow E F G) B X → local_env → CTree (OutRow E F G) B (X × local_env)

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|interp_local_bind"
  interp_local_bind : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    (R S : Type) (t : CTree (InRow E F G) B R) (k : R → CTree (InRow E F G) B S) (s : local_env),
    eqit Eq false false (interp_local (t >>= k) s)
      (interp_local t s >>= fun p ↦ interp_local (k p.1) p.2)

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|interp_local_ret"
  interp_local_ret : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    (R : Type) (s : local_env) (x : R),
    eqit Eq false false (interp_local (CTree.ret x : CTree (InRow E F G) B R) s) (CTree.ret (x, s))

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|interp_local_Tau"
  interp_local_Tau : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    {R : Type} (t : CTree (InRow E F G) B R) (s : local_env),
    eqit Eq false false (interp_local t.guard s) (interp_local t s).guard

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|interp_local_vis_eqit"
  interp_local_vis_eqit : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    (s : local_env) (S : Type) (e : (InRow E F G).I)
    (k : (InRow E F G).O e → CTree (InRow E F G) B S),
    eqit Eq false false (interp_local (CTree.vis e k) s)
      (interp_local_h (B := B) e s >>= fun p ↦ (interp_local (k p.1) p.2).guard)

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|interp_local_vis"
  interp_local_vis : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    (s : local_env) (S : Type) (e : (InRow E F G).I)
    (k : (InRow E F G).O e → CTree (InRow E F G) B S),
    eutt Eq (interp_local (CTree.vis e k) s)
      (interp_local_h (B := B) e s >>= fun p ↦ interp_local (k p.1) p.2)

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|interp_local_trigger"
  interp_local_trigger : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    (s : local_env) (e : (InRow E F G).I),
    eutt Eq (interp_local (B := B) (CTree.trigger e) s) (interp_local_h (B := B) e s)

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|interp_local_bind_trigger_eqit"
  interp_local_bind_trigger_eqit : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    (s : local_env) (S : Type) (e : (InRow E F G).I)
    (k : (InRow E F G).O e → CTree (InRow E F G) B S),
    eqit Eq false false (interp_local (CTree.trigger e >>= k) s)
      (interp_local_h (B := B) e s >>= fun p ↦ (interp_local (k p.1) p.2).guard)

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|interp_local_trigger_bind"
  interp_local_trigger_bind : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    (s : local_env) (S : Type) (e : (InRow E F G).I)
    (k : (InRow E F G).O e → CTree (InRow E F G) B S),
    eutt Eq (interp_local (CTree.trigger e >>= k) s)
      (interp_local_h (B := B) e s >>= fun p ↦ interp_local (k p.1) p.2)

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|Proper_interp_local"
  Proper_interp_local : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    {R : Type} {b : Bool} (t u : CTree (InRow E F G) B R),
    eqit Eq b b t u → ∀ s : local_env, eutt Eq (interp_local t s) (interp_local u s)

#source_check "src/rocq/Semantics/Handlers/Local.v|Vellvm.Semantics.Handlers.Local|Proper_interp_local_pointwise"
  Proper_interp_local_pointwise : ∀ [Pa : Params] {E F G B : Effect} [FailureE -< G]
    {R : Type} {b : Bool} (t u : CTree (InRow E F G) B R),
    eqit Eq b b t u → ∀ s s' : local_env, s = s' → eqit Eq b b (interp_local t s) (interp_local u s')
