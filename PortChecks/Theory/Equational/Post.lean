import PortChecks.SourceType
import Vellvm.Theory.Equational.Post

open ITree (Effect Subeffect)
open CTree (CTree)
open Vellvm Vellvm.Tree Vellvm.Semantics Vellvm.Semantics.Interfaces.Params
open LLVMEvents Vellvm.Theory.Equational Vellvm.Utils.CTreeUtil

universe u

#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|has_post_trigger_cast"
  has_post_trigger_cast : ∀ {E B : Effect.{u}} (e : E.I) (he : E.O e = PEmpty) {A : Type u}
    (P : A → Prop), has_post (trigger_cast' (B := B) e he) P

#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|has_post_ret"
  has_post_ret : ∀ {E B : Effect.{u}} {R : Type u} (r : R) (P : R → Prop),
    P r → has_post (CTree.ret r : CTree E B R) P

#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|raise_has_all_posts"
  raise_has_all_posts : ∀ {E B : Effect} {X : Type} [FailureE -< E] (s : IRString) (Q : X → Prop),
    has_post (LLVMEvents.«raise» (E := E) (B := B) s) Q

#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|raiseUB_has_all_posts"
  raiseUB_has_all_posts : ∀ {E B : Effect} {X : Type} [UBE -< E] (s : IRString) (Q : X → Prop),
    has_post (raiseUB (E := E) (B := B) s) Q

#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|raiseOOM_has_all_posts"
  raiseOOM_has_all_posts : ∀ {E B : Effect} {X : Type} [OOME -< E] (s : IRString) (Q : X → Prop),
    has_post (raiseOOM (E := E) (B := B) s) Q

#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|raiseLLVM_has_all_posts"
  raiseLLVM_has_all_posts : ∀ [Pa : Params] {E B : Effect} {X : Type} [LLVMExcE -< E]
    (ex : exc) (Q : X → Prop), has_post (raiseLLVM (E := E) (B := B) ex) Q
