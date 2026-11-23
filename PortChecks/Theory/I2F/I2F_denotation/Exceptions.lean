import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_denotation.Exceptions

namespace PortChecks.I2FDenotationExceptions
open Vellvm Vellvm.Tree Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.LLVMEvents
open Vellvm.Semantics.Denotation Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_denotation
open Vellvm.Numeric.Rocqlib (option_rel)
open Vellvm.Utils.rutt_cutoff (sum_rel)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|unfold_run_exc_strong"
  unfold_run_exc_strong : ∀ [Pa : Params] {A : Type} (t : CFGtop A),
    eqit Eq false false (run_exc t) (match t.unfold with
      | .ret a => .ret (.inr a)
      | .guard u => .guard (run_exc u)
      | .stuck => .stuck
      | .step u => .step (.guard (run_exc u))
      | .br c _ => nomatch c
      | .vis e k => match exc_of_event e with
        | some x => .ret (.inl x)
        | none => .vis e fun a ↦ .guard (run_exc (k a)))

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|cutUB_exc_of_event"
  cutUB_exc_of_event : ∀ [Pa : Params] (e : CFGEtop.I), cutUB (E := CFGEtop) e → exc_of_event e = none

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|cutOOM_exc_of_event"
  cutOOM_exc_of_event : ∀ [Pa : Params] (e : CFGEtop.I), cutOOM (E := CFGEtop) e → exc_of_event e = none

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2FE_CFG_exc_of_event"
  I2FE_CFG_exc_of_event : ∀ (e : (@CFGEtop PInf).I) (f : (@CFGEtop PFin).I), I2FE_CFG e f →
    option_rel I2F_dvalue (@exc_of_event PInf e) (@exc_of_event PFin f)

#source_check "src/rocq/Theory/I2F/I2F_denotation.v|Vellvm.Theory.I2F.I2F_denotation|I2F_run_exc"
  I2F_run_exc : ∀ {X Y : Type} {RR : X → Y → Prop} (t : @CFGtop PInf X) (s : @CFGtop PFin Y),
    ruttc cutUB cutOOM I2FE_CFG I2FA_CFG RR t s →
    ruttc cutUB cutOOM I2FE_CFG I2FA_CFG (sum_rel I2F_dvalue RR) (@run_exc PInf X t) (@run_exc PFin Y s)

end PortChecks.I2FDenotationExceptions
