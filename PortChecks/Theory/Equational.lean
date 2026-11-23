import PortChecks.SourceType
import PortChecks.Theory.Equational.Post
import PortChecks.Theory.Equational.Exits
import Vellvm.Theory.Equational

open Vellvm Vellvm.Tree Vellvm.Semantics Vellvm.Semantics.Interfaces.Params
open Vellvm.Theory.Equational DynamicValues Denotation LLVMEvents
open Syntax.LLVMAst Syntax.DynamicTypes Syntax.CFG Syntax.Scope

namespace PortChecks.EquationalTypes

private abbrev Instr := (instr_id × instr dtyp) × List (metadata dtyp)
private abbrev Term := (instr_id × terminator dtyp) × List (metadata dtyp)
private abbrev Phis := List ((local_id × phi dtyp) × List (metadata dtyp))
private abbrev Edge := block_id × block_id
private abbrev G := ocfg dtyp
private abbrev VA [p : Params] := Option p.PTR.ptr
private abbrev strict {A} [Params] (a b : CFGtop A) := eqit Eq false false a b

#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_code_nil"
  denote_code_nil : ∀ [Params] (va : VA), strict (denote_code [] va) (pure ())
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_code_app"
  denote_code_app : ∀ [Params] (va : VA) (a b : code dtyp),
    strict (denote_code (a ++ b) va) (denote_code a va >>= fun _ ↦ denote_code b va)
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_code_cons"
  denote_code_cons : ∀ [Params] (va : VA) (i : Instr) (c : code dtyp),
    strict (denote_code (i :: c) va) (denote_instr i va >>= fun _ ↦ denote_code c va)
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_code_singleton"
  denote_code_singleton : ∀ [Params] (va : VA) (i : Instr), strict (denote_code [i] va) (denote_instr i va)
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_phi_hd"
  denote_phi_hd : ∀ [Params] (bid : block_id) (e : exp dtyp) (id : local_id) (fm : List fast_math)
    (dt : dtyp) (tl : List (block_id × exp dtyp)),
    eutt Eq (denote_phi bid ((id, .Phi fm dt ((bid, e) :: tl)), []))
      (denote_exp' (some dt) e >>= fun v ↦ pure (id, v))
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_phi_tl"
  denote_phi_tl : ∀ [Params] {bid bid' : block_id} (e : exp dtyp) (id : local_id) (fm : List fast_math)
    (dt : dtyp) (tl : List (block_id × exp dtyp)), bid ≠ bid' →
    eutt Eq (denote_phi bid ((id, .Phi fm dt ((bid', e) :: tl)), [])) (denote_phi bid ((id, .Phi fm dt tl), []))
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_no_phis"
  denote_no_phis : ∀ [Params] (x : block_id), eutt Eq (denote_phis x []) (pure ())
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_block_unfold_cont"
  denote_block_unfold_cont : ∀ [Params] {R : Type} (va : VA) id (ps : Phis) (c : code dtyp)
    (tr : Term) (s : Option (List IRString)) origin (k : (block_id ⊕ dvalue) → CFGtop R),
    eutt Eq (denote_block (mk_block id ps c tr s) origin va >>= k)
      (denote_phis origin ps >>= fun _ ↦ denote_code c va >>= fun _ ↦ denote_terminator tr >>= k)
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_block_unfold"
  denote_block_unfold : ∀ [Params] (va : VA) id (ps : Phis) (c : code dtyp) (tr : Term)
    (s : Option (List IRString)) origin, eutt Eq (denote_block (mk_block id ps c tr s) origin va)
      (denote_phis origin ps >>= fun _ ↦ denote_code c va >>= fun _ ↦ denote_terminator tr)

#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_ocfg_nil"
  denote_ocfg_nil : ∀ [Params] (va : VA) (s : Edge), eutt Eq (denote_ocfg [] va s) (pure (.inl s))
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_ocfg_unfold_in"
  denote_ocfg_unfold_in : ∀ [Params] (va : VA) (g : G) (pred src : block_id) (b : block dtyp),
    find_block g src = some b → eutt Eq (denote_ocfg g va (pred, src))
      (denote_block b pred va >>= Sum.elim (fun dst ↦ denote_ocfg g va (src, dst)) (fun v ↦ pure (.inr v)))
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_ocfg_unfold_not_in"
  denote_ocfg_unfold_not_in : ∀ [Params] (va : VA) (g : G) (pred src : block_id),
    find_block g src = none → eutt Eq (denote_ocfg g va (pred, src)) (pure (.inl (pred, src)))
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_ocfg_unfold_in_euttge"
  denote_ocfg_unfold_in_euttge : ∀ [Params] (va : VA) (g : G) (pred src : block_id) (b : block dtyp),
    find_block g src = some b → euttge Eq (denote_ocfg g va (pred, src))
      (denote_block b pred va >>= Sum.elim (fun dst ↦ denote_ocfg g va (src, dst)) (fun v ↦ pure (.inr v)))
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_ocfg_unfold_in_eq_itree"
  denote_ocfg_unfold_in_eq_itree : ∀ [Params] (va : VA) (g : G) (pred src : block_id) (b : block dtyp),
    find_block g src = some b → strict (denote_ocfg g va (pred, src))
      (denote_block b pred va >>= Sum.elim (fun dst ↦ CTree.CTree.guard (denote_ocfg g va (src, dst))) (fun v ↦ pure (.inr v)))
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_ocfg_unfold_not_in_eq_itree"
  denote_ocfg_unfold_not_in_eq_itree : ∀ [Params] (va : VA) (g : G) (pred src : block_id),
    find_block g src = none → strict (denote_ocfg g va (pred, src)) (pure (.inl (pred, src)))
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_ocfg_unfold_eq_itree"
  denote_ocfg_unfold_eq_itree : ∀ [Params] (va : VA) (g : G) (pred src : block_id),
    strict (denote_ocfg g va (pred, src)) (match find_block g src with
      | some b => denote_block b pred va >>= Sum.elim (fun dst ↦ CTree.CTree.guard (denote_ocfg g va (src, dst))) (fun v ↦ pure (.inr v))
      | none => pure (.inl (pred, src)))

#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_ocfg_has_post_strong"
  denote_ocfg_has_post_strong : ∀ [Params] (va : VA) (g : G) (s : Edge) (P : Edge → Prop) (Q : dvalue → Prop),
    P s → (∀ (i : Edge) (b : block dtyp), P i → find_block g i.2 = some b →
      has_post (denote_block b i.1 va) (Sum.elim (fun d ↦ P (i.2, d)) Q)) →
    has_post (denote_ocfg g va s) (Sum.elim P Q)
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_ocfg_has_post"
  denote_ocfg_has_post : ∀ [Params] (va : VA) (g : G) (s : Edge) (P : block_id → Prop) (Q : dvalue → Prop),
    s.2 ∈ inputs g → (∀ (i : Edge) (b : block dtyp), find_block g i.2 = some b →
      has_post (denote_block b i.1 va) (Sum.elim P Q)) →
    has_post (denote_ocfg g va s) (Sum.elim (fun edge ↦ True ∧ P edge.2) Q)
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|exits_in_outputs"
  exits_in_outputs : ∀ [Params] {T : Type}, ocfg T → (Edge ⊕ dvalue) → Prop
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_ocfg_exits_in_outputs"
  denote_ocfg_exits_in_outputs : ∀ [Params] (va : VA) (g : G) (s : Edge),
    s.2 ∈ inputs g → has_post (denote_ocfg g va s) (exits_in_outputs g)
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_ocfg_app_no_edges"
  denote_ocfg_app_no_edges : ∀ [Params] (va : VA) {a b : G} (s : Edge),
    find_block a s.2 = none → no_reentrance a b → eutt Eq (denote_ocfg (a ++ b) va s) (denote_ocfg b va s)
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_ocfg_app"
  denote_ocfg_app : ∀ [Params] (va : VA) {a b : G} (s : Edge), no_reentrance a b →
    eutt Eq (denote_ocfg (a ++ b) va s)
      (denote_ocfg a va s >>= Sum.elim (denote_ocfg b va) (fun v ↦ pure (.inr v)))
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_ocfg_flow_left"
  denote_ocfg_flow_left : ∀ [Params] (va : VA) {a b : G} (s : Edge), independent_flows a b →
    s.2 ∈ inputs a → eutt Eq (denote_ocfg (a ++ b) va s) (denote_ocfg a va s)
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_ocfg_flow_right"
  denote_ocfg_flow_right : ∀ [Params] (va : VA) {a b : G} (s : Edge), independent_flows a b →
    s.2 ∈ inputs b → eutt Eq (denote_ocfg (a ++ b) va s) (denote_ocfg b va s)
#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_ocfg_prefix"
  denote_ocfg_prefix : ∀ [Params] (va : VA) (pre frag post : G) {g : G} (pred dst : block_id),
    g = pre ++ (frag ++ post) → wf_ocfg_bid g → eutt Eq (denote_ocfg g va (pred, dst))
      (denote_ocfg frag va (pred, dst) >>= Sum.elim (denote_ocfg g va) (fun v ↦ pure (.inr v)))

end PortChecks.EquationalTypes
