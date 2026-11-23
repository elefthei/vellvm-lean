import Vellvm.Semantics.Denotation
import Vellvm.Syntax.ScopeTheory
import Vellvm.Tree.StrictEq

namespace Vellvm.Theory.Equational
open Semantics Semantics.Interfaces.Params Tree Syntax.LLVMAst Syntax.DynamicTypes Syntax.CFG
open Syntax.ScopeTheory DynamicValues Denotation LLVMEvents
open Utils.ListUtil (map_monad loop_monad eqit_bind)
open CTree (CTree)

variable [Pa : Params]

private abbrev VA [p : Params] := Option p.PTR.ptr
private abbrev Instr := (instr_id × instr dtyp) × List (metadata dtyp)
private abbrev Term := (instr_id × terminator dtyp) × List (metadata dtyp)
private abbrev Phis := List ((local_id × phi dtyp) × List (metadata dtyp))

theorem denote_code_nil (va : VA) : eqit Eq false false (denote_code [] va) (pure ()) :=
  eqit_refl false false _

theorem denote_code_cons (va : VA) (i : Instr) (c : code dtyp) :
    eqit Eq false false (denote_code (i :: c) va) (denote_instr i va >>= fun _ ↦ denote_code c va) :=
  eqit_refl false false _

theorem denote_code_app (va : VA) (a b : code dtyp) : eqit Eq false false (denote_code (a ++ b) va)
    (denote_code a va >>= fun _ ↦ denote_code b va) := by
  apply eqit_strict_iff_eq.mpr
  induction a with
  | nil =>
    change denote_code b va = ((pure () : CFGtop Unit) >>= fun _ ↦ denote_code b va)
    rw [pure_bind]
  | cons i c ih =>
    change (denote_instr i va >>= fun _ ↦ denote_code (c ++ b) va) =
      ((denote_instr i va >>= fun _ ↦ denote_code c va) >>= _)
    rw [ih, bind_assoc]

theorem denote_code_singleton (va : VA) (i : Instr) :
    eqit Eq false false (denote_code [i] va) (denote_instr i va) := by
  apply eqit_strict_iff_eq.mpr
  change (denote_instr i va >>= pure) = _
  simp

theorem denote_phi_hd (bid : block_id) (e : exp dtyp) (id : local_id) (fm : List fast_math)
    (dt : dtyp) (tl : List (block_id × exp dtyp)) :
    eutt Eq (denote_phi bid ((id, .Phi fm dt ((bid, e) :: tl)), []))
      (denote_exp' (some dt) e >>= fun v ↦ pure (id, v)) := by
  unfold denote_phi Denotation.Worker.denote_phi
  simp only [Utils.Assoc.assoc_hd]
  change eutt Eq (pure () >>= fun _ ↦ _) _
  rw [pure_bind]
  apply eqit_refl

theorem denote_phi_tl {bid bid' : block_id} (e : exp dtyp) (id : local_id) (fm : List fast_math)
    (dt : dtyp) (tl : List (block_id × exp dtyp)) (h : bid ≠ bid') :
    eutt Eq (denote_phi bid ((id, .Phi fm dt ((bid', e) :: tl)), []))
      (denote_phi bid ((id, .Phi fm dt tl), [])) := by
  unfold denote_phi Denotation.Worker.denote_phi
  simp only [Utils.Assoc.assoc_tl _ _ _ _ h]
  apply eqit_refl

theorem denote_no_phis (x : block_id) : eutt Eq (denote_phis x []) (pure ()) := by
  change eutt Eq (pure ([] : List (local_id × dvalue)) >>= _) _
  rw [pure_bind]
  apply eqit_refl

theorem denote_block_unfold (va : VA) (id : block_id) (phis : Phis) (c : code dtyp) (t : Term)
    (s : Option (List IRString)) (origin : block_id) :
    eutt Eq (denote_block (mk_block id phis c t s) origin va)
      (denote_phis origin phis >>= fun _ ↦ denote_code c va >>= fun _ ↦ denote_terminator t) :=
  eqit_refl true true _

theorem denote_block_unfold_cont {R : Type} (va : VA) (id : block_id) (phis : Phis) (c : code dtyp)
    (t : Term) (s : Option (List IRString)) (origin : block_id) (k : (block_id ⊕ dvalue) → CFGtop R) :
    eutt Eq (denote_block (mk_block id phis c t s) origin va >>= k)
      (denote_phis origin phis >>= fun _ ↦ denote_code c va >>= fun _ ↦ denote_terminator t >>= k) := by
  change eutt Eq ((denote_phis origin phis >>= fun _ ↦ denote_code c va >>= fun _ ↦ denote_terminator t) >>= k) _
  simp only [bind_assoc]
  apply eqit_refl

/-- Exact iter unfolding, with a guard only when control transfers to another label. -/
theorem ocfg_unroll (va : VA) (g : ocfg dtyp) (pred src : block_id) :
    denote_ocfg g va (pred, src) = match find_block g src with
      | some b => denote_block b pred va >>= Sum.elim
        (fun d ↦ CTree.guard (denote_ocfg g va (src, d))) (fun v ↦ pure (.inr v))
      | none => pure (.inl (pred, src)) := by
  unfold denote_ocfg Denotation.Worker.denote_ocfg Denotation.Worker.denote_ocfg_map
  change CTree.iter _ (pred, src) = _
  rw [CTree.unfold_iter]
  dsimp only
  rw [ocfg_map_find_block]
  cases find_block g src with
  | none => apply pure_bind
  | some b =>
    dsimp only
    rw [bind_assoc]
    congr 1
    funext x
    cases x <;> apply pure_bind

theorem denote_ocfg_unfold_eq_itree (va : VA) (g : ocfg dtyp) (pred src : block_id) :
    eqit Eq false false (denote_ocfg g va (pred, src)) (match find_block g src with
      | some b => denote_block b pred va >>= Sum.elim
        (fun d ↦ CTree.guard (denote_ocfg g va (src, d))) (fun v ↦ pure (.inr v))
      | none => pure (.inl (pred, src))) := eqit_strict_iff_eq.mpr (ocfg_unroll va g pred src)

theorem denote_ocfg_unfold_in_eq_itree (va : VA) (g : ocfg dtyp) (pred src : block_id)
    (b : block dtyp) (h : find_block g src = some b) : eqit Eq false false (denote_ocfg g va (pred, src))
      (denote_block b pred va >>= Sum.elim (fun d ↦ CTree.guard (denote_ocfg g va (src, d)))
        (fun v ↦ pure (.inr v))) := by
  apply eqit_strict_iff_eq.mpr
  simpa only [h] using ocfg_unroll va g pred src

theorem denote_ocfg_unfold_not_in_eq_itree (va : VA) (g : ocfg dtyp) (pred src : block_id)
    (h : find_block g src = none) :
    eqit Eq false false (denote_ocfg g va (pred, src)) (pure (.inl (pred, src))) := by
  apply eqit_strict_iff_eq.mpr
  simpa only [h] using ocfg_unroll va g pred src

private theorem ocfg_hit (right : Bool) (va : VA) (g : ocfg dtyp) (pred src : block_id)
    (b : block dtyp) (h : find_block g src = some b) : eqit Eq true right (denote_ocfg g va (pred, src))
      (denote_block b pred va >>= Sum.elim (fun d ↦ denote_ocfg g va (src, d)) (fun v ↦ pure (.inr v))) := by
  rw [eqit_strict_iff_eq.mp (denote_ocfg_unfold_in_eq_itree va g pred src b h)]
  apply eqit_bind (RR := Eq) _ _ _ (eqit_refl true right _)
  rintro (d | v) _ rfl
  · exact Related.guard_left rfl (eqit_refl true right _)
  · exact eqit_refl true right _

theorem denote_ocfg_unfold_in (va : VA) (g : ocfg dtyp) (pred src : block_id)
    (b : block dtyp) (h : find_block g src = some b) : eutt Eq (denote_ocfg g va (pred, src))
      (denote_block b pred va >>= Sum.elim (fun d ↦ denote_ocfg g va (src, d)) (fun v ↦ pure (.inr v))) :=
  ocfg_hit true va g pred src b h

theorem denote_ocfg_unfold_in_euttge (va : VA) (g : ocfg dtyp) (pred src : block_id)
    (b : block dtyp) (h : find_block g src = some b) : euttge Eq (denote_ocfg g va (pred, src))
      (denote_block b pred va >>= Sum.elim (fun d ↦ denote_ocfg g va (src, d)) (fun v ↦ pure (.inr v))) :=
  ocfg_hit false va g pred src b h

theorem denote_ocfg_unfold_not_in (va : VA) (g : ocfg dtyp) (pred src : block_id)
    (h : find_block g src = none) : eutt Eq (denote_ocfg g va (pred, src)) (pure (.inl (pred, src))) := by
  rw [eqit_strict_iff_eq.mp (denote_ocfg_unfold_not_in_eq_itree va g pred src h)]
  apply eqit_refl

theorem denote_ocfg_nil (va : VA) (s : block_id × block_id) :
    eutt Eq (denote_ocfg [] va s) (pure (.inl s)) := denote_ocfg_unfold_not_in va [] s.1 s.2 rfl

end Vellvm.Theory.Equational
