import Vellvm.Theory.Equational.Unfold
import Vellvm.Theory.Equational.Exits

namespace Vellvm.Theory.Equational
open Semantics Semantics.Interfaces.Params Tree DynamicValues Denotation LLVMEvents
open Syntax.LLVMAst Syntax.DynamicTypes Syntax.CFG Syntax.Scope Syntax.ScopeTheory
open Coinduction
open Utils.rutt_cutoff (ruttc_bind_bchain ruttc_eutt_l)

private abbrev Edge := block_id × block_id
private abbrev Graph := ocfg dtyp
variable [Pa : Params]

/-- Separate the invariant on loop entries from the predicate at a missing block. -/
private theorem loop_post (va : Option Pa.PTR.ptr) (g : Graph) (s : Edge)
    (I P : Edge → Prop) (Q : dvalue → Prop) (hi : I s)
    (miss : ∀ i : Edge, I i → find_block g i.2 = none → P i)
    (hit : ∀ (i : Edge) (b : block dtyp), I i → find_block g i.2 = some b →
      has_post (denote_block b i.1 va) (Sum.elim (fun d ↦ I (i.2, d)) Q)) :
    has_post (denote_ocfg g va s) (Sum.elim P Q) := by
  unfold denote_ocfg Denotation.Worker.denote_ocfg Denotation.Worker.denote_ocfg_map
  apply has_post_iter hi
  rintro ⟨pred, src⟩ h
  dsimp only
  rw [ocfg_map_find_block]
  cases hb : find_block g src with
  | none => exact has_post_ret _ _ (miss (pred, src) h hb)
  | some b =>
    apply has_post_bind (hit (pred, src) b h hb)
    rintro (d | v) hv <;> exact has_post_ret _ _ hv

theorem denote_ocfg_has_post_strong (va : Option Pa.PTR.ptr) (g : Graph) (s : Edge)
    (P : Edge → Prop) (Q : dvalue → Prop) (hi : P s)
    (hb : ∀ (i : Edge) (b : block dtyp), P i → find_block g i.2 = some b →
      has_post (denote_block b i.1 va) (Sum.elim (fun d ↦ P (i.2, d)) Q)) :
    has_post (denote_ocfg g va s) (Sum.elim P Q) :=
  loop_post va g s P P Q hi (fun _ h _ ↦ h) hb

theorem denote_ocfg_has_post (va : Option Pa.PTR.ptr) (g : Graph) (s : Edge)
    (P : block_id → Prop) (Q : dvalue → Prop) (hi : s.2 ∈ inputs g)
    (hb : ∀ (i : Edge) (b : block dtyp), find_block g i.2 = some b →
      has_post (denote_block b i.1 va) (Sum.elim P Q)) :
    has_post (denote_ocfg g va s) (Sum.elim (fun e ↦ True ∧ P e.2) Q) := by
  apply loop_post va g s (fun i ↦ i.2 ∈ inputs g ∨ P i.2) _ Q (.inl hi)
  · intro i h hm
    refine ⟨trivial, h.resolve_left ?_⟩
    intro hin
    obtain ⟨b, h⟩ := find_block_in_inputs i.2 g hin
    rw [hm] at h
    contradiction
  · intro i b _ hf
    apply has_post_weaken (hb i b hf)
    rintro (d | v) hv
    · exact .inr hv
    · exact hv

def exits_in_outputs {T : Type} (g : ocfg T) : (Edge ⊕ dvalue) → Prop :=
  Sum.elim (fun i ↦ i.2 ∈ outputs g) (fun _ ↦ True)

theorem denote_ocfg_exits_in_outputs (va : Option Pa.PTR.ptr) (g : Graph) (s : Edge)
    (hi : s.2 ∈ inputs g) : has_post (denote_ocfg g va s) (exits_in_outputs g) := by
  apply has_post_weaken (denote_ocfg_has_post va g s (fun d ↦ d ∈ outputs g) (fun _ ↦ True) hi ?_)
  · rintro (d | v) h
    · exact h.2
    · trivial
  · intro i b hf
    apply has_post_weaken (denote_bk_exits_in_outputs va b i.1)
    rintro (d | v) h
    · exact In_bk_outputs i.2 d g h hf
    · trivial

theorem denote_ocfg_app_no_edges (va : Option Pa.PTR.ptr) {a b : Graph} (s : Edge)
    (miss : find_block a s.2 = none) (nr : no_reentrance a b) :
    eutt Eq (denote_ocfg (a ++ b) va s) (denote_ocfg b va s) := by
  revert s
  coinduction C hc ih
  rintro ⟨pred, src⟩ hm
  rw [ocfg_unroll va (a ++ b) pred src, ocfg_unroll va b pred src, find_block_none_app a b src hm]
  cases hf : find_block b src with
  | none => exact gfp_le_chain (.step hc) _ _ (eqit_refl true true _)
  | some bk =>
    apply ruttc_bind_bchain _ _ _ _ Eq C hc _ _ _ _ _ _ _ (strengthen (denote_bk_exits_in_outputs va bk pred))
    rintro (dst | v) _ ⟨rfl, h⟩
    · change Layer _ C _ _
      simp only [Sum.elim_inl, CTree.unfold_guard]
      exact .guard (ih (src, dst) (find_block_not_in_inputs dst a
        (no_reentrance_not_in nr dst (In_bk_outputs src dst b h hf))))
    · exact gfp_le_chain (.step hc) _ _ (eqit_refl true true _)

/-- Factor a subgraph out of the iteration. After its first miss the residual computation takes over. -/
private theorem factor (va : Option Pa.PTR.ptr) (g part : Graph)
    (rest : Edge → CFGtop (Edge ⊕ dvalue))
    (hit : ∀ src bk, find_block part src = some bk → find_block g src = some bk)
    (miss : ∀ i : Edge, find_block part i.2 = none → eutt Eq (denote_ocfg g va i) (rest i)) :
    ∀ i, eutt Eq (denote_ocfg g va i)
      (denote_ocfg part va i >>= Sum.elim rest (fun v ↦ pure (.inr v))) := by
  coinduction C hc ih
  rintro ⟨pred, src⟩
  cases hf : find_block part src with
  | none =>
    rw [ocfg_unroll va part pred src, hf]
    simp only [pure_bind, Sum.elim_inl]
    exact gfp_le_chain (.step hc) _ _ (miss (pred, src) hf)
  | some bk =>
    rw [ocfg_unroll va g pred src, hit src bk hf, ocfg_unroll va part pred src, hf]
    rw [bind_assoc]
    apply ruttc_bind_bchain _ _ _ _ Eq C hc _ _ Eq _ _ _ _ (eqit_refl true true _)
    rintro (dst | v) _ rfl
    · change Layer _ C _ _
      simp only [Sum.elim_inl, CTree.guard_bind, CTree.unfold_guard]
      exact .guard (ih (src, dst))
    · simp only [Sum.elim_inr, pure_bind]
      exact gfp_le_chain (.step hc) _ _ (eqit_refl true true _)

theorem denote_ocfg_app (va : Option Pa.PTR.ptr) {a b : Graph} (s : Edge) (nr : no_reentrance a b) :
    eutt Eq (denote_ocfg (a ++ b) va s)
      (denote_ocfg a va s >>= Sum.elim (denote_ocfg b va) (fun v ↦ pure (.inr v))) :=
  factor va (a ++ b) a (denote_ocfg b va) (fun src _ ↦ find_block_some_app a b src)
    (fun i hm ↦ denote_ocfg_app_no_edges va i hm nr) s

theorem denote_ocfg_flow_left (va : Option Pa.PTR.ptr) {a b : Graph} (s : Edge)
    (h : independent_flows a b) (hin : s.2 ∈ inputs a) :
    eutt Eq (denote_ocfg (a ++ b) va s) (denote_ocfg a va s) := by
  apply ruttc_eutt_l _ _ _ (denote_ocfg_app va s h.1)
  have hr := post_bind_eq (k := Sum.elim (denote_ocfg b va) (fun v ↦ pure (.inr v)))
    (l := pure) (denote_ocfg_exits_in_outputs va a s hin) (by
      rintro (⟨pred, src⟩ | v) hout
      · exact denote_ocfg_unfold_not_in va b pred src
          (find_block_not_in_inputs src b (no_reentrance_not_in h.2.1 src hout))
      · exact eqit_refl true true _)
  simpa only [bind_pure] using hr

theorem denote_ocfg_flow_right (va : Option Pa.PTR.ptr) {a b : Graph} (s : Edge)
    (h : independent_flows a b) (hin : s.2 ∈ inputs b) :
    eutt Eq (denote_ocfg (a ++ b) va s) (denote_ocfg b va s) :=
  denote_ocfg_app_no_edges va s (find_block_not_in_inputs s.2 a (no_duplicate_bid_not_in_l h.2.2 s.2 hin)) h.1

theorem denote_ocfg_prefix (va : Option Pa.PTR.ptr) (pre frag post : Graph) {g : Graph}
    (pred dst : block_id) (he : g = pre ++ (frag ++ post)) (wf : wf_ocfg_bid g) :
    eutt Eq (denote_ocfg g va (pred, dst))
      (denote_ocfg frag va (pred, dst) >>= Sum.elim (denote_ocfg g va) (fun v ↦ pure (.inr v))) := by
  subst g
  apply factor
  · intro src b hb
    exact find_block_app_r_wf src pre (frag ++ post) wf (find_block_some_app frag post src hb)
  · intro i _
    apply eqit_refl

end Vellvm.Theory.Equational
