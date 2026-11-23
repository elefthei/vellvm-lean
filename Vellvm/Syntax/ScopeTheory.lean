/- Copyright (c) 2026 Vellvm developers. Distributed under the MIT License. -/
module

public import Vellvm.Syntax.CFG
public import Vellvm.Syntax.Scope
public import Vellvm.Syntax.TypToDtyp

/-! Block labels, lookup, predecessor edges, and preservation by type conversion. -/

@[expose] public section
namespace Vellvm.Syntax.ScopeTheory

open LLVMAst CFG Scope RawIdMaps TypToDtyp Numeric.Rocqlib

universe u
variable {T : Type}

theorem app_snoc_app {A : Type u} (l l' : List A) (x : A) :
    (l ++ [x]) ++ l' = l ++ (x :: l') := by simp

theorem inputs_app (l l' : ocfg T) : inputs (l ++ l') = inputs l ++ inputs l' :=
  List.map_append

theorem inputs_cons (b : block T) (l : ocfg T) : inputs (b :: l) = b.blk_id :: inputs l := rfl

theorem outputs_acc (bks : ocfg T) (acc : List block_id) :
    bks.foldl (fun a bk ↦ a ++ successors bk) acc =
    acc ++ bks.foldl (fun a bk ↦ a ++ successors bk) [] := by
  simp [List.foldl_append_eq_append]

theorem outputs_app (l l' : ocfg T) : outputs (l ++ l') = outputs l ++ outputs l' := by
  unfold outputs
  rw [List.foldl_append, outputs_acc]

theorem outputs_cons (b : block T) (l : ocfg T) : outputs (b :: l) = successors b ++ outputs l :=
  outputs_acc l (successors b)

theorem wf_ocfg_bid_nil : wf_ocfg_bid ([] : ocfg T) := List.nodup_nil

theorem wf_ocfg_bid_cons ⦃b : block T⦄ ⦃bs : ocfg T⦄ (h : wf_ocfg_bid (b :: bs)) :
    wf_ocfg_bid bs := (List.nodup_cons.mp h).2

theorem wf_ocfg_bid_cons_not_in ⦃b : block T⦄ ⦃bs : ocfg T⦄ (h : wf_ocfg_bid (b :: bs)) :
    b.blk_id ∉ inputs bs := (List.nodup_cons.mp h).1

theorem wf_ocfg_bid_singleton (b : block T) : wf_ocfg_bid [b] := by
  simp [wf_ocfg_bid, inputs, list_norepet]

theorem wf_ocfg_bid_cons' (b : block T) ⦃bks : ocfg T⦄ (h : b.blk_id ∉ inputs bks)
    (hw : wf_ocfg_bid bks) : wf_ocfg_bid (b :: bks) := List.nodup_cons.mpr ⟨h, hw⟩

theorem wf_ocfg_bid_app_r (bs₁ bs₂ : ocfg T) (h : wf_ocfg_bid (bs₁ ++ bs₂)) :
    wf_ocfg_bid bs₂ := by
  unfold wf_ocfg_bid at h ⊢
  rw [inputs_app] at h
  exact list_norepet_append_right _ _ h

theorem wf_ocfg_bid_app_l (bs₁ bs₂ : ocfg T) (h : wf_ocfg_bid (bs₁ ++ bs₂)) :
    wf_ocfg_bid bs₁ := by
  unfold wf_ocfg_bid at h ⊢
  rw [inputs_app] at h
  exact list_norepet_append_left _ _ h

theorem wf_ocfg_commut (G G' : ocfg T) (h : wf_ocfg_bid (G ++ G')) : wf_ocfg_bid (G' ++ G) := by
  simp only [wf_ocfg_bid, inputs_app] at h ⊢
  exact list_norepet_append_commut _ _ h

theorem wf_ocfg_commut_hd ⦃bk bk' : block T⦄ ⦃G : List (block T)⦄ :
    wf_ocfg_bid (bk :: bk' :: G) → wf_ocfg_bid (bk' :: bk :: G) :=
  (List.Perm.swap bk'.blk_id bk.blk_id (inputs G)).nodup_iff.mp

theorem wf_ocfg_map (f : block T → block T) (G : ocfg T) (h : ∀ bk, (f bk).blk_id = bk.blk_id) :
    wf_ocfg_bid G ↔ wf_ocfg_bid (G.map f) := by
  simp [wf_ocfg_bid, inputs, List.map_map, Function.comp_def, h]

theorem wf_ocfg_bid_distinct_labels (bks₁ bks₂ : ocfg T) ⦃b₁ b₂ : block_id⦄
    (h : wf_ocfg_bid (bks₁ ++ bks₂)) (h₁ : b₁ ∈ inputs bks₁) (h₂ : b₂ ∈ inputs bks₂) :
    b₁ ≠ b₂ := by
  rw [wf_ocfg_bid, inputs_app, list_norepet_app] at h
  exact h.2.2 b₁ b₂ h₁ h₂

theorem wf_ocfg_bid_app_not_in_l (id : block_id) (bs bs' : ocfg T) (hin : id ∈ inputs bs)
    (h : wf_ocfg_bid (bs' ++ bs)) : id ∉ inputs bs' :=
  fun h' ↦ wf_ocfg_bid_distinct_labels bs' bs h h' hin rfl

theorem wf_ocfg_app_not_in_r (id : block_id) (bs bs' : ocfg T) :
    id ∈ inputs bs → wf_ocfg_bid (bs' ++ bs) → id ∉ inputs bs' :=
  wf_ocfg_bid_app_not_in_l id bs bs'

theorem no_reentrance_not_in ⦃bks₁ bks₂ : ocfg T⦄ (h : no_reentrance bks₁ bks₂) (x : block_id) :
    x ∈ outputs bks₂ → x ∉ inputs bks₁ := list_disjoint_notin x h

theorem no_reentrance_app_l (bks₁ bks₁' bks₂ : ocfg T) :
    no_reentrance (bks₁ ++ bks₁') bks₂ ↔ no_reentrance bks₁ bks₂ ∧ no_reentrance bks₁' bks₂ := by
  simp only [no_reentrance, inputs_app, list_disjoint, List.mem_append]
  grind

theorem no_reentrance_app_r (bks₁ bks₂ bks₂' : ocfg T) :
    no_reentrance bks₁ (bks₂ ++ bks₂') ↔ no_reentrance bks₁ bks₂ ∧ no_reentrance bks₁ bks₂' := by
  simp only [no_reentrance, outputs_app, list_disjoint, List.mem_append]
  grind

theorem no_duplicate_bid_not_in_l ⦃bks₁ bks₂ : ocfg T⦄ (h : no_duplicate_bid bks₁ bks₂)
    (x : block_id) : x ∈ inputs bks₂ → x ∉ inputs bks₁ := list_disjoint_notin x (list_disjoint_sym h)

theorem no_duplicate_bid_not_in_r ⦃bks₁ bks₂ : ocfg T⦄ (h : no_duplicate_bid bks₁ bks₂)
    (x : block_id) : x ∈ inputs bks₁ → x ∉ inputs bks₂ := list_disjoint_notin x h

theorem independent_flows_no_reentrance_l ⦃bks₁ bks₂ : ocfg T⦄ (h : independent_flows bks₁ bks₂) :
    no_reentrance bks₁ bks₂ := h.1

theorem independent_flows_no_reentrance_r ⦃bks₁ bks₂ : ocfg T⦄ (h : independent_flows bks₁ bks₂) :
    no_reentrance bks₂ bks₁ := h.2.1

theorem independent_flows_no_duplicate_bid ⦃bks₁ bks₂ : ocfg T⦄ (h : independent_flows bks₁ bks₂) :
    no_duplicate_bid bks₁ bks₂ := h.2.2

theorem free_in_cfg_cons ⦃b : block T⦄ ⦃bs : ocfg T⦄ ⦃id : block_id⦄ (h : free_in_cfg (b :: bs) id) :
    free_in_cfg bs id := fun hin ↦ h (List.mem_cons_of_mem _ hin)

theorem free_in_cfg_app (bks₁ bks₂ : ocfg T) (b : block_id) :
    free_in_cfg (bks₁ ++ bks₂) b ↔ free_in_cfg bks₁ b ∧ free_in_cfg bks₂ b := by
  simp [free_in_cfg, inputs_app]

theorem find_block_nil (b : block_id) : find_block ([] : ocfg T) b = none := rfl

theorem find_block_eq ⦃x : block_id⦄ (b : block T) (bs : ocfg T) (h : b.blk_id = x) :
    find_block (b :: bs) x = some b := by simp [find_block, h]

theorem find_block_ineq ⦃x : block_id⦄ (b : block T) (bs : ocfg T) (h : b.blk_id ≠ x) :
    find_block (b :: bs) x = find_block bs x := by simp [find_block, h]

theorem find_block_In' (G : List (block T)) (b : block_id) ⦃bk : block T⦄
    (h : find_block G b = some bk) : bk ∈ G := List.mem_of_find?_eq_some h

theorem find_block_In (G : List (block T)) ⦃bk : block T⦄ :
    find_block G bk.blk_id = some bk → bk ∈ G := fun h ↦ find_block_In' G bk.blk_id h

theorem find_block_has_id (G : ocfg T) (b : block_id) ⦃bk : block T⦄
    (h : find_block G b = some bk) : b = bk.blk_id := by
  unfold find_block at h
  have he := List.find?_some h
  simpa using (of_decide_eq_true he).symm

theorem find_block_Some_In_inputs (bks : ocfg T) (b : block_id) ⦃bk : block T⦄
    (h : find_block bks b = some bk) : b ∈ inputs bks :=
  List.mem_map.mpr ⟨bk, find_block_In' bks b h, (find_block_has_id bks b h).symm⟩

theorem find_block_in_inputs (id : block_id) (bks : ocfg T) (hin : id ∈ inputs bks) :
    ∃ bk, find_block bks id = some bk := by
  obtain ⟨bk, hb, he⟩ := List.mem_map.mp hin
  apply Option.isSome_iff_exists.mp
  apply List.find?_isSome.mpr
  exact ⟨bk, hb, by simp [he]⟩

theorem In_find_block (bks : ocfg T) (bk : block T) (h : bk ∈ bks) :
    ∃ bk', find_block bks bk.blk_id = some bk' :=
  find_block_in_inputs bk.blk_id bks (List.mem_map_of_mem h)

theorem find_block_not_in_inputs (bid : block_id) (l : ocfg T) (h : bid ∉ inputs l) :
    find_block l bid = none := by
  cases he : find_block l bid with
  | none => rfl
  | some bk => exact False.elim (h (find_block_Some_In_inputs l bid he))

theorem find_block_free_id ⦃G : ocfg T⦄ ⦃id : block_id⦄ :
    free_in_cfg G id → find_block G id = none := find_block_not_in_inputs id G

theorem In_bk_outputs (bid br : block_id) ⦃b : block T⦄ (l : ocfg T) (hs : br ∈ successors b)
    (h : find_block l bid = some b) : br ∈ outputs l := by
  rw [outputs, List.foldl_append_eq_append, List.nil_append]
  exact List.mem_flatten.mpr ⟨successors b, List.mem_map_of_mem (find_block_In' l bid h), hs⟩

theorem ocfg_map_find_block (bks : ocfg T) (b : block_id) :
    RM.find b (ocfg_map bks) = find_block bks b := by
  induction bks with
  | nil => exact RM.find_empty b
  | cons bk bs ih =>
    change RM.find b (RM.add bk.blk_id bk (ocfg_map bs)) = _
    rw [RM.find_add, ih]
    by_cases he : bk.blk_id = b
    · simp [he.symm, find_block_eq bk bs rfl]
    · simp [Ne.symm he, find_block_ineq bk bs he]

theorem wf_ocfg_bid_In_is_found ⦃bks : ocfg T⦄ (bk : block T) (hw : wf_ocfg_bid bks)
    (hin : bk ∈ bks) : find_block bks bk.blk_id = some bk := by
  induction bks with
  | nil => cases hin
  | cons hd bs ih =>
    rcases List.mem_cons.mp hin with rfl | hin
    · exact find_block_eq _ _ rfl
    · have hn : hd.blk_id ≠ bk.blk_id := fun he ↦
        wf_ocfg_bid_cons_not_in hw (he ▸ List.mem_map_of_mem hin)
      rw [find_block_ineq hd bs hn]
      exact ih (wf_ocfg_bid_cons hw) hin

theorem find_block_none_app (bks₁ bks₂ : ocfg T) (bid : block_id) (h : find_block bks₁ bid = none) :
    find_block (bks₁ ++ bks₂) bid = find_block bks₂ bid := by
  unfold find_block at h ⊢
  rw [List.find?_append, h]; rfl

theorem find_block_some_app (bks₁ bks₂ : ocfg T) ⦃bk : block T⦄ (bid : block_id)
    (h : find_block bks₁ bid = some bk) : find_block (bks₁ ++ bks₂) bid = some bk := by
  unfold find_block at h ⊢
  rw [List.find?_append, h]; rfl

theorem wf_ocfg_bid_find_None_app_l (bks₁ bks₂ : ocfg T) (b : block_id) ⦃bk : block T⦄
    (hw : wf_ocfg_bid (bks₁ ++ bks₂)) (h : find_block bks₂ b = some bk) : find_block bks₁ b = none :=
  find_block_not_in_inputs b bks₁
    (wf_ocfg_bid_app_not_in_l b bks₂ bks₁ (find_block_Some_In_inputs bks₂ b h) hw)

theorem find_block_app_r_wf (x : block_id) ⦃b : block T⦄ (bs₁ bs₂ : ocfg T)
    (hw : wf_ocfg_bid (bs₁ ++ bs₂)) (h : find_block bs₂ x = some b) :
    find_block (bs₁ ++ bs₂) x = some b :=
  (find_block_none_app bs₁ bs₂ x (wf_ocfg_bid_find_None_app_l bs₁ bs₂ x hw h)).trans h

theorem find_block_app_l_wf (x : block_id) ⦃b : block T⦄ (bs₁ bs₂ : ocfg T)
    (_ : wf_ocfg_bid (bs₁ ++ bs₂)) : find_block bs₁ x = some b → find_block (bs₁ ++ bs₂) x = some b :=
  find_block_some_app bs₁ bs₂ x

theorem find_block_tail_wf (x : block_id) ⦃b b' : block T⦄ ⦃bs : ocfg T⦄ :
    wf_ocfg_bid (b :: bs) → find_block bs x = some b' → find_block (b :: bs) x = some b' :=
  find_block_app_r_wf x [b] bs

theorem wf_ocfg_cons_not_in_tail ⦃bk : block T⦄ ⦃G : List (block T)⦄ (h : wf_ocfg_bid (bk :: G)) :
    find_block G bk.blk_id = none := find_block_not_in_inputs _ _ (wf_ocfg_bid_cons_not_in h)

theorem wf_ocfg_bid_find_block_unique ⦃bks : ocfg T⦄ ⦃bk₁ : block T⦄ (b₁ : block_id) ⦃bk₂ : block T⦄
    (_ : wf_ocfg_bid bks) (h₁ : find_block bks b₁ = some bk₁) (h₂ : find_block bks b₁ = some bk₂) :
    bk₁ = bk₂ := Option.some.inj (h₁.symm.trans h₂)

theorem find_block_map (f : block T → block T) (G : List (block T)) (b : block_id)
    (h : ∀ bk, (f bk).blk_id = bk.blk_id) : find_block (G.map f) b = option_map f (find_block G b) := by
  simp [find_block, List.find?_map, Function.comp_def, h, option_map]

theorem find_block_map_some (f : block T → block T) (G : List (block T)) (b : block_id) ⦃bk : block T⦄
    (h : ∀ bk, (f bk).blk_id = bk.blk_id) (hf : find_block G b = some bk) :
    find_block (G.map f) b = some (f bk) := by rw [find_block_map f G b h, hf]; rfl

theorem find_block_map_none (f : block T → block T) (G : List (block T)) (b : block_id)
    (h : ∀ bk, (f bk).blk_id = bk.blk_id) (hf : find_block G b = none) :
    find_block (G.map f) b = none := by rw [find_block_map f G b h, hf]; rfl

def predecessors_aux (b : block_id) (G : ocfg T) (acc : List block_id) : List block_id :=
  G.foldl (fun acc bk ↦ if is_predecessor b bk then bk.blk_id :: acc else acc) acc

private theorem predecessors_aux_eq (t : block_id) (G : ocfg T) (acc : List block_id) :
    predecessors_aux t G acc = (G.filter (is_predecessor t)).reverse.map blk_id ++ acc := by
  induction G generalizing acc with
  | nil => rfl
  | cons bk bs ih =>
    change predecessors_aux t bs (if is_predecessor t bk then bk.blk_id :: acc else acc) = _
    rw [ih]
    cases hb : is_predecessor t bk <;> simp [hb]

theorem predecessors_app (bks bks' : ocfg T) (f : block_id) :
    predecessors f (bks ++ bks') = predecessors f bks' ++ predecessors f bks := by
  change predecessors_aux f (bks ++ bks') [] = predecessors_aux f bks' [] ++ predecessors_aux f bks []
  simp [predecessors_aux_eq]

theorem predecessors_cons (bks : ocfg T) (bk : block T) (f : block_id) :
    predecessors f (bk :: bks) = predecessors f bks ++ predecessors f [bk] :=
  predecessors_app [bk] bks f

theorem In_predecessors_is_predecessor_aux (G : ocfg T) (acc : List block_id) (src tgt : block_id)
    (hin : src ∈ predecessors_aux tgt G acc) :
    src ∈ acc ∨ ∃ bk ∈ G, src = bk.blk_id ∧ is_predecessor tgt bk = true := by
  rw [predecessors_aux_eq, List.mem_append] at hin
  rcases hin with h | h
  · obtain ⟨bk, hm, rfl⟩ := List.mem_map.mp h
    obtain ⟨hb, ht⟩ := List.mem_filter.mp (List.mem_reverse.mp hm)
    exact .inr ⟨bk, hb, rfl, ht⟩
  · exact .inl h

theorem In_predecessors_is_predecessor (G : ocfg T) (src tgt : block_id)
    (hin : src ∈ predecessors tgt G) : ∃ bk ∈ G, src = bk.blk_id ∧ is_predecessor tgt bk = true := by
  exact (In_predecessors_is_predecessor_aux G [] src tgt hin).resolve_left (by simp)

theorem successor_predecessor (G : ocfg T) ⦃source : block T⦄ (target : block_id)
    (hs : target ∈ successors source) (hf : find_block G source.blk_id = some source) :
    source.blk_id ∈ predecessors target G := by
  change source.blk_id ∈ predecessors_aux target G []
  rw [predecessors_aux_eq, List.append_nil]
  apply List.mem_map_of_mem
  exact List.mem_reverse.mpr (List.mem_filter.mpr ⟨find_block_In G hf, decide_eq_true hs⟩)

theorem predecessor_successor ⦃G : ocfg T⦄ (source target : block_id) ⦃bk : block T⦄
    (hw : wf_ocfg_bid G) (hin : source ∈ predecessors target G) (hf : find_block G source = some bk) :
    target ∈ successors bk := by
  obtain ⟨b, hb, rfl, ht⟩ := In_predecessors_is_predecessor G source target hin
  have he := wf_ocfg_bid_In_is_found b hw hb
  rw [hf] at he
  cases he
  exact of_decide_eq_true ht

theorem blk_id_convert_typ (env : List («ident» × typ)) (b : block typ) :
    (convert_typ (F := block) env b).blk_id = b.blk_id := by cases b; rfl

theorem inputs_convert_typ (env : List («ident» × typ)) (bs : ocfg typ) :
    inputs (convert_typ (F := ocfg) env bs) = inputs bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change (convert_typ (F := block) env b).blk_id :: inputs (convert_typ (F := ocfg) env bs) = _
    rw [blk_id_convert_typ, ih]; rfl

theorem free_in_convert_typ (env : List («ident» × typ)) ⦃bs : List (block typ)⦄ ⦃id : block_id⦄ :
    free_in_cfg bs id → free_in_cfg (convert_typ (F := ocfg) env bs) id := by
  simp only [free_in_cfg, inputs_convert_typ, imp_self]

theorem wf_ocfg_bid_convert_typ (env : List («ident» × typ)) ⦃bs : ocfg typ⦄ :
    wf_ocfg_bid bs → wf_ocfg_bid (convert_typ (F := ocfg) env bs) := by
  simp only [wf_ocfg_bid, inputs_convert_typ, imp_self]

theorem convert_typ_terminator_outputs (t : terminator typ) :
    terminator_outputs (convert_typ (F := terminator) [] t) = terminator_outputs t := by
  cases t <;> try rfl
  case TERM_Switch v dest brs =>
    induction brs with
    | nil => rfl
    | cons p ps ih =>
      cases p
      exact congrArg (dest :: ·) (congrArg (_ :: ·) (List.cons.inj ih).2)
  case TERM_IndirectBr v brs fn =>
    induction brs with
    | nil => rfl
    | cons x xs ih => exact congrArg (x :: ·) ih

theorem convert_typ_outputs (bks : ocfg typ) : outputs (convert_typ (F := ocfg) [] bks) = outputs bks := by
  induction bks with
  | nil => rfl
  | cons bk bs ih =>
    change outputs (convert_typ (F := block) [] bk :: convert_typ (F := ocfg) [] bs) = _
    rw [outputs_cons, outputs_cons, ih]
    exact congrArg (· ++ outputs bs) (convert_typ_terminator_outputs bk.blk_term.1.2)

end Vellvm.Syntax.ScopeTheory
