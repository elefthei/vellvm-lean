/- Copyright (c) 2026 Vellvm developers. Distributed under the MIT License. -/
import PortChecks.SourceType
import Vellvm.Syntax.ScopeTheory

open Vellvm.Syntax.LLVMAst Vellvm.Syntax.CFG Vellvm.Syntax.RawIdMaps
open Vellvm.Syntax.Scope Vellvm.Syntax.TypToDtyp Vellvm.Syntax.ScopeTheory

universe u

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|app_snoc_app"
  app_snoc_app : ∀ {A : Type u} (l l' : List A) (x : A), (l ++ [x]) ++ l' = l ++ (x :: l')

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|inputs_app"
  inputs_app : ∀ {T : Type} (l r : ocfg T), inputs (l ++ r) = inputs l ++ inputs r

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|inputs_cons"
  inputs_cons : ∀ {T : Type} (b : block T) (l : ocfg T), inputs (b :: l) = b.blk_id :: inputs l

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|outputs_acc"
  outputs_acc : ∀ {T : Type} (bs : ocfg T) (acc : List block_id),
    bs.foldl (fun a b ↦ a ++ successors b) acc = acc ++ bs.foldl (fun a b ↦ a ++ successors b) []

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|outputs_app"
  outputs_app : ∀ {T : Type} (l r : ocfg T), outputs (l ++ r) = outputs l ++ outputs r

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|outputs_cons"
  outputs_cons : ∀ {T : Type} (b : block T) (l : ocfg T), outputs (b :: l) = successors b ++ outputs l

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|wf_ocfg_bid_nil"
  wf_ocfg_bid_nil : ∀ {T : Type}, wf_ocfg_bid ([] : ocfg T)

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|wf_ocfg_bid_cons"
  wf_ocfg_bid_cons : ∀ {T : Type} ⦃b : block T⦄ ⦃bs : ocfg T⦄, wf_ocfg_bid (b :: bs) → wf_ocfg_bid bs

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|wf_ocfg_bid_cons_not_in"
  wf_ocfg_bid_cons_not_in : ∀ {T : Type} ⦃b : block T⦄ ⦃bs : ocfg T⦄,
    wf_ocfg_bid (b :: bs) → b.blk_id ∉ inputs bs

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|wf_ocfg_bid_app_r"
  wf_ocfg_bid_app_r : ∀ {T : Type} (bs₁ bs₂ : ocfg T), wf_ocfg_bid (bs₁ ++ bs₂) → wf_ocfg_bid bs₂

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|wf_ocfg_bid_app_l"
  wf_ocfg_bid_app_l : ∀ {T : Type} (bs₁ bs₂ : ocfg T), wf_ocfg_bid (bs₁ ++ bs₂) → wf_ocfg_bid bs₁

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|wf_ocfg_commut"
  wf_ocfg_commut : ∀ {T : Type} (G G' : ocfg T), wf_ocfg_bid (G ++ G') → wf_ocfg_bid (G' ++ G)

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|wf_ocfg_commut_hd"
  wf_ocfg_commut_hd : ∀ {T : Type} ⦃b b' : block T⦄ ⦃G : List (block T)⦄,
    wf_ocfg_bid (b :: b' :: G) → wf_ocfg_bid (b' :: b :: G)

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|wf_ocfg_map"
  wf_ocfg_map : ∀ {T : Type} (f : block T → block T) (G : ocfg T),
    (∀ b, (f b).blk_id = b.blk_id) → (wf_ocfg_bid G ↔ wf_ocfg_bid (G.map f))

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|blk_id_convert_typ"
  blk_id_convert_typ : ∀ (env : List («ident» × typ)) (b : block typ),
    (convert_typ (F := block) env b).blk_id = b.blk_id

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|wf_ocfg_bid_app_not_in_l"
  wf_ocfg_bid_app_not_in_l : ∀ {T : Type} (id : block_id) (bs bs' : ocfg T),
    id ∈ inputs bs → wf_ocfg_bid (bs' ++ bs) → id ∉ inputs bs'

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|wf_ocfg_app_not_in_r"
  wf_ocfg_app_not_in_r : ∀ {T : Type} (id : block_id) (bs bs' : ocfg T),
    id ∈ inputs bs → wf_ocfg_bid (bs' ++ bs) → id ∉ inputs bs'

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|In_bk_outputs"
  In_bk_outputs : ∀ {T : Type} (bid br : block_id) ⦃b : block T⦄ (l : ocfg T),
    br ∈ successors b → find_block l bid = some b → br ∈ outputs l

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|find_block_in_inputs"
  find_block_in_inputs : ∀ {T : Type} (label : block_id) (bs : ocfg T),
    label ∈ inputs bs → ∃ bk, find_block bs label = some bk

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|no_reentrance_not_in"
  no_reentrance_not_in : ∀ {T : Type} ⦃a b : ocfg T⦄, no_reentrance a b →
    ∀ x, x ∈ outputs b → x ∉ inputs a

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|no_reentrance_app_l"
  no_reentrance_app_l : ∀ {T : Type} (a a' b : ocfg T),
    no_reentrance (a ++ a') b ↔ no_reentrance a b ∧ no_reentrance a' b

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|no_reentrance_app_r"
  no_reentrance_app_r : ∀ {T : Type} (a b b' : ocfg T),
    no_reentrance a (b ++ b') ↔ no_reentrance a b ∧ no_reentrance a b'

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|no_duplicate_bid_not_in_l"
  no_duplicate_bid_not_in_l : ∀ {T : Type} ⦃a b : ocfg T⦄, no_duplicate_bid a b →
    ∀ x, x ∈ inputs b → x ∉ inputs a

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|no_duplicate_bid_not_in_r"
  no_duplicate_bid_not_in_r : ∀ {T : Type} ⦃a b : ocfg T⦄, no_duplicate_bid a b →
    ∀ x, x ∈ inputs a → x ∉ inputs b

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|independent_flows_no_reentrance_l"
  independent_flows_no_reentrance_l : ∀ {T : Type} ⦃a b : ocfg T⦄,
    independent_flows a b → no_reentrance a b

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|independent_flows_no_reentrance_r"
  independent_flows_no_reentrance_r : ∀ {T : Type} ⦃a b : ocfg T⦄,
    independent_flows a b → no_reentrance b a

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|independent_flows_no_duplicate_bid"
  independent_flows_no_duplicate_bid : ∀ {T : Type} ⦃a b : ocfg T⦄,
    independent_flows a b → no_duplicate_bid a b

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|find_block_not_in_inputs"
  find_block_not_in_inputs : ∀ {T : Type} (bid : block_id) (l : ocfg T),
    bid ∉ inputs l → find_block l bid = none

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|wf_ocfg_bid_singleton"
  wf_ocfg_bid_singleton : ∀ {T : Type} (b : block T), wf_ocfg_bid [b]

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|wf_ocfg_bid_cons'"
  wf_ocfg_bid_cons' : ∀ {T : Type} (b : block T) ⦃bs : ocfg T⦄,
    b.blk_id ∉ inputs bs → wf_ocfg_bid bs → wf_ocfg_bid (b :: bs)

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|free_in_cfg_cons"
  free_in_cfg_cons : ∀ {T : Type} ⦃b : block T⦄ ⦃bs : ocfg T⦄ ⦃id : block_id⦄,
    free_in_cfg (b :: bs) id → free_in_cfg bs id

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|free_in_cfg_app"
  free_in_cfg_app : ∀ {T : Type} (a b : ocfg T) (id : block_id),
    free_in_cfg (a ++ b) id ↔ free_in_cfg a id ∧ free_in_cfg b id

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|wf_ocfg_bid_distinct_labels"
  wf_ocfg_bid_distinct_labels : ∀ {T : Type} (bs₁ bs₂ : ocfg T) ⦃l r : block_id⦄,
    wf_ocfg_bid (bs₁ ++ bs₂) → l ∈ inputs bs₁ → r ∈ inputs bs₂ → l ≠ r

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|predecessors_app"
  predecessors_app : ∀ {T : Type} (l r : ocfg T) (f : block_id),
    predecessors f (l ++ r) = predecessors f r ++ predecessors f l

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|predecessors_cons"
  predecessors_cons : ∀ {T : Type} (l : ocfg T) (b : block T) (f : block_id),
    predecessors f (b :: l) = predecessors f l ++ predecessors f [b]

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|find_block_In"
  find_block_In : ∀ {T : Type} (G : List (block T)) ⦃bk : block T⦄,
    find_block G bk.blk_id = some bk → bk ∈ G

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|successor_predecessor"
  successor_predecessor : ∀ {T : Type} (G : ocfg T) ⦃bk : block T⦄ (tgt : block_id),
    tgt ∈ successors bk → find_block G bk.blk_id = some bk → bk.blk_id ∈ predecessors tgt G

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|In_predecessors_is_predecessor_aux"
  In_predecessors_is_predecessor_aux : ∀ {T : Type} (G : ocfg T) (acc : List block_id) (s t : block_id),
    s ∈ predecessors_aux t G acc → s ∈ acc ∨ ∃ bk ∈ G, s = bk.blk_id ∧ is_predecessor t bk = true

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|In_predecessors_is_predecessor"
  In_predecessors_is_predecessor : ∀ {T : Type} (G : ocfg T) (s t : block_id),
    s ∈ predecessors t G → ∃ bk ∈ G, s = bk.blk_id ∧ is_predecessor t bk = true

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|find_block_nil"
  find_block_nil : ∀ {T : Type} (x : block_id), find_block ([] : ocfg T) x = none

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|find_block_eq"
  find_block_eq : ∀ {T : Type} ⦃x : block_id⦄ (b : block T) (bs : ocfg T),
    b.blk_id = x → find_block (b :: bs) x = some b

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|find_block_ineq"
  find_block_ineq : ∀ {T : Type} ⦃x : block_id⦄ (b : block T) (bs : ocfg T),
    b.blk_id ≠ x → find_block (b :: bs) x = find_block bs x

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|ocfg_map_find_block"
  ocfg_map_find_block : ∀ {T : Type} (bs : ocfg T) (id : block_id),
    RM.find id (ocfg_map bs) = find_block bs id

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|wf_ocfg_bid_In_is_found"
  wf_ocfg_bid_In_is_found : ∀ {T : Type} ⦃bs : ocfg T⦄ (b : block T),
    wf_ocfg_bid bs → b ∈ bs → find_block bs b.blk_id = some b

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|predecessor_successor"
  predecessor_successor : ∀ {T : Type} ⦃G : ocfg T⦄ (s t : block_id) ⦃bk : block T⦄,
    wf_ocfg_bid G → s ∈ predecessors t G → find_block G s = some bk → t ∈ successors bk

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|find_block_app_r_wf"
  find_block_app_r_wf : ∀ {T : Type} (id : block_id) ⦃b : block T⦄ (l r : ocfg T),
    wf_ocfg_bid (l ++ r) → find_block r id = some b → find_block (l ++ r) id = some b

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|find_block_app_l_wf"
  find_block_app_l_wf : ∀ {T : Type} (id : block_id) ⦃b : block T⦄ (l r : ocfg T),
    wf_ocfg_bid (l ++ r) → find_block l id = some b → find_block (l ++ r) id = some b

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|find_block_tail_wf"
  find_block_tail_wf : ∀ {T : Type} (id : block_id) ⦃a b : block T⦄ ⦃l : ocfg T⦄,
    wf_ocfg_bid (a :: l) → find_block l id = some b → find_block (a :: l) id = some b

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|find_block_free_id"
  find_block_free_id : ∀ {T : Type} ⦃bs : ocfg T⦄ ⦃id : block_id⦄,
    free_in_cfg bs id → find_block bs id = none

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|find_block_none_app"
  find_block_none_app : ∀ {T : Type} (l r : ocfg T) (id : block_id),
    find_block l id = none → find_block (l ++ r) id = find_block r id

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|find_block_some_app"
  find_block_some_app : ∀ {T : Type} (l r : ocfg T) ⦃b : block T⦄ (id : block_id),
    find_block l id = some b → find_block (l ++ r) id = some b

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|find_block_Some_In_inputs"
  find_block_Some_In_inputs : ∀ {T : Type} (bs : ocfg T) (id : block_id) ⦃bk : block T⦄,
    find_block bs id = some bk → id ∈ inputs bs

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|wf_ocfg_bid_find_None_app_l"
  wf_ocfg_bid_find_None_app_l : ∀ {T : Type} (l r : ocfg T) (id : block_id) ⦃b : block T⦄,
    wf_ocfg_bid (l ++ r) → find_block r id = some b → find_block l id = none

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|find_block_has_id"
  find_block_has_id : ∀ {T : Type} (G : ocfg T) (id : block_id) ⦃b : block T⦄,
    find_block G id = some b → id = b.blk_id

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|find_block_map_some"
  find_block_map_some : ∀ {T : Type} (f : block T → block T) (G : List (block T))
    (id : block_id) ⦃b : block T⦄, (∀ bk, (f bk).blk_id = bk.blk_id) →
    find_block G id = some b → find_block (G.map f) id = some (f b)

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|find_block_map_none"
  find_block_map_none : ∀ {T : Type} (f : block T → block T) (G : List (block T)) (id : block_id),
    (∀ bk, (f bk).blk_id = bk.blk_id) → find_block G id = none → find_block (G.map f) id = none

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|wf_ocfg_bid_find_block_unique"
  wf_ocfg_bid_find_block_unique : ∀ {T : Type} ⦃G : ocfg T⦄ ⦃x : block T⦄
    (id : block_id) ⦃y : block T⦄, wf_ocfg_bid G → find_block G id = some x →
    find_block G id = some y → x = y

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|find_block_In'"
  find_block_In' : ∀ {T : Type} (G : List (block T)) (id : block_id) ⦃bk : block T⦄,
    find_block G id = some bk → bk ∈ G

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|wf_ocfg_cons_not_in_tail"
  wf_ocfg_cons_not_in_tail : ∀ {T : Type} ⦃b : block T⦄ ⦃G : List (block T)⦄,
    wf_ocfg_bid (b :: G) → find_block G b.blk_id = none

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|In_find_block"
  In_find_block : ∀ {T : Type} (bs : ocfg T) (b : block T),
    b ∈ bs → ∃ b', find_block bs b.blk_id = some b'

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|find_block_map"
  find_block_map : ∀ {T : Type} (f : block T → block T) (G : List (block T)) (id : block_id),
    (∀ bk, (f bk).blk_id = bk.blk_id) → find_block (G.map f) id =
      Vellvm.Numeric.Rocqlib.option_map f (find_block G id)

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|free_in_convert_typ"
  free_in_convert_typ : ∀ (env : List («ident» × typ)) ⦃bs : List (block typ)⦄ ⦃id : block_id⦄,
    free_in_cfg bs id → free_in_cfg (convert_typ (F := ocfg) env bs) id

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|convert_typ_terminator_outputs"
  convert_typ_terminator_outputs : ∀ t : terminator typ,
    terminator_outputs (convert_typ (F := terminator) [] t) = terminator_outputs t

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|convert_typ_outputs"
  convert_typ_outputs : ∀ bs : ocfg typ, outputs (convert_typ (F := ocfg) [] bs) = outputs bs

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|inputs_convert_typ"
  inputs_convert_typ : ∀ (env : List («ident» × typ)) (bs : ocfg typ),
    inputs (convert_typ (F := ocfg) env bs) = inputs bs

#source_check "src/rocq/Syntax/ScopeTheory.v|Vellvm.Syntax.ScopeTheory|wf_ocfg_bid_convert_typ"
  wf_ocfg_bid_convert_typ : ∀ (env : List («ident» × typ)) ⦃bs : ocfg typ⦄,
    wf_ocfg_bid bs → wf_ocfg_bid (convert_typ (F := ocfg) env bs)
