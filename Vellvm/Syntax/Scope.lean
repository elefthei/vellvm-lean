module

public import Vellvm.Syntax.CFG.Types
public import Vellvm.Syntax.AstLib
public import Vellvm.Numeric.Rocqlib

/-! Block-label scope and local register use and definition sites. -/

@[expose] public section
namespace Vellvm.Syntax.Scope

open LLVMAst CFG Numeric.Rocqlib

universe u
variable {T : Type}

def inputs (bks : ocfg T) : List block_id := bks.map blk_id

def terminator_outputs : terminator T → List block_id
  | .TERM_Br _ br₁ br₂ => [br₁, br₂]
  | .TERM_Br_1 br => [br]
  | .TERM_Switch _ d brs => d :: brs.map Prod.snd
  | .TERM_IndirectBr _ brs _ => brs
  | .TERM_Invoke _ _ dest unwind _ _ => [dest, unwind]
  | .TERM_Ret _ | .TERM_Ret_void | .TERM_Resume _ | .TERM_Unreachable => []

def successors (bk : block T) : List block_id := terminator_outputs bk.blk_term.1.2

def outputs (bks : ocfg T) : List block_id := bks.foldl (fun acc bk ↦ acc ++ successors bk) []

def raw_id_eq_dec (x y : raw_id) : Decidable (x = y) := AstLib.RawIDOrd.eq_dec x y

def raw_id_in (a : raw_id) (xs : List raw_id) : Decidable (a ∈ xs) :=
  letI : DecidableEq raw_id := raw_id_eq_dec
  inferInstance

def is_predecessor (b : block_id) (bk : block T) : Bool :=
  @decide _ (raw_id_in b (successors bk))

def predecessors (b : block_id) (G : ocfg T) : List block_id :=
  G.foldl (fun acc bk ↦ if is_predecessor b bk then bk.blk_id :: acc else acc) []

def wf_ocfg_bid (bks : ocfg T) : Prop := list_norepet (inputs bks)

def no_reentrance (bks₁ bks₂ : ocfg T) : Prop := list_disjoint (outputs bks₂) (inputs bks₁)

def no_duplicate_bid (bks₁ bks₂ : ocfg T) : Prop := list_disjoint (inputs bks₁) (inputs bks₂)

def independent_flows (bks₁ bks₂ : ocfg T) : Prop :=
  no_reentrance bks₁ bks₂ ∧ no_reentrance bks₂ bks₁ ∧ no_duplicate_bid bks₁ bks₂

def free_in_cfg (G : ocfg T) (id : block_id) : Prop := id ∉ inputs G

def phi_sources : phi T → List block_id
  | .Phi _ _ l => l.map Prod.fst

def wf_ocfg_phis (G : ocfg T) : Prop :=
  ∀ (bk : block T) pred x p md, bk ∈ G → ((x, p), md) ∈ bk.blk_phis →
    (pred ∈ phi_sources p ↔ pred ∈ predecessors bk.blk_id G)

structure wf_cfg (G : cfg T) : Prop where
  WF_CFG (G) ::
  wf_cfg_bid : wf_ocfg_bid G.blks
  wf_cfg_phis : wf_ocfg_phis G.blks

export wf_cfg (WF_CFG wf_cfg_bid wf_cfg_phis)

namespace SetNotations

/- The list-set operations follow Stdlib/Lists/ListSet.v, Copyright INRIA, CNRS and
contributors, licensed under the GNU Lesser General Public License version 2.1.
In particular, union preserves the left list, adding missing right elements from the end. -/
def set_add (x : raw_id) : List raw_id → List raw_id
  | [] => [x]
  | y :: ys => if @decide _ (raw_id_eq_dec x y) then y :: ys else y :: set_add x ys

def set_union (xs ys : List raw_id) : List raw_id := ys.foldr set_add xs

def set_diff (xs ys : List raw_id) : List raw_id :=
  xs.foldr (fun x acc ↦ if @decide _ (raw_id_in x ys) then acc else set_add x acc) []

scoped infixr:65 " +++ " => set_union
scoped infixr:65 " ::: " => set_add
scoped infixr:65 " ∖ " => set_diff
scoped notation "∅" => ([] : List _)

def set_flat_map {A : Type u} (f : A → List raw_id) (xs : List A) : List raw_id :=
  xs.foldr (fun x acc ↦ set_union (f x) acc) []

end SetNotations

open SetNotations

class Def_sites (A : Type u) where
  Build_Def_sites ::
  def_sites : A → List raw_id

export Def_sites (Build_Def_sites def_sites)

instance instr_id_defs : Def_sites instr_id where
  def_sites
    | .IId id => [id]
    | .IVoid _ => []

instance code_defs : Def_sites (code T) where
  def_sites c := c.foldr (fun x acc ↦ def_sites x.1.1 +++ acc) []

instance block_def_sites : Def_sites (block T) where
  def_sites bk := bk.blk_phis.map (·.1.1) +++ def_sites bk.blk_code

instance ocfg_def_sites : Def_sites (ocfg T) where
  def_sites := set_flat_map def_sites

instance cfg_def_sites : Def_sites (cfg T) where
  def_sites G := def_sites G.blks

class Use_sites (A : Type u) where
  Build_Use_sites ::
  use_sites : A → List raw_id

export Use_sites (Build_Use_sites use_sites)

instance ident_use_sites : Use_sites «ident» where
  use_sites
    | .ID_Local id => [id]
    | .ID_Global _ => []

instance exp_use_sites : Use_sites (exp T) := ⟨expUses⟩ where
  expUses : exp T → List raw_id
    | .EXP_Ident id => use_sites id
    | .EXP_Integer _ | .EXP_Float _ | .EXP_Bool _ | .EXP_Null | .EXP_Zero_initializer
    | .EXP_Cstring _ | .EXP_Undef | .EXP_Poison | .EXP_Asm _ _ _ _ _ _ | .EXP_Metadata _
    | .EXP_BlockAddress _ _ => []
    | .OP_Conversion _ _ e _ | .OP_ExtractValue (_, e) _ | .OP_Freeze (_, e)
    | .OP_Fneg _ (_, e) | .EXP_Splat (_, e) => expUses e
    | .OP_IBinop _ _ a b | .OP_ICmp _ _ _ a b | .OP_FBinop _ _ _ a b | .OP_FCmp _ _ _ a b
    | .OP_ExtractElement (_, a) (_, b) | .OP_InsertValue (_, a) (_, b) _ => expUses a +++ expUses b
    | .OP_InsertElement (_, a) (_, b) (_, c) | .OP_ShuffleVector (_, a) (_, b) (_, c)
    | .OP_Select _ (_, a) (_, b) (_, c) => expUses a +++ expUses b +++ expUses c
    | .EXP_Struct xs | .EXP_Packed_struct xs | .EXP_Array xs | .EXP_Vector xs => texpListUses xs
    | .OP_GetElementPtr _ _ (_, e) xs => expUses e +++ texpListUses xs

  texpListUses : List (texp T) → List raw_id
    | [] => []
    | (_, e) :: xs => expUses e +++ texpListUses xs

instance texp_use_sites : Use_sites (texp T) := ⟨fun x ↦ use_sites x.2⟩

instance option_use_sites {A : Type u} [Use_sites A] : Use_sites (Option A) where
  use_sites
    | some e => use_sites e
    | none => []

instance landingpad_clause_use_sites : Use_sites (@landingpad_clause T) where
  use_sites
    | .CATCH t | .FILTER t => use_sites t

instance instr_use_sites : Use_sites (instr T) where
  use_sites
    | .INSTR_Op e => use_sites e
    | .INSTR_Call e l _ _ => use_sites e +++ set_flat_map (fun a ↦ use_sites a.1) l
    | .INSTR_Load _ e _ => use_sites e
    | .INSTR_Store e₁ e₂ _ => use_sites e₁ +++ use_sites e₂
    | .INSTR_LandingPad _ _ cs => set_flat_map use_sites cs
    | .INSTR_Alloca _ _ | .INSTR_Fence _ _ | .INSTR_AtomicCmpXchg _ | .INSTR_AtomicRMW _
    | .INSTR_VAArg _ _ | .INSTR_Comment _ => []

instance code_use_sites : Use_sites (code T) where
  use_sites := set_flat_map (fun x ↦ use_sites x.1.2)

instance term_use_sites : Use_sites (terminator T) where
  use_sites
    | .TERM_Ret e | .TERM_Br e _ _ | .TERM_IndirectBr e _ _ | .TERM_Resume e
    | .TERM_Switch e _ _ => use_sites e
    | .TERM_Ret_void | .TERM_Br_1 _ | .TERM_Unreachable => []
    | .TERM_Invoke _ l _ _ _ _ => set_flat_map (fun a ↦ use_sites a.1) l

instance phi_use_sites : Use_sites (phi T) where
  use_sites
    | .Phi _ _ l => set_flat_map (fun a ↦ use_sites a.2) l

instance block_use_sites : Use_sites (block T) where
  use_sites bk :=
    set_flat_map (fun a ↦ use_sites a.1.2) bk.blk_phis +++
      use_sites bk.blk_code +++ use_sites bk.blk_term.1.2

instance ocfg_use_sites : Use_sites (ocfg T) := ⟨set_flat_map use_sites⟩

instance cfg_use_sites : Use_sites (cfg T) where
  use_sites G := G.args +++ use_sites G.blks

end Vellvm.Syntax.Scope
