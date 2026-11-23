import Vellvm.Semantics.Denotation.Frames
import Vellvm.Semantics.Denotation.Terminators
import Vellvm.Semantics.Attributes
import Vellvm.Utils.IntMaps.Refinement

namespace Vellvm.Semantics.Denotation
open ITree (Effect)
open Tree Interfaces.Params DynamicValues Syntax.LLVMAst Syntax.CFG Syntax.RawIdMaps Syntax.DynamicTypes
open LLVMEvents (CallE CFGEtop MCFGEtop CFGtop MCFGtop exc)
open Utils.IntMaps (IntMap)

variable [Pa : Params]

namespace Worker
variable {M : Effect → Effect → Type → Type v} [Runtime M] [Instrumentation.Diagnostics M]

def denote_ocfg_map (bmap : rmap (block dtyp)) (varargs : Option Pa.PTR.ptr)
    (entry : block_id × block_id) : M CFGEtop NoChoice ((block_id × block_id) ⊕ dvalue) :=
  Runtime.iter (fun (pred, src) ↦ do
    match RM.find src bmap with
    | none => pure (.inr (.inl (pred, src)))
    | some b => match ← denote_block b pred varargs with
      | .inl dst => pure (.inl (src, dst))
      | .inr v => pure (.inr (.inr v))) entry

def denote_ocfg (bks : ocfg dtyp) := denote_ocfg_map (M := M) (ocfg_map bks)

def denote_cfg_map (bmap : rmap (block dtyp)) (f : cfg dtyp) (varargs : Option Pa.PTR.ptr) :
    M CFGEtop NoChoice dvalue := do
  match ← denote_ocfg_map bmap varargs (f.init, f.init) with
  | .inl bid =>
    LLVMEvents.Worker.«raise» ("Can't find block in denote_cfg ".toUTF8 ++ Syntax.ShowAST.show_raw_id bid.2)
  | .inr v => pure v

def denote_cfg (f : cfg dtyp) (varargs : Option Pa.PTR.ptr) : M CFGEtop NoChoice dvalue :=
  denote_cfg_map (ocfg_map f.blks) f varargs

def denote_function [Catch M] (df : definition dtyp (cfg dtyp)) : function_denotation M :=
  let bmap := ocfg_map df.df_instrs.blks
  let (retAttrs, argsAttrs) := df.df_prototype.dc_param_attrs
  let fname := Syntax.ShowAST.show_raw_id df.df_prototype.dc_name
  let fcc := anns_cconv df.df_prototype.dc_annotations
  fun cc retTy args ↦ do
    LLVMEvents.Worker.EOU_to_itree (Attributes.check_cconv fcc cc fname)
    let args ← Attributes.Worker.apply_args_attrs argsAttrs
      ("Argument of ".toUTF8 ++ fname ++ " violates noundef.".toUTF8) args
    let vargs ← push_call_frame df args
    let rv ← run_exc (denote_cfg_map bmap df.df_instrs (some vargs))
    pop_call_frame
    Attributes.Worker.check_call_return df.df_prototype.dc_attrs retAttrs none fname retTy
      (args.map Prod.snd) rv

def call_body (fundefs : IntMap (function_denotation M)) : (d : CallE.I) → M CFGEtop NoChoice (CallE.O d)
  | .Call dt cc fv args => do
    LLVMEvents.Worker.EOU_to_itree (Attributes.check_callee fv)
    match lookup_defn fv fundefs with
    | some f => f cc dt args
    | none => return .inr (← LLVMEvents.Worker.external_call dt fv args)

def denote_mcfg (fundefs : IntMap (function_denotation M)) (dt : dtyp) (fv : dvalue)
    (args : List (dtyp × dvalue)) : M MCFGEtop NoChoice (dvalue ⊕ dvalue) :=
  let ctx := call_body fundefs
  Runtime.interp_mrec ctx (ctx (.Call dt .CC_Ccc fv args))

variable {N : Effect → Effect → Type → Type w} [Runtime N] [Instrumentation.Diagnostics N]
variable [Instrumentation.Snapshots M] [Instrumentation.Snapshots N] (sim : Simulation M N)

theorem denote_ocfg_map_related (bmap : rmap (block dtyp)) (varargs : Option Pa.PTR.ptr)
    (entry : block_id × block_id) :
    sim.R (denote_ocfg_map bmap varargs entry) (denote_ocfg_map bmap varargs entry) := by
  unfold denote_ocfg_map
  apply sim.iter
  rintro ⟨pred, src⟩
  dsimp only
  cases RM.find src bmap with
  | none => exact sim.pure _
  | some b =>
    apply sim.bind (denote_block_related sim b pred varargs)
    rintro (dst | v) <;> exact sim.pure _

theorem denote_cfg_map_related (bmap : rmap (block dtyp)) (f : cfg dtyp) (varargs : Option Pa.PTR.ptr) :
    sim.R (denote_cfg_map bmap f varargs) (denote_cfg_map bmap f varargs) := by
  unfold denote_cfg_map
  apply sim.bind (denote_ocfg_map_related sim bmap varargs _)
  rintro (bid | v)
  · exact sim.raise _
  · exact sim.pure _

def FunctionsRelated (f : function_denotation M) (g : function_denotation N) : Prop :=
  ∀ cc retTy args, sim.R (f cc retTy args) (g cc retTy args)

theorem denote_function_related [Catch M] [Catch N] (hc : CatchCompatible sim)
    (df : definition dtyp (cfg dtyp)) :
    FunctionsRelated sim (denote_function df) (denote_function df) := by
  intro cc retTy args
  unfold denote_function
  apply sim.bind (sim.liftEOU _)
  intro _
  apply sim.bind (Attributes.Worker.apply_args_attrs_congr sim _ _ _)
  intro passed
  apply sim.bind (push_call_frame_related sim df passed)
  intro vargs
  apply sim.bind (hc _ (denote_cfg_map_related sim _ _ _))
  intro rv
  apply sim.bind (pop_call_frame_related sim)
  intro _
  exact Attributes.Worker.check_call_return_congr sim _ _ _ _ _ _ _

theorem call_body_related (fs : IntMap (function_denotation M)) (gs : IntMap (function_denotation N))
    (hm : Utils.IntMaps.IM_Refine (FunctionsRelated sim) fs gs) (d : CallE.I) :
    sim.R (call_body fs d) (call_body gs d) := by
  rcases d with ⟨dt, cc, fv, args⟩
  unfold call_body
  apply sim.bind (sim.liftEOU _)
  intro _
  have hr : Numeric.Rocqlib.option_rel (FunctionsRelated sim) (lookup_defn fv fs) (lookup_defn fv gs) := by
    unfold lookup_defn
    cases dvalue_ptr_address fv with
    | none => exact .none
    | some k => exact Utils.IntMaps.IM_Refine_lookup _ fs gs hm k
  generalize lookup_defn fv fs = lf, lookup_defn fv gs = rg at hr ⊢
  cases hr with
  | some _ _ h => exact h cc dt args
  | none =>
    exact sim.bind (sim.emit (E := LLVMEvents.ExternalCallE) (.ExternalCall dt fv args))
      fun v ↦ sim.pure (Sum.inr v : exc ⊕ dvalue)

theorem denote_mcfg_related (fs : IntMap (function_denotation M)) (gs : IntMap (function_denotation N))
    (hm : Utils.IntMaps.IM_Refine (FunctionsRelated sim) fs gs) (dt : dtyp) (fv : dvalue)
    (args : List (dtyp × dvalue)) : sim.R (denote_mcfg fs dt fv args) (denote_mcfg gs dt fv args) :=
  sim.mrec (call_body_related sim _ _ hm) (call_body_related sim _ _ hm (.Call dt .CC_Ccc fv args))

end Worker

def denote_ocfg_map (bmap : rmap (block dtyp)) (varargs : Option Pa.PTR.ptr) (entry : block_id × block_id) :
    CFGtop ((block_id × block_id) ⊕ dvalue) := Worker.denote_ocfg_map bmap varargs entry

def denote_ocfg (bks : ocfg dtyp) := Worker.denote_ocfg (M := CTree.CTree) bks

def denote_cfg_map (bmap : rmap (block dtyp)) (f : cfg dtyp) (varargs : Option Pa.PTR.ptr) :
    CFGtop dvalue := Worker.denote_cfg_map bmap f varargs

def denote_cfg (f : cfg dtyp) (varargs : Option Pa.PTR.ptr) : CFGtop dvalue := Worker.denote_cfg f varargs

def denote_function (df : definition dtyp (cfg dtyp)) : function_denotation :=
  Worker.denote_function df

def denote_mcfg (fundefs : IntMap function_denotation) (dt : dtyp) (fv : dvalue)
    (args : List (dtyp × dvalue)) : MCFGtop (dvalue ⊕ dvalue) := Worker.denote_mcfg fundefs dt fv args

end Vellvm.Semantics.Denotation
