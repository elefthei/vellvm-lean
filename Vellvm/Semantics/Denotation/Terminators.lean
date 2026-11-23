import Vellvm.Semantics.Denotation.Instructions
import Vellvm.Semantics.Simulation
import Vellvm.Utils.Assoc

namespace Vellvm.Semantics.Denotation
open Tree Interfaces.Params DynamicValues Syntax.LLVMAst Syntax.DynamicTypes Syntax.AstLib
open LLVMEvents (CFGEtop CFGtop)
open Utils.ListUtil (map_monad loop_monad)

variable [Pa : Params]

def select_switch (value : dvalue) (default_dest : block_id) :
    List (dvalue × block_id) → EOU.EOU block_id
  | [] => pure default_dest
  | (v, dest) :: rest =>
    match value, v with
    | .DVALUE_Base (.DVALUE_I w x), .DVALUE_Base (.DVALUE_I w' y) =>
      if h : w = w' then
        if Numeric.Integers.cmp .Ceq x (h.symm ▸ y) then pure dest
        else select_switch value default_dest rest
      else .raise_error "Ill-typed switch.".toUTF8
    | _, _ => .raise_error "Ill-typed switch.".toUTF8

theorem select_switch_hit (w : Positive) (x : Numeric.Integers.bit_int w) (dest fallback : block_id)
    (rest : List (dvalue × block_id)) :
    let v := DVALUE_Base (DVALUE_I w x)
    select_switch v fallback ((v, dest) :: rest) = .raise_ret dest := by
  simp [select_switch, Numeric.Integers.cmp, Numeric.Integers.eq, pure]

namespace Worker
open LLVMEvents.Worker
open Instrumentation (Diagnostics)
variable {M : ITree.Effect → ITree.Effect → Type → Type v} [Runtime M] [Diagnostics M]

def denote_terminator (trm : (instr_id × terminator dtyp) × List (metadata dtyp)) :
    M CFGEtop NoChoice (block_id ⊕ dvalue) := do
  let ((iid, term), md) := trm
  let info := get_file_info md
  Diagnostics.setLoc info
  let err_loc := fun () ↦ location_string info
  match term with
  | .TERM_Ret (dt, op) => return .inr (← denote_exp' (some dt) op)
  | .TERM_Ret_void => return .inr NONE
  | .TERM_Br (dt, op) br1 br2 =>
    match ← denote_exp' (some dt) op with
    | .DVALUE_Base (.DVALUE_I w bit) =>
      if w.val = 1 then
        return .inl (if Numeric.Integers.eq bit Numeric.Integers.one then br1 else br2)
      else «raise» (err_loc () ++ ": Br got non-bool value".toUTF8)
    | .DVALUE_Base .DVALUE_Poison => raiseUB (err_loc () ++ ": Branching on poison.".toUTF8)
    | _ => «raise» (err_loc () ++ ": Br got non-bool value".toUTF8)
  | .TERM_Br_1 br => return .inl br
  | .TERM_Switch (dt, e) default_br dests =>
    let selector ← denote_exp' (some dt) e
    if dvalue_is_poison selector then raiseUB (err_loc () ++ ": Switching on poison.".toUTF8)
    else
      let bid ← EOU_to_itree (do
        let switches ← map_monad (fun (.TInt_Literal sz x, dest) ↦ do
          let s ← coerce_integer_to_int (some sz) (Attributes.denote_int_syntax x)
          return (DVALUE_Base s, dest)) dests
        select_switch selector default_br switches)
      return .inl bid
  | .TERM_Unreachable =>
    raiseUB (err_loc () ++ ": IMPOSSIBLE: unreachable in reachable position".toUTF8)
  | .TERM_Invoke (dt, fnptrval) args to_label unwind_label anns obs =>
    let loc := err_loc ()
    let uvs ← denote_call_args args (loc ++ ": Invoke argument violates noundef.".toUTF8)
    denote_operand_bundles loc fnptrval obs
    let fv ← denote_exp' none fnptrval
    let rv ← call dt (anns_cconv anns) fv uvs
    let rv ← Attributes.Worker.check_call_return (ann_fun_attributes anns) (ann_ret_attributes anns)
      (metadata_range md) (loc ++ ": Invoke".toUTF8) dt (uvs.map Prod.snd) rv
    match rv with
    | .inl exn =>
      stack_raise exn
      return .inl unwind_label
    | .inr returned =>
      match iid with
      | .IVoid _ => pure ()
      | .IId id => lwrite id returned
      return .inl to_label
  | .TERM_Resume (dt, e) => raiseLLVM (← denote_exp' (some dt) e)
  | .TERM_IndirectBr (dt, addr) brs fn =>
    let a ← denote_exp' (some dt) addr
    if dvalue_is_poison a then raiseUB (err_loc () ++ ": indirectbr on a poison address.".toUTF8)
    else
      match fn with
      | none => «raise» (err_loc () ++ ": indirectbr outside of a function".toUTF8)
      | some f =>
        let addrs ← map_monad (fun b ↦ do
          return dvalue_ptr_address (← gread (blockaddress_id f b))) brs
        match dvalue_ptr_address a with
        | none => «raise» (err_loc () ++ ": indirectbr on a non-pointer".toUTF8)
        | some z =>
          match indirectbr_target z (brs.zip addrs) with
          | some b => return .inl b
          | none => raiseUB (err_loc () ++
              ": indirectbr to an address that is not one of its listed blocks.".toUTF8)

def denote_code (c : code dtyp) (varargs : Option Pa.PTR.ptr) : M CFGEtop NoChoice Unit :=
  loop_monad (fun i ↦ denote_instr i varargs) c

def denote_phi (bid_from : block_id) (id_p : (local_id × phi dtyp) × List (metadata dtyp)) :
    M CFGEtop NoChoice (local_id × dvalue) := do
  let ((id, .Phi _ dt args), md) := id_p
  let info := get_file_info md
  Diagnostics.setLoc info
  match Utils.Assoc.assoc bid_from args with
  | some op => return (id, ← denote_exp' (some dt) op)
  | none => «raise» (location_string info ++ ": jump: phi node doesn't include block ".toUTF8)

def denote_phis (bid_from : block_id) (phis : List ((local_id × phi dtyp) × List (metadata dtyp))) :
    M CFGEtop NoChoice Unit := do
  -- All incoming values see the predecessor's locals, including when the block jumps to itself.
  let dvs ← map_monad (denote_phi bid_from) phis
  loop_monad (fun (id, dv) ↦ lwrite id dv) dvs

def denote_block (b : block dtyp) (bid_from : block_id) (varargs : Option Pa.PTR.ptr) :
    M CFGEtop NoChoice (block_id ⊕ dvalue) := do
  denote_phis bid_from b.blk_phis
  denote_code b.blk_code varargs
  denote_terminator b.blk_term

section
variable {N : ITree.Effect → ITree.Effect → Type → Type w} [Runtime N] [Diagnostics N]
variable [Instrumentation.Snapshots M] [Instrumentation.Snapshots N] (sim : Simulation M N)

theorem denote_terminator_related (trm : (instr_id × terminator dtyp) × List (metadata dtyp)) :
    sim.R (denote_terminator trm) (denote_terminator trm) := by
  rcases trm with ⟨⟨iid, t⟩, md⟩
  unfold denote_terminator
  refine sim.bind (sim.loc _) (fun _ ↦ ?_)
  cases t with
  | TERM_Ret arg =>
    rcases arg with ⟨_, _⟩
    exact sim.bind (denote_exp'_related sim _ _) (fun _ ↦ sim.pure _)
  | TERM_Ret_void | TERM_Br_1 => exact sim.pure _
  | TERM_Br arg br1 br2 =>
    rcases arg with ⟨_, _⟩
    refine sim.bind (denote_exp'_related sim _ _) (fun v ↦ ?_)
    cases v with
    | DVALUE_Base b =>
      cases b with
      | DVALUE_I w bit =>
        dsimp only
        split
        · exact sim.pure _
        · apply sim.raise
      | DVALUE_Poison => apply sim.raiseUB
      | _ => apply sim.raise
    | _ => apply sim.raise
  | TERM_Switch arg default_br dests =>
    rcases arg with ⟨_, _⟩
    refine sim.bind (denote_exp'_related sim _ _) (fun selector ↦ ?_)
    dsimp only
    split
    · apply sim.raiseUB
    · apply sim.bind
      · apply sim.liftEOU
      · exact fun _ ↦ sim.pure _
  | TERM_Unreachable => apply sim.raiseUB
  | TERM_Invoke fnptr args to_label unwind_label anns obs =>
    rcases fnptr with ⟨dt, f⟩
    refine sim.bind (denote_call_args_related sim _ _) (fun uvs ↦ ?_)
    refine sim.bind (denote_operand_bundles_related sim _ _ _) (fun _ ↦ ?_)
    refine sim.bind (denote_exp'_related sim _ _) (fun fv ↦ ?_)
    refine sim.bind (sim.call _ _ _ _) (fun rv ↦ ?_)
    refine sim.bind (Attributes.Worker.check_call_return_congr sim _ _ _ _ _ _ _) (fun rv ↦ ?_)
    cases rv with
    | inl exn =>
      exact sim.bind (sim.stack_raise exn) (fun _ ↦ sim.pure _)
    | inr returned =>
      cases iid with
      | IVoid _ => exact sim.pure _
      | IId id => exact sim.bind (sim.lwrite id returned) (fun _ ↦ sim.pure _)
  | TERM_Resume arg =>
    rcases arg with ⟨_, _⟩
    refine sim.bind (denote_exp'_related sim _ _) (fun exn ↦ ?_)
    apply sim.raiseLLVM
  | TERM_IndirectBr arg brs fn =>
    rcases arg with ⟨_, _⟩
    refine sim.bind (denote_exp'_related sim _ _) (fun a ↦ ?_)
    dsimp only
    split
    · apply sim.raiseUB
    · cases fn with
      | none => apply sim.raise
      | some f =>
        apply sim.bind
        · apply sim.map_monad
          intro b
          exact sim.bind (sim.gread _) (fun _ ↦ sim.pure _)
        intro addrs
        cases dvalue_ptr_address a with
        | none => apply sim.raise
        | some z =>
          cases hb : indirectbr_target z (brs.zip addrs) with
          | none => simp only [hb]; apply sim.raiseUB
          | some b => simp only [hb]; exact sim.pure _

theorem denote_code_related (c : code dtyp) (varargs : Option Pa.PTR.ptr) :
    sim.R (denote_code c varargs) (denote_code c varargs) := by
  apply sim.loop_monad
  exact fun i ↦ denote_instr_related sim i varargs

theorem denote_phi_related (bid_from : block_id)
    (id_p : (local_id × phi dtyp) × List (metadata dtyp)) :
    sim.R (denote_phi bid_from id_p) (denote_phi bid_from id_p) := by
  rcases id_p with ⟨⟨id, ⟨_, dt, args⟩⟩, md⟩
  unfold denote_phi
  refine sim.bind (sim.loc _) (fun _ ↦ ?_)
  cases Utils.Assoc.assoc bid_from args with
  | none => apply sim.raise
  | some e => exact sim.bind (denote_exp'_related sim _ _) (fun _ ↦ sim.pure _)

theorem denote_phis_related (bid_from : block_id)
    (phis : List ((local_id × phi dtyp) × List (metadata dtyp))) :
    sim.R (denote_phis bid_from phis) (denote_phis bid_from phis) := by
  apply sim.bind
  · apply sim.map_monad
    exact denote_phi_related sim bid_from
  intro dvs
  apply sim.loop_monad
  rintro ⟨id, dv⟩
  exact sim.lwrite id dv

theorem denote_block_related (b : block dtyp) (bid_from : block_id) (varargs : Option Pa.PTR.ptr) :
    sim.R (denote_block b bid_from varargs) (denote_block b bid_from varargs) :=
  sim.bind (denote_phis_related sim _ _) fun _ ↦
    sim.bind (denote_code_related sim _ _) fun _ ↦ denote_terminator_related sim _

end

end Worker

def denote_terminator (trm : (instr_id × terminator dtyp) × List (metadata dtyp)) :
    CFGtop (block_id ⊕ dvalue) := Worker.denote_terminator (M := CTree.CTree) trm

def denote_code (c : code dtyp) (varargs : Option Pa.PTR.ptr) : CFGtop Unit :=
  Worker.denote_code (M := CTree.CTree) c varargs

def denote_phi (bid_from : block_id) (id_p : (local_id × phi dtyp) × List (metadata dtyp)) :
    CFGtop (local_id × dvalue) := Worker.denote_phi (M := CTree.CTree) bid_from id_p

def denote_phis (bid_from : block_id) (phis : List ((local_id × phi dtyp) × List (metadata dtyp))) :
    CFGtop Unit := Worker.denote_phis (M := CTree.CTree) bid_from phis

def denote_block (b : block dtyp) (bid_from : block_id) (varargs : Option Pa.PTR.ptr) :
    CFGtop (block_id ⊕ dvalue) := Worker.denote_block (M := CTree.CTree) b bid_from varargs

end Vellvm.Semantics.Denotation
