import Vellvm.Semantics.Denotation.Expressions
import Vellvm.Semantics.Attributes

namespace Vellvm.Semantics.Denotation
open Tree Interfaces.Params DynamicValues Syntax.LLVMAst Syntax.DynamicTypes Syntax.AstLib
open LLVMEvents (CFGEtop CFGtop)
open Utils.ListUtil (map_monad loop_monad)

variable [Pa : Params]

namespace Worker
open LLVMEvents.Worker
open Instrumentation (Diagnostics)
variable {M : ITree.Effect → ITree.Effect → Type → Type v} [Runtime M] [Diagnostics M]

def denote_cmpxchg (id : raw_id) (cpx : cmpxchg dtyp) : M CFGEtop NoChoice Unit := do
  let (ptrTy, ptrExp) := cpx.c_ptr
  let (cmpTy, cmpExp) := cpx.c_cmp
  let (newTy, newExp) := cpx.c_new
  if cmpTy ≠ newTy then return ← «raise» "Ill-typed atomiccmpxchg".toUTF8
  let ptr ← denote_exp' (M := M) (some ptrTy) ptrExp
  let cmp ← denote_exp' (M := M) (some cmpTy) cmpExp
  let newVal ← denote_exp' (M := M) (some cmpTy) newExp
  EOU_to_itree (Attributes.assert_aligned_to ptr cpx.c_align
    "cmpxchg with overestimated alignment.".toUTF8)
  let loaded ← load cmpTy ptr
  match ← EOU_to_itree (Operations.Compare.eval_icmp false .Eq cmpTy loaded cmp) with
  | .DVALUE_Base (.DVALUE_I ⟨1, _⟩ bit) =>
    let same := Numeric.Integers.eq bit Numeric.Integers.one
    if same then store cmpTy ptr newVal
    let flag : VellvmIntegers.int1 := if same then Numeric.Integers.one else Numeric.Integers.zero
    lwrite id (.DVALUE_Struct false [loaded, .DVALUE_Base (.DVALUE_I ⟨1, by decide⟩ flag)])
  | .DVALUE_Base .DVALUE_Poison => raiseUB "comparing poison in atomiccmpxchg.".toUTF8
  | _ => «raise» "Br got non-bool value".toUTF8

def denote_atomic_rmw_operation (op : atomic_rmw_operation) (dt : dtyp) (pv val : dvalue) :
    M CFGEtop NoChoice dvalue :=
  match op with
  | .Axchg => pure val
  | .Aadd => EOU_to_itree (eval_iop (.Add false false) dt pv val)
  | .Asub => EOU_to_itree (eval_iop (.Sub false false) dt pv val)
  | .Aand => EOU_to_itree (eval_iop .And dt pv val)
  | .Aor => EOU_to_itree (eval_iop (.Or false) dt pv val)
  | .Axor => EOU_to_itree (eval_iop .Xor dt pv val)
  | .Anand =>
    match val with
    | .DVALUE_Base (.DVALUE_I sz _) => EOU_to_itree (do
      let both ← eval_iop .And dt pv val
      let mask := Numeric.Integers.repr (w := sz) (Numeric.Integers.max_unsigned (w := sz))
      eval_iop (.Sub false false) dt (.DVALUE_Base (.DVALUE_I sz mask)) both)
    | _ => «raise» "atomicrmw nand of non-integer value".toUTF8
  | .Afadd => EOU_to_itree (eval_fop .FAdd dt pv val)
  | .Afsub => EOU_to_itree (eval_fop .FSub dt pv val)
  | .Amax | .Amin | .Aumax | .Aumin | .Afmax | .Afmin | .Afmaximum | .Afminimum
  | .Auinc_wrap | .Audec_wrap | .Ausub_cond | .Ausub_sat =>
    «raise» "Unsupported atomicrwm operation".toUTF8

def denote_atomicrmw (id : raw_id) (armw : atomicrmw dtyp) : M CFGEtop NoChoice Unit := do
  let (ptrTy, ptrExp) := armw.a_ptr
  let (dt, e) := armw.a_val
  let ptr ← denote_exp' (M := M) (some ptrTy) ptrExp
  let v ← denote_exp' (M := M) (some dt) e
  EOU_to_itree (Attributes.assert_aligned_to ptr armw.a_align
    "atomicrmw with overestimated alignment.".toUTF8)
  let loaded ← load dt ptr
  let stored ← denote_atomic_rmw_operation armw.a_operation dt loaded v
  store dt ptr stored
  lwrite id loaded

def denote_call_args (args : List (texp dtyp × List param_attr)) (msg : IRString) :
    M CFGEtop NoChoice (List (dtyp × dvalue)) :=
  map_monad (fun ((t, e), attrs) ↦ do
    let v ← denote_exp' (M := M) (some t) e
    return (t, ← Attributes.Worker.apply_attrs attrs msg t v)) args

def denote_operand_bundles (loc : IRString) (f : exp dtyp) (obs : List (@operand_bundle dtyp)) :
    M CFGEtop NoChoice Unit :=
  loop_monad (fun (ob : @operand_bundle dtyp) ↦ do
    let vs ← map_monad (fun
      | .SSA_value (t, e) => denote_exp' (M := M) (some t) e
      | .Metadata_string _ => pure NONE) ob.ob_ops
    match Attributes.Worker.bundle_check (M := M) (E := CFGEtop) (B := NoChoice) f ob.ob_tag with
    | some check => check loc vs
    | none => pure ()) obs

def denote_instr (i : (instr_id × instr dtyp) × List (metadata dtyp)) (varargs : Option Pa.PTR.ptr) :
    M CFGEtop NoChoice Unit := do
  let ((iid, ins), md) := i
  let info := get_file_info md
  Diagnostics.setLoc info
  let err_loc := fun () ↦ location_string info
  match iid, ins with
  | .IId id, .INSTR_Op op => lwrite id (← denote_exp' (M := M) none op)
  | .IId id, .INSTR_Alloca dt anns =>
    let align := Attributes.explicit_alignment anns
    let num ← match anns.findSome? ann_num_elements with
      | none => pure 1
      | some (t, e) => do
        let n ← denote_exp' (M := M) (some t) e
        if dvalue_is_poison n then
          raiseUB (err_loc () ++ ": Alloca with poison element count.".toUTF8)
        else
          let b ← EOU_to_itree (dvalue_to_dvalue_base n)
          pure (dvalue_base_int_unsigned b).toNat
    lwrite id (← alloca dt num align)
  | .IId id, .INSTR_Load dt (du, ptr) anns =>
    let a ← denote_exp' (M := M) (some du) ptr
    let loc := err_loc ()
    EOU_to_itree (Attributes.assert_alignment a anns
      (loc ++ ": Load with overestimated alignment.".toUTF8))
    let v ← load dt a
    let v ← EOU_to_itree (Attributes.apply_value_attrs (load_metadata_attrs md)
      (loc ++ ": Loaded value violates !noundef.".toUTF8) dt
      (Attributes.value_metadata_range (metadata_range md) dt v))
    Attributes.Worker.assert_load_dereferenceable md v
      (loc ++ ": Loaded value violates !dereferenceable.".toUTF8)
    lwrite id v
  | .IVoid _, .INSTR_Store (dt, val) (du, ptr) anns =>
    let v ← denote_exp' (M := M) (some dt) val
    let a ← denote_exp' (M := M) (some du) ptr
    let loc := err_loc ()
    EOU_to_itree (Attributes.assert_alignment a anns
      (loc ++ ": Store with overestimated alignment.".toUTF8))
    match a with
    | .DVALUE_Base .DVALUE_Poison => raiseUB (loc ++ ": Store to poisoned address.".toUTF8)
    | _ => store dt a v
  | .IId _, .INSTR_Store .. =>
    «raise» (err_loc () ++ ": ILL-FORMED itree ERROR: Store to non-void ID".toUTF8)
  | pt, .INSTR_Call (dt, f) args anns obs =>
    let loc := err_loc ()
    let vs ← denote_call_args args (loc ++ ": Call argument violates noundef.".toUTF8)
    denote_operand_bundles loc f obs
    let res ← match IntrinsicsDefinitions.intrinsic_exp f with
      | some s => intrinsic dt s vs varargs
      | none => do
        let fv ← denote_exp' (M := M) none f
        call dt (anns_cconv anns) fv vs
    let res ← Attributes.Worker.check_call_return (ann_fun_attributes anns) (ann_ret_attributes anns)
      (metadata_range md) (loc ++ ": Call".toUTF8) dt (vs.map Prod.snd) res
    match res with
    | .inl ex => raiseLLVM ex
    | .inr v => match pt with
      | .IVoid _ => pure ()
      | .IId id => lwrite id v
  | .IVoid _, .INSTR_Comment _ => pure ()
  | pt, .INSTR_VAArg (_, e) argty =>
    let ptrTy := DTYPE_Base DTYPE_Pointer
    let ptr ← denote_exp' (M := M) (some ptrTy) e
    let args ← load ptrTy ptr
    let v ← load argty args
    let ix ← EOU_to_itree (Pa.IPTR.from_Z 1)
    let next ← EOU_to_itree (Operations.Gep.eval_gep gep_no_flags argty args
      [.DVALUE_Base (.DVALUE_Iptr ix)])
    store ptrTy ptr next
    match pt with
    | .IVoid _ => pure ()
    | .IId id => lwrite id v
  | .IId id, .INSTR_AtomicCmpXchg cpx => denote_cmpxchg id cpx
  | .IId id, .INSTR_AtomicRMW armw => denote_atomicrmw id armw
  | _, .INSTR_Fence .. => pure ()
  | .IId id, .INSTR_LandingPad .. =>
    match ← stack_get_exc with
    | some ex => lwrite id ex
    | none => «raise» (err_loc () ++ ": landingpad reached with no in-flight exception".toUTF8)
  | .IVoid _, .INSTR_LandingPad .. => «raise» (err_loc () ++ ": landingpad must define a value".toUTF8)
  | _, _ => «raise» (err_loc () ++ ": ID / Instr mismatch void / non-void".toUTF8)

variable {N : ITree.Effect → ITree.Effect → Type → Type w} [Runtime N] [Diagnostics N]
variable [Instrumentation.Snapshots M] [Instrumentation.Snapshots N] (sim : Simulation M N)

local macro "instr_step " s:term : tactic => `(tactic| first
  | exact Simulation.pure $s _
  | exact denote_exp'_related $s _ _
  | exact Simulation.liftEOU $s _
  | exact Simulation.«raise» $s _
  | exact Simulation.raiseUB $s _
  | exact Simulation.raiseLLVM $s _
  | exact Simulation.lwrite $s _ _
  | exact Simulation.load $s _ _
  | exact Simulation.store $s _ _ _
  | exact Simulation.alloca $s _ _ _
  | exact Simulation.call $s _ _ _ _
  | exact Simulation.intrinsic $s _ _ _ _
  | exact Simulation.stack_get_exc $s
  | apply Simulation.bind $s
  | split
  | intro)

theorem denote_cmpxchg_related (id : raw_id) (cpx : cmpxchg dtyp) :
    sim.R (denote_cmpxchg id cpx) (denote_cmpxchg id cpx) := by
  rcases cpx with ⟨_, _, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩, _, _, _, _⟩
  simp only [denote_cmpxchg]
  repeat' instr_step sim

theorem denote_atomic_rmw_operation_related (op : atomic_rmw_operation) (dt : dtyp)
    (pv val : dvalue) :
    sim.R (denote_atomic_rmw_operation op dt pv val) (denote_atomic_rmw_operation op dt pv val) := by
  cases op <;> simp only [denote_atomic_rmw_operation] <;> repeat' instr_step sim

theorem denote_atomicrmw_related (id : raw_id) (armw : atomicrmw dtyp) :
    sim.R (denote_atomicrmw id armw) (denote_atomicrmw id armw) := by
  rcases armw with ⟨_, _, ⟨_, _⟩, ⟨_, _⟩, _, _, _⟩
  simp only [denote_atomicrmw]
  repeat' first | exact denote_atomic_rmw_operation_related sim _ _ _ _ | instr_step sim

theorem denote_call_args_related (args : List (texp dtyp × List param_attr)) (msg : IRString) :
    sim.R (denote_call_args args msg) (denote_call_args args msg) := by
  unfold denote_call_args
  apply sim.map_monad
  rintro ⟨⟨t, e⟩, attrs⟩
  exact sim.bind (denote_exp'_related sim _ e) fun v ↦
    sim.bind (Attributes.Worker.apply_attrs_congr sim attrs msg t v) fun _ ↦ sim.pure _

theorem denote_operand_bundles_related (loc : IRString) (f : exp dtyp)
    (obs : List (@operand_bundle dtyp)) :
    sim.R (denote_operand_bundles loc f obs) (denote_operand_bundles loc f obs) := by
  unfold denote_operand_bundles
  apply sim.loop_monad
  intro ob
  apply sim.bind
  · apply sim.map_monad
    rintro (⟨t, e⟩ | md)
    · exact denote_exp'_related sim (some t) e
    · exact sim.pure _
  · intro vs
    have h := Attributes.Worker.bundle_check_congr (E := CFGEtop) (B := NoChoice) sim f ob.ob_tag
    generalize Attributes.Worker.bundle_check (M := M) (E := CFGEtop) (B := NoChoice)
      f ob.ob_tag = l at h ⊢
    generalize Attributes.Worker.bundle_check (M := N) (E := CFGEtop) (B := NoChoice)
      f ob.ob_tag = r at h ⊢
    cases h with
    | none => exact sim.pure _
    | some h => exact h loc vs

theorem denote_instr_related (i : (instr_id × instr dtyp) × List (metadata dtyp))
    (varargs : Option Pa.PTR.ptr) : sim.R (denote_instr i varargs) (denote_instr i varargs) := by
  rcases i with ⟨⟨iid, ins⟩, md⟩
  unfold denote_instr
  refine sim.bind (sim.loc _) fun _ ↦ ?_
  cases iid <;> cases ins <;> try dsimp only
  all_goals
    repeat' first
      | exact denote_cmpxchg_related sim _ _
      | exact denote_atomicrmw_related sim _ _
      | exact denote_call_args_related sim _ _
      | exact denote_operand_bundles_related sim _ _ _
      | exact Attributes.Worker.assert_load_dereferenceable_congr sim _ _ _
      | exact Attributes.Worker.check_call_return_congr sim _ _ _ _ _ _ _
      | instr_step sim

end Worker

def denote_cmpxchg (id : raw_id) (cpx : cmpxchg dtyp) : CFGtop Unit :=
  Worker.denote_cmpxchg (M := CTree.CTree) id cpx

def denote_atomic_rmw_operation (op : atomic_rmw_operation) (dt : dtyp) (pv val : dvalue) :
    CFGtop dvalue := Worker.denote_atomic_rmw_operation (M := CTree.CTree) op dt pv val

def denote_atomicrmw (id : raw_id) (armw : atomicrmw dtyp) : CFGtop Unit :=
  Worker.denote_atomicrmw (M := CTree.CTree) id armw

def denote_call_args (args : List (texp dtyp × List param_attr)) (msg : IRString) :
    CFGtop (List (dtyp × dvalue)) := Worker.denote_call_args (M := CTree.CTree) args msg

def denote_operand_bundles (loc : IRString) (f : exp dtyp) (obs : List (@operand_bundle dtyp)) :
    CFGtop Unit := Worker.denote_operand_bundles (M := CTree.CTree) loc f obs

def denote_instr (i : (instr_id × instr dtyp) × List (metadata dtyp)) (varargs : Option Pa.PTR.ptr) :
    CFGtop Unit := Worker.denote_instr (M := CTree.CTree) i varargs

end Vellvm.Semantics.Denotation
