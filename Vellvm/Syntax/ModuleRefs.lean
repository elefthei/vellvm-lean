/- Port of Vellvm, Syntax/ModuleRefs.v. -/
module

public import Vellvm.Syntax.RawIdMaps
public import Vellvm.Utils.IntMaps

@[expose] public section
namespace Vellvm.Syntax.ModuleRefs
open LLVMAst RawIdMaps Utils.IntMaps

abbrev Entities (T : Type) := toplevel_entities T (block T × List (block T))
abbrev Callees := rmap (List param_attr × List (List param_attr))

def metadata_defs (tles : Entities T) : IntMap (metadata T) :=
  tles.foldl (init := empty) fun m e ↦ match e with
    | .TLE_Metadata (.METADATA_Id (.Anon n)) _ md => add n md m
    | _ => m

def attribute_groups (tles : Entities T) : IntMap (List fn_attr) :=
  tles.foldl (init := empty) fun m e ↦ match e with
    | .TLE_Attribute_group n attrs => add n attrs m
    | _ => m

/-- Substitute just the value in a kind/value pair, never recursively expand a metadata node. -/
def resolve_metadata (defs : IntMap (metadata T)) (md : metadata T) : metadata T :=
  match md with
  | .METADATA_Pair kind (.METADATA_Id (.Anon n)) =>
    match lookup n defs with | some node => .METADATA_Pair kind node | none => md
  | _ => md

def resolve_metadata_list (defs : IntMap (metadata T)) (mds : List (metadata T)) :=
  mds.map (resolve_metadata defs)

def expand_fn_attrs (groups : IntMap (List fn_attr)) (attrs : List fn_attr) : List fn_attr :=
  attrs.flatMap fun a ↦ match a with
    | .FNATTR_Attr_grp n => (lookup n groups).getD [a]
    | _ => [a]

def expand_annotations (groups : IntMap (List fn_attr)) (anns : List (annotation T)) :=
  anns.flatMap fun ann ↦ match ann with
    | .ANN_fun_attribute a => (expand_fn_attrs groups [a]).map ANN_fun_attribute
    | _ => [ann]

def expand_declaration (groups : IntMap (List fn_attr)) (d : declaration T) :=
  { d with dc_attrs := expand_fn_attrs groups d.dc_attrs }

def callee_attrs (tles : Entities T) : Callees :=
  tles.foldl (init := RM.empty _) fun m e ↦ match e with
    | .TLE_Declaration d => RM.add d.dc_name d.dc_param_attrs m
    | .TLE_Definition d => RM.add d.df_prototype.dc_name d.df_prototype.dc_param_attrs m
    | _ => m

def merge_arg_attrs : List (texp T × List param_attr) → List (List param_attr) → List (texp T × List param_attr)
  | (v, as) :: vs, ps :: pss => (v, as ++ ps) :: merge_arg_attrs vs pss
  | vs, _ => vs

def merge_callee_attrs (callees : Callees) (fn : texp T) (args : List (texp T × List param_attr))
    (anns : List (annotation T)) : List (texp T × List param_attr) × List (annotation T) :=
  match fn.2 with
  | .EXP_Ident (.ID_Global f) =>
    match rid_lookup f callees with
    | some (ret, params) => (merge_arg_attrs args params, anns ++ ret.map ANN_ret_attribute)
    | none => (args, anns)
  | _ => (args, anns)

def resolve_instr (groups : IntMap (List fn_attr)) (callees : Callees) (i : instr T) : instr T :=
  match i with
  | .INSTR_Call fn args anns obs =>
    let (args', anns') := merge_callee_attrs callees fn args anns
    .INSTR_Call fn args' (expand_annotations groups anns') obs
  | _ => i

def resolve_terminator (groups : IntMap (List fn_attr)) (callees : Callees) (t : terminator T) : terminator T :=
  match t with
  | .TERM_Invoke fn args toL unwind anns obs =>
    let (args', anns') := merge_callee_attrs callees fn args anns
    .TERM_Invoke fn args' toL unwind (expand_annotations groups anns') obs
  | _ => t

def resolve_block (defs : IntMap (metadata T)) (groups : IntMap (List fn_attr)) (callees : Callees)
    (b : block T) : block T :=
  let md := resolve_metadata_list defs
  let ((id, t), atts) := b.blk_term
  { b with
    blk_phis := b.blk_phis.map fun (p, mds) ↦ (p, md mds)
    blk_code := b.blk_code.map fun ((i, ins), mds) ↦ ((i, resolve_instr groups callees ins), md mds)
    blk_term := ((id, resolve_terminator groups callees t), md atts) }

def resolve_definition (defs : IntMap (metadata T)) (groups : IntMap (List fn_attr)) (callees : Callees)
    (d : definition T (block T × List (block T))) : definition T (block T × List (block T)) :=
  let resolve := resolve_block defs groups callees
  { d with df_prototype := expand_declaration groups d.df_prototype
           df_instrs := (resolve d.df_instrs.1, d.df_instrs.2.map resolve) }

/-- Apply to each translation unit before linking: numeric identifiers are module-local. -/
def resolve_module_refs (tles : Entities T) : Entities T :=
  let defs := metadata_defs tles
  let groups := attribute_groups tles
  let callees := callee_attrs tles
  tles.map fun
    | .TLE_Declaration d => .TLE_Declaration (expand_declaration groups d)
    | .TLE_Definition d => .TLE_Definition (resolve_definition defs groups callees d)
    | e => e

end Vellvm.Syntax.ModuleRefs
