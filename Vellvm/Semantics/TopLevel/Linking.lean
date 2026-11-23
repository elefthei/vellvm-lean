/- Port of Semantics/TopLevel.v: module-local resolution and left-priority linking. -/
module

public import Vellvm.Syntax.ModuleRefs

@[expose] public section
namespace Vellvm.Semantics.TopLevel
open Syntax.LLVMAst Syntax.ModuleRefs

abbrev ll_toplevel_entity := toplevel_entity typ (block typ × List (block typ))
abbrev ll_toplevel_entities := List ll_toplevel_entity

def PREDEFINED_FUNCTIONS : ll_toplevel_entities := []

def userdecl_defined_in (name : IRString) (predefs : ll_toplevel_entities) : Bool :=
  predefs.any fun
    | .TLE_Definition df => match df.df_prototype.dc_name with
      | .Name n => name == n
      | _ => false
    | _ => false

def decl_defined_in (tle : ll_toplevel_entity) (predefs : ll_toplevel_entities) : Bool :=
  match tle with
  | .TLE_Declaration d => match d.dc_name with
    | .Name n => userdecl_defined_in n predefs
    | _ => false
  | _ => false

def defines_decl (predefs : ll_toplevel_entities) (tle : ll_toplevel_entity) : Bool :=
  decl_defined_in tle predefs

def link (predefs userprog : ll_toplevel_entities) : ll_toplevel_entities :=
  predefs ++ userprog.filter fun tle ↦ !defines_decl predefs tle

def link_all (linked_files : List ll_toplevel_entities) (userprog : ll_toplevel_entities) :
    ll_toplevel_entities :=
  linked_files.foldl (fun prog linked ↦ link (resolve_module_refs linked) prog)
    (resolve_module_refs userprog)

end Vellvm.Semantics.TopLevel
