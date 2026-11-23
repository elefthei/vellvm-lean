import Vellvm.Syntax.ModuleRefs

open Vellvm.Syntax.LLVMAst Vellvm.Syntax.ModuleRefs

-- No source proof declarations. Check the per-module boundary at the full AST type.
example {T : Type} : toplevel_entities T (block T × List (block T)) →
    toplevel_entities T (block T × List (block T)) := resolve_module_refs

-- A self-reference inside the replacement node is not recursively expanded.
example {T : Type} (kind : metadata T) :
    let id : metadata T := METADATA_Id (Anon 1)
    let defs := metadata_defs [TLE_Metadata id false (METADATA_Node [id])]
    resolve_metadata defs (METADATA_Pair kind id) = METADATA_Pair kind (METADATA_Node [id]) := rfl

-- Parameter attributes are appended to, rather than replacing, the call-site attributes;
-- extra varargs keep their original attributes.
example {T : Type} (x y : texp T) :
    merge_arg_attrs [(x, [PARAMATTR_Noundef]), (y, [PARAMATTR_Inreg])] [[PARAMATTR_Nonnull]] =
      [(x, [PARAMATTR_Noundef, PARAMATTR_Nonnull]), (y, [PARAMATTR_Inreg])] := rfl
