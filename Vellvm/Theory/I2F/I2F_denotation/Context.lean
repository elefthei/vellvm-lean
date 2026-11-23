module

public import Vellvm.Theory.I2F.Refinement.Basic
public import Vellvm.Semantics.Denotation.Frames

@[expose] public section
namespace Vellvm.Theory.I2F.I2F_denotation
open Semantics.Denotation Refinement
open Numeric.Rocqlib (option_rel)
open Utils.IntMaps (IntMap lookup)

def I2F_function_denotation (f : @function_denotation PInf) (g : @function_denotation PFin) : Prop :=
  ∀ cc t xs ys, I2F_targs xs ys →
    I2F_refine_CFG (Sum.LiftRel I2F_dvalue I2F_dvalue) (f cc t xs) (g cc t ys)

def I2F_ctx (l : IntMap (@function_denotation PInf)) (r : IntMap (@function_denotation PFin)) : Prop :=
  ∀ k, option_rel I2F_function_denotation (lookup k l) (lookup k r)

end Vellvm.Theory.I2F.I2F_denotation
