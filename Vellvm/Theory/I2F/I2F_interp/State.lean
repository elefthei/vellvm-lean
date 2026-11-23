import Vellvm.Semantics.InterpretationStack
import Vellvm.Theory.I2F.I2F_memory.State

namespace Vellvm.Theory.I2F.I2F_interp
open Refinement I2F_memory Semantics.Handlers Semantics.InterpretationStack
open Syntax.RawIdMaps Numeric.Rocqlib

def I2F_env : @Local.local_env PInf → @Local.local_env PFin → Prop := RM_Refine I2F_dvalue
def I2F_local_env : @Local.local_env PInf → @Local.local_env PFin → Prop := I2F_env
def I2F_global_env : @Global.global_env PInf → @Global.global_env PFin → Prop := I2F_env

structure I2F_stack_frame (f : @Stack.stack_frame PInf) (g : @Stack.stack_frame PFin) : Prop where
  Build_I2F_stack_frame ::
  i2f_sf_vars : I2F_local_env (@Stack.stack_vars PInf f) (@Stack.stack_vars PFin g)
  i2f_sf_exc : option_rel I2F_dvalue (@Stack.stack_exc PInf f) (@Stack.stack_exc PFin g)
  i2f_sf_loc : @Stack.stack_loc PInf f = @Stack.stack_loc PFin g

export I2F_stack_frame (Build_I2F_stack_frame i2f_sf_vars i2f_sf_exc i2f_sf_loc)

def I2F_stack : @Stack.stack PInf → @Stack.stack PFin → Prop := List.Forall₂ I2F_stack_frame

structure I2F_FusedS (s : @FusedS PInf) (t : @FusedS PFin) : Prop where
  Build_I2F_FusedS ::
  i2f_fs_mem : I2F_State s.1 t.1
  i2f_fs_frame : I2F_stack_frame s.2.1.1 t.2.1.1
  i2f_fs_stack : I2F_stack s.2.1.2 t.2.1.2
  i2f_fs_genv : I2F_global_env s.2.2 t.2.2

export I2F_FusedS (Build_I2F_FusedS i2f_fs_mem i2f_fs_frame i2f_fs_stack i2f_fs_genv)

end Vellvm.Theory.I2F.I2F_interp
