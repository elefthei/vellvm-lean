import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_interp.State

open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_memory Vellvm.Theory.I2F.I2F_interp
open Vellvm.Semantics.Handlers Vellvm.Semantics.InterpretationStack Vellvm.Numeric.Rocqlib

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_env"
  I2F_env : @Local.local_env PInf → @Local.local_env PFin → Prop
#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_local_env"
  I2F_local_env : @Local.local_env PInf → @Local.local_env PFin → Prop
#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_global_env"
  I2F_global_env : @Global.global_env PInf → @Global.global_env PFin → Prop
#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_stack_frame"
  I2F_stack_frame : @Stack.stack_frame PInf → @Stack.stack_frame PFin → Prop
#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_stack"
  I2F_stack : @Stack.stack PInf → @Stack.stack PFin → Prop
#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|I2F_FusedS"
  I2F_FusedS : @FusedS PInf → @FusedS PFin → Prop

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|Build_I2F_stack_frame"
  Build_I2F_stack_frame : ∀ (f : @Stack.stack_frame PInf) (g : @Stack.stack_frame PFin),
    I2F_local_env (@Stack.stack_vars PInf f) (@Stack.stack_vars PFin g) →
    option_rel I2F_dvalue (@Stack.stack_exc PInf f) (@Stack.stack_exc PFin g) →
    @Stack.stack_loc PInf f = @Stack.stack_loc PFin g → I2F_stack_frame f g
#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|i2f_sf_vars"
  i2f_sf_vars : ∀ {f g}, I2F_stack_frame f g → I2F_local_env (@Stack.stack_vars PInf f) (@Stack.stack_vars PFin g)
#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|i2f_sf_exc"
  i2f_sf_exc : ∀ {f g}, I2F_stack_frame f g → option_rel I2F_dvalue (@Stack.stack_exc PInf f) (@Stack.stack_exc PFin g)
#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|i2f_sf_loc"
  i2f_sf_loc : ∀ {f g}, I2F_stack_frame f g → @Stack.stack_loc PInf f = @Stack.stack_loc PFin g

#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|Build_I2F_FusedS"
  Build_I2F_FusedS : ∀ (s : @FusedS PInf) (t : @FusedS PFin),
    I2F_State s.1 t.1 → I2F_stack_frame s.2.1.1 t.2.1.1 → I2F_stack s.2.1.2 t.2.1.2 →
    I2F_global_env s.2.2 t.2.2 → I2F_FusedS s t
#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|i2f_fs_mem"
  i2f_fs_mem : ∀ {s t}, I2F_FusedS s t → I2F_State s.1 t.1
#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|i2f_fs_frame"
  i2f_fs_frame : ∀ {s t}, I2F_FusedS s t → I2F_stack_frame s.2.1.1 t.2.1.1
#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|i2f_fs_stack"
  i2f_fs_stack : ∀ {s t}, I2F_FusedS s t → I2F_stack s.2.1.2 t.2.1.2
#source_check "src/rocq/Theory/I2F/I2F_interp.v|Vellvm.Theory.I2F.I2F_interp|i2f_fs_genv"
  i2f_fs_genv : ∀ {s t}, I2F_FusedS s t → I2F_global_env s.2.2 t.2.2
