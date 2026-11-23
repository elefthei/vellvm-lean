import PortChecks.SourceType
import PortChecks.Theory.I2F.I2F_exp.Unsigned
import Vellvm.Theory.I2F.I2F_exp.Operations

open Vellvm Vellvm.Syntax.DynamicTypes Vellvm.Syntax.LLVMAst
open Vellvm.Semantics.DynamicValues Vellvm.Semantics.EOU Vellvm.Semantics.Denotation
open Vellvm.Semantics.Operations.Conversion Vellvm.Semantics.Operations.Gep
open Vellvm.Semantics.Operations.Select
open Vellvm.Semantics.Attributes (denote_int_syntax)
open Vellvm.Theory.I2F.Refinement
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_convert_pure_base"
  I2F_convert_pure_base : ∀ (cv : pure_conversion) (t u : dtyp_base) {v : @dvalue_base PInf} {v' : @dvalue_base PFin},
    I2F_dvalue_base v v' → I2F_EOU I2F_dvalue_base
      (@convert_pure_base PInf cv t v u) (@convert_pure_base PFin cv t v' u)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_convert_pure"
  I2F_convert_pure : ∀ (cv : pure_conversion) (t u : dtyp) {v : @dvalue PInf} {v' : @dvalue PFin},
    I2F_dvalue v v' → I2F_EOU I2F_dvalue
      (@convert_pure PInf cv t v u) (@convert_pure PFin cv t v' u)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_convert"
  I2F_convert : ∀ (cv : conversion_type) (t u : dtyp) {v : @dvalue PInf} {v' : @dvalue PFin},
    I2F_dvalue v v' → I2F_refine
      (@convert PInf cv t v u) (@convert PFin cv t v' u)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_gep_indexable"
  I2F_gep_indexable : ∀ (t : dtyp),
    @gep_indexable PInf t = @gep_indexable PFin t

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_sequential_stride"
  I2F_sequential_stride : ∀ (v : Bool) (t : dtyp),
    @sequential_stride PInf v t = @sequential_stride PFin v t

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_gep_struct_field"
  I2F_gep_struct_field : ∀ (p : Bool) (ts : List dtyp) (n : Nat),
    @gep_struct_field PInf p ts n = @gep_struct_field PFin p ts n

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_gep_index"
  I2F_gep_index : ∀ {v : @dvalue PInf} {v' : @dvalue PFin},
    I2F_dvalue v v' → @gep_index PInf v = @gep_index PFin v'

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_gep_index_trunc_ok"
  I2F_gep_index_trunc_ok : ∀ (u : Bool) {v : @dvalue PInf} {v' : @dvalue PFin},
    I2F_dvalue v v' → @gep_index_trunc_ok PInf u v = @gep_index_trunc_ok PFin u v'

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_gep_trunc_violated"
  I2F_gep_trunc_violated : ∀ (flags : gep_flags) {vs : List (@dvalue PInf)} {ws : List (@dvalue PFin)},
    List.Forall₂ I2F_dvalue vs ws → @gep_trunc_violated PInf flags vs = @gep_trunc_violated PFin flags ws

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_gep_steps_h"
  I2F_gep_steps_h : ∀ {vs : List (@dvalue PInf)} {ws : List (@dvalue PFin)},
    List.Forall₂ I2F_dvalue vs ws → ∀ t : dtyp, @gep_steps_h PInf t vs = @gep_steps_h PFin t ws

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_gep_steps"
  I2F_gep_steps : ∀ (t : dtyp) {vs : List (@dvalue PInf)} {ws : List (@dvalue PFin)},
    List.Forall₂ I2F_dvalue vs ws → @gep_steps PInf t vs = @gep_steps PFin t ws

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_handle_gep_ptr"
  I2F_handle_gep_ptr : ∀ (flags : gep_flags) (t : dtyp) (a : PInf.PTR.ptr) (b : PFin.PTR.ptr) {vs : List (@dvalue PInf)} {ws : List (@dvalue PFin)},
    I2F_Addr a b → List.Forall₂ I2F_dvalue vs ws → I2F_EOUP I2F_Addr
      (@handle_gep_ptr PInf flags t a vs) (@handle_gep_ptr PFin flags t b ws)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_eval_gep"
  I2F_eval_gep : ∀ (flags : gep_flags) (t : dtyp) {v : @dvalue PInf} {vs : List (@dvalue PInf)}
    {v' : @dvalue PFin} {ws : List (@dvalue PFin)},
    I2F_dvalue v v' → List.Forall₂ I2F_dvalue vs ws → I2F_EOU I2F_dvalue
      (@eval_gep PInf flags t v vs) (@eval_gep PFin flags t v' ws)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_vector_index"
  I2F_vector_index : ∀ {v : @dvalue PInf} {v' : @dvalue PFin},
    I2F_dvalue v v' → @vector_index PInf v = @vector_index PFin v'

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_extract_element"
  I2F_extract_element : ∀ {a b : @dvalue PInf} {a' b' : @dvalue PFin},
    I2F_dvalue a a' → I2F_dvalue b b' →
    I2F_EOU I2F_dvalue
      (@extract_element PInf a b) (@extract_element PFin a' b')

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_insert_element"
  I2F_insert_element : ∀ (dt : dtyp) {a b c : @dvalue PInf} {a' b' c' : @dvalue PFin},
    I2F_dvalue a a' → I2F_dvalue b b' → I2F_dvalue c c' →
    I2F_EOU I2F_dvalue
      (@insert_element PInf dt a b c) (@insert_element PFin dt a' b' c')

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_shuffle_vector"
  I2F_shuffle_vector : ∀ (dt : dtyp) {a b c : @dvalue PInf} {a' b' c' : @dvalue PFin},
    I2F_dvalue a a' → I2F_dvalue b b' → I2F_dvalue c c' →
    I2F_EOU I2F_dvalue
      (@shuffle_vector PInf dt a b c) (@shuffle_vector PFin dt a' b' c')

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_extract_value"
  I2F_extract_value : ∀ (dt : dtyp) {a : @dvalue PInf} {a' : @dvalue PFin} (idxs : List int_syntax),
    I2F_dvalue a a' →
    I2F_EOU I2F_dvalue
      (@extract_value PInf dt a (idxs.map denote_int_syntax)) (@extract_value PFin dt a' (idxs.map denote_int_syntax))

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_insert_value"
  I2F_insert_value : ∀ (idxs : List int_syntax) (dt : dtyp) {a b : @dvalue PInf} {a' b' : @dvalue PFin},
    I2F_dvalue a a' → I2F_dvalue b b' →
    I2F_EOU I2F_dvalue
      (@insert_value PInf dt a b (idxs.map denote_int_syntax)) (@insert_value PFin dt a' b' (idxs.map denote_int_syntax))

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_eval_select_base_dvalue"
  I2F_eval_select_base_dvalue : ∀ {cond : @dvalue_base PInf} {cond' : @dvalue_base PFin}
    {a b : @dvalue PInf} {a' b' : @dvalue PFin},
    I2F_dvalue_base cond cond' → I2F_dvalue a a' → I2F_dvalue b b' →
    I2F_EOU I2F_dvalue
      (@eval_select_base_dvalue PInf cond a b) (@eval_select_base_dvalue PFin cond' a' b')

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_eval_select"
  I2F_eval_select : ∀ (dt : dtyp) {a b c : @dvalue PInf} {a' b' c' : @dvalue PFin},
    I2F_dvalue a a' → I2F_dvalue b b' → I2F_dvalue c c' →
    I2F_EOU I2F_dvalue
      (@eval_select PInf a dt b c) (@eval_select PFin a' dt b' c')

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_denote_exp"
  I2F_denote_exp : ∀ (e : exp dtyp) (τ : Option dtyp),
    I2F_refine (@denote_exp PInf τ e) (@denote_exp PFin τ e)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_denote_exp'"
  I2F_denote_exp' : ∀ (e : exp dtyp) (τ : Option dtyp),
    I2F_refine_CFG I2F_dvalue (@denote_exp' PInf τ e) (@denote_exp' PFin τ e)
