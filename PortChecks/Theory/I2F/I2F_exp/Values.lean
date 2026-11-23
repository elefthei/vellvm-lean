import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.Values

open Vellvm.Semantics.DynamicValues Vellvm.Syntax.DynamicTypes
open Vellvm.Theory.I2F.Refinement Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_dvalue_to_dvalue_base"
  I2F_dvalue_to_dvalue_base : ∀ {v : @dvalue PInf} {w : @dvalue PFin}, I2F_dvalue v w →
    I2F_EOU I2F_dvalue_base (@dvalue_to_dvalue_base PInf v) (@dvalue_to_dvalue_base PFin w)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|Forall2_map_Base"
  Forall2_map_Base : ∀ {xs : List (@dvalue_base PInf)} {ys : List (@dvalue_base PFin)},
    List.Forall₂ I2F_dvalue_base xs ys →
    List.Forall₂ I2F_dvalue (xs.map (@DVALUE_Base PInf)) (ys.map (@DVALUE_Base PFin))

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_dvalue_is_poison"
  I2F_dvalue_is_poison : ∀ {v : @dvalue PInf} {w : @dvalue PFin}, I2F_dvalue v w →
    @dvalue_is_poison PInf v = @dvalue_is_poison PFin w

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_forallb_is_poison"
  I2F_forallb_is_poison : ∀ {xs : List (@dvalue PInf)} {ys : List (@dvalue PFin)},
    List.Forall₂ I2F_dvalue xs ys → xs.all (@dvalue_is_poison PInf) = ys.all (@dvalue_is_poison PFin)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_fields_all_poison"
  I2F_fields_all_poison : ∀ (ts : List dtyp) {xs : List (@dvalue PInf)} {ys : List (@dvalue PFin)},
    List.Forall₂ I2F_dvalue xs ys → @fields_all_poison PInf ts xs = @fields_all_poison PFin ts ys

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_agg_is_poison"
  I2F_agg_is_poison : ∀ (t : dtyp) {xs : List (@dvalue PInf)} {ys : List (@dvalue PFin)},
    List.Forall₂ I2F_dvalue xs ys → @agg_is_poison PInf t xs = @agg_is_poison PFin t ys

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_canonicalize_agg"
  I2F_canonicalize_agg : ∀ (t : dtyp) {xs : List (@dvalue PInf)} {ys : List (@dvalue PFin)},
    List.Forall₂ I2F_dvalue xs ys → I2F_dvalue (@canonicalize_agg PInf t xs) (@canonicalize_agg PFin t ys)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_empty_dvalue_of_dtyp"
  I2F_empty_dvalue_of_dtyp : ∀ t : dtyp,
    I2F_dvalue (@empty_dvalue_of_dtyp PInf t) (@empty_dvalue_of_dtyp PFin t)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_poison_of_dtyp"
  I2F_poison_of_dtyp : ∀ t : dtyp, I2F_dvalue (@poison_of_dtyp PInf t) (@poison_of_dtyp PFin t)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_vector_elts"
  I2F_vector_elts : ∀ (n : Nat) {v : @dvalue PInf} {w : @dvalue PFin}, I2F_dvalue v w →
    match @vector_elts PInf n v, @vector_elts PFin n w with
    | some xs, some ys => List.Forall₂ I2F_dvalue xs ys
    | none, none => True
    | _, _ => False

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_dvalue_well_defined"
  I2F_dvalue_well_defined : ∀ {v : @dvalue PInf} {w : @dvalue PFin}, I2F_dvalue v w →
    @dvalue_well_defined PInf v = @dvalue_well_defined PFin w
