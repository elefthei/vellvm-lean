import PortChecks.SourceType
import Vellvm.Theory.I2F.I2F_exp.Freeze

open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.DynamicValues
open Vellvm.Semantics.LLVMEvents Vellvm.Semantics.Operations.Freeze Vellvm.Semantics.Denotation
open Vellvm.Syntax.DynamicTypes Vellvm.Syntax.LLVMAst Vellvm.Numeric.Integers
open Vellvm.Theory.I2F.Refinement Vellvm.Utils.ListUtil
open Vellvm.Utils.rutt_cutoff (pred1 prerel postrel ruttc_ret ruttc_bind ruttc_trigger)
open Vellvm.Tree (ruttc)
open CTree (CTree)
open ITree (Effect Subeffect)
open Vellvm.Theory.I2F.I2F_exp

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|refine_dvalue_base_map"
  refine_dvalue_base_map : ∀ {t₁ : @MCFGtop PInf (@dvalue_base PInf)} {t₂ : @MCFGtop PFin (@dvalue_base PFin)}
    (h : I2F_refine_MCFG I2F_dvalue_base t₁ t₂),
    I2F_refine_MCFG I2F_dvalue ((@DVALUE_Base PInf) <$> t₁) ((@DVALUE_Base PFin) <$> t₂)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|freeze_fields"
  freeze_fields : ∀ [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (vs : List dvalue) (ts : List dtyp) (acc : List dvalue),
    CTree E B (List dvalue)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|freeze_elts"
  freeze_elts : ∀ [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (t : dtyp) (vs acc : List dvalue),
    CTree E B (List dvalue)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|freeze_Base_eq"
  freeze_Base_eq : ∀ [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (t : dtyp) (v : dvalue_base),
    freeze (E := E) (B := B) t (DVALUE_Base v) = freeze_base t v

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|freeze_Struct_eq"
  freeze_Struct_eq : ∀ [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (packed : Bool) (vs : List dvalue) (dt : dtyp),
    freeze (E := E) (B := B) dt (DVALUE_Struct packed vs) = match dt with
      | .DTYPE_Struct p ts => do return DVALUE_Struct p (← freeze_fields vs ts [])
      | _ => LLVMEvents.«raise» "freeze: type mismatch non-struct type".toUTF8

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|freeze_Array_eq"
  freeze_Array_eq : ∀ [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (vec : Bool) (vs : List dvalue) (dt : dtyp),
    freeze (E := E) (B := B) dt (DVALUE_Array vec vs) = match dt with
      | .DTYPE_Array v _ t => do return DVALUE_Array v (← freeze_elts t vs [])
      | _ => LLVMEvents.«raise» "freeze: type mismatch non-array type".toUTF8

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|freeze_fields_nil"
  freeze_fields_nil : ∀ [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (acc : List dvalue),
    freeze_fields (E := E) (B := B) [] [] acc = pure (acc.reverseAux [])

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|freeze_fields_nil_cons"
  freeze_fields_nil_cons : ∀ [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (t : dtyp) (ts : List dtyp) (acc : List dvalue),
    freeze_fields (E := E) (B := B) [] (t :: ts) acc = LLVMEvents.«raise» "freeze_fields: mismatched field types and values".toUTF8

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|freeze_fields_cons_nil"
  freeze_fields_cons_nil : ∀ [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (v : dvalue) (vs acc : List dvalue),
    freeze_fields (E := E) (B := B) (v :: vs) [] acc = LLVMEvents.«raise» "freeze_fields: mismatched field types and values".toUTF8

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|freeze_fields_cons"
  freeze_fields_cons : ∀ [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (v : dvalue) (vs : List dvalue) (t : dtyp) (ts : List dtyp) (acc : List dvalue),
    freeze_fields (E := E) (B := B) (v :: vs) (t :: ts) acc =
      (freeze t v >>= fun x ↦ freeze_fields vs ts (x :: acc))

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|freeze_elts_nil"
  freeze_elts_nil : ∀ [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (t : dtyp) (acc : List dvalue),
    freeze_elts (E := E) (B := B) t [] acc = pure (acc.reverseAux [])

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|freeze_elts_cons"
  freeze_elts_cons : ∀ [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (t : dtyp) (v : dvalue) (vs acc : List dvalue),
    freeze_elts (E := E) (B := B) t (v :: vs) acc =
      (freeze t v >>= fun x ↦ freeze_elts t vs (x :: acc))

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_freeze_bits"
  I2F_freeze_bits : ∀ (z : Int) {bs : List (@memory_bit PInf)} {cs : List (@memory_bit PFin)} (i : Nat)
    (h : List.Forall₂ I2F_memory_bit bs cs),
    List.Forall₂ I2F_memory_bit (@freeze_bits PInf z i bs) (@freeze_bits PFin z i cs)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_existsb_poison_bits"
  I2F_existsb_poison_bits : ∀ {bs : List (@memory_bit PInf)} {cs : List (@memory_bit PFin)}
    (h : List.Forall₂ I2F_memory_bit bs cs),
    bs.any (@is_poison_bit PInf) = cs.any (@is_poison_bit PFin)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_forallb_int_bits"
  I2F_forallb_int_bits : ∀ {bs : List (@memory_bit PInf)} {cs : List (@memory_bit PFin)}
    (h : List.Forall₂ I2F_memory_bit bs cs),
    bs.all (@is_int_bit PInf) = cs.all (@is_int_bit PFin)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_int_bits_to_Z"
  I2F_int_bits_to_Z : ∀ {bs : List (@memory_bit PInf)} {cs : List (@memory_bit PFin)}
    (h : List.Forall₂ I2F_memory_bit bs cs),
    @int_bits_to_Z PInf bs = @int_bits_to_Z PFin cs

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_draw_Z"
  I2F_draw_Z : ∀ {a : @dvalue PInf} {b : @dvalue PFin} (h : I2F_dvalue a b),
    (letI := PInf; (fun v : dvalue ↦ match v with
      | .DVALUE_Base (.DVALUE_I _ i) => unsigned i | _ => 0) a) =
    (letI := PFin; (fun v : dvalue ↦ match v with
      | .DVALUE_Base (.DVALUE_I _ i) => unsigned i | _ => 0) b)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_freeze_mixed_bits"
  I2F_freeze_mixed_bits : ∀ (sz : Positive) {z z' : Int} {bs : List (@memory_bit PInf)} {cs : List (@memory_bit PFin)}
    (hz : z = z') (h : List.Forall₂ I2F_memory_bit bs cs),
    I2F_dvalue_bv (@freeze_mixed_bits PInf sz z bs) (@freeze_mixed_bits PFin sz z' cs)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_freeze_base_gen"
  I2F_freeze_base_gen : ∀ {E F B : Effect}
    [@DrawE PInf -< E] [ef : FailureE -< E] [OOME -< E] [UBE -< E]
    [@DrawE PFin -< F] [ff : FailureE -< F] [OOME -< F] [UBE -< F]
    {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F}
    (hd : ∀ t, ruttc (B := B) L K V A I2F_dvalue (draw (Pa := PInf) t) (draw (Pa := PFin) t))
    (dt : dtyp) {a : @dvalue_base PInf} {b : @dvalue_base PFin} (h : I2F_dvalue_base a b),
    ruttc (B := B) L K V A I2F_dvalue (freeze_base (Pa := PInf) dt a) (freeze_base (Pa := PFin) dt b)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_raise_gen"
  I2F_raise_gen : ∀ {E F B : Effect} [ef : FailureE -< E] [ff : FailureE -< F]
    {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F}
    (hf : ∀ u v : Unit, V (requestIn (D := FailureE) (Throw u))
      (requestIn (D := FailureE) (Throw v)))
    {X Y : Type} (R : X → Y → Prop) (s t : IRString),
    ruttc (B := B) L K V A R (LLVMEvents.«raise» s) (LLVMEvents.«raise» t)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_freeze_fields_gen"
  I2F_freeze_fields_gen : ∀ {E F B : Effect}
    [@DrawE PInf -< E] [ef : FailureE -< E] [OOME -< E] [UBE -< E]
    [@DrawE PFin -< F] [ff : FailureE -< F] [OOME -< F] [UBE -< F]
    {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F}
    (hf : ∀ u v : Unit, V (requestIn (D := FailureE) (Throw u))
      (requestIn (D := FailureE) (Throw v)))
    {xs : List (@dvalue PInf)} {ys : List (@dvalue PFin)}
    (hs : List.Forall₂ (fun a b ↦ ∀ t, ruttc (B := B) L K V A I2F_dvalue
      (freeze (Pa := PInf) t a) (freeze (Pa := PFin) t b)) xs ys)
    (dts : List dtyp) {acc : List (@dvalue PInf)} {acc' : List (@dvalue PFin)}
    (ha : List.Forall₂ I2F_dvalue acc acc'),
    ruttc (B := B) L K V A (List.Forall₂ I2F_dvalue)
      (freeze_fields (Pa := PInf) xs dts acc) (freeze_fields (Pa := PFin) ys dts acc')

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_freeze_elts_gen"
  I2F_freeze_elts_gen : ∀ {E F B : Effect}
    [@DrawE PInf -< E] [ef : FailureE -< E] [OOME -< E] [UBE -< E]
    [@DrawE PFin -< F] [ff : FailureE -< F] [OOME -< F] [UBE -< F]
    {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F}
    (t : dtyp) {xs : List (@dvalue PInf)} {ys : List (@dvalue PFin)}
    (hs : List.Forall₂ (fun a b ↦ ∀ t, ruttc (B := B) L K V A I2F_dvalue
      (freeze (Pa := PInf) t a) (freeze (Pa := PFin) t b)) xs ys)
    {acc : List (@dvalue PInf)} {acc' : List (@dvalue PFin)}
    (ha : List.Forall₂ I2F_dvalue acc acc'),
    ruttc (B := B) L K V A (List.Forall₂ I2F_dvalue)
      (freeze_elts (Pa := PInf) t xs acc) (freeze_elts (Pa := PFin) t ys acc')

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_freeze_gen"
  I2F_freeze_gen : ∀ {E F B : Effect}
    [@DrawE PInf -< E] [ef : FailureE -< E] [OOME -< E] [UBE -< E]
    [@DrawE PFin -< F] [ff : FailureE -< F] [OOME -< F] [UBE -< F]
    {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F}
    (hd : ∀ t, ruttc (B := B) L K V A I2F_dvalue (draw (Pa := PInf) t) (draw (Pa := PFin) t))
    (hf : ∀ u v : Unit, V (requestIn (D := FailureE) (Throw u))
      (requestIn (D := FailureE) (Throw v)))
    (dt : dtyp) {a : @dvalue PInf} {b : @dvalue PFin} (h : I2F_dvalue a b),
    ruttc (B := B) L K V A I2F_dvalue (freeze (Pa := PInf) dt a) (freeze (Pa := PFin) dt b)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_draw_MCFG"
  I2F_draw_MCFG : ∀ (dt : dtyp),
    I2F_refine_MCFG I2F_dvalue (draw (Pa := PInf) dt) (draw (Pa := PFin) dt)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_freeze_base"
  I2F_freeze_base : ∀ (dt : dtyp) {a : @dvalue_base PInf} {b : @dvalue_base PFin} (h : I2F_dvalue_base a b),
    I2F_refine (freeze_base (Pa := PInf) dt a) (freeze_base (Pa := PFin) dt b)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_freeze"
  I2F_freeze : ∀ (dt : dtyp) {a : @dvalue PInf} {b : @dvalue PFin} (h : I2F_dvalue a b),
    I2F_refine (freeze (Pa := PInf) dt a) (freeze (Pa := PFin) dt b)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_denote_int_syntax_as_int"
  I2F_denote_int_syntax_as_int : ∀ (t : dtyp) (x : int_syntax),
    I2F_EOU I2F_dvalue (@denote_int_syntax_as_int PInf t x) (@denote_int_syntax_as_int PFin t x)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_denote_float_syntax_as_float"
  I2F_denote_float_syntax_as_float : ∀ (t : dtyp) (x : float_syntax),
    I2F_EOU I2F_dvalue (@denote_float_syntax_as_float PInf t x) (@denote_float_syntax_as_float PFin t x)

#source_check "src/rocq/Theory/I2F/I2F_exp.v|Vellvm.Theory.I2F.I2F_exp|I2F_default_dvalue_of_dtyp"
  I2F_default_dvalue_of_dtyp : ∀ (t : dtyp),
    I2F_EOU I2F_dvalue (@default_dvalue_of_dtyp PInf t) (@default_dvalue_of_dtyp PFin t)
