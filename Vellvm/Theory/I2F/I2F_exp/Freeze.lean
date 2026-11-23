import Vellvm.Theory.I2F.Refinement.TreeLaws
import Vellvm.Semantics.Operations.Freeze
import Vellvm.Semantics.Denotation.Expressions

namespace Vellvm.Theory.I2F.I2F_exp
open Vellvm Vellvm.Semantics Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.DynamicValues
open Vellvm.Semantics.LLVMEvents Vellvm.Semantics.Operations.Freeze Vellvm.Semantics.Denotation
open Vellvm.Syntax.DynamicTypes Vellvm.Syntax.LLVMAst Vellvm.Numeric.Integers
open Vellvm.Theory.I2F.Refinement Vellvm.Utils.ListUtil
open Vellvm.Utils.rutt_cutoff (pred1 prerel postrel ruttc_ret ruttc_bind ruttc_trigger)
open Vellvm.Tree (ruttc)
open CTree (CTree)
open ITree (Effect Subeffect)

theorem refine_dvalue_base_map {t₁ : @MCFGtop PInf (@dvalue_base PInf)} {t₂ : @MCFGtop PFin (@dvalue_base PFin)}
    (h : I2F_refine_MCFG I2F_dvalue_base t₁ t₂) :
    I2F_refine_MCFG I2F_dvalue ((@DVALUE_Base PInf) <$> t₁) ((@DVALUE_Base PFin) <$> t₂) :=
  refine_dvalue_base_map_gen _ _ h

def freeze_fields [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (vs : List dvalue) (ts : List dtyp) (acc : List dvalue) :
    CTree E B (List dvalue) := Operations.Freeze.Worker.freezeFields ts vs acc

def freeze_elts [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (t : dtyp) (vs acc : List dvalue) :
    CTree E B (List dvalue) := Operations.Freeze.Worker.freezeElts t vs acc

theorem freeze_Base_eq [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (t : dtyp) (v : dvalue_base) :
    freeze (E := E) (B := B) t (DVALUE_Base v) = freeze_base t v := rfl

theorem freeze_Struct_eq [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (packed : Bool) (vs : List dvalue) (dt : dtyp) :
    freeze (E := E) (B := B) dt (DVALUE_Struct packed vs) = match dt with
      | .DTYPE_Struct p ts => do return DVALUE_Struct p (← freeze_fields vs ts [])
      | _ => LLVMEvents.«raise» "freeze: type mismatch non-struct type".toUTF8 := by cases dt <;> rfl

theorem freeze_Array_eq [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (vec : Bool) (vs : List dvalue) (dt : dtyp) :
    freeze (E := E) (B := B) dt (DVALUE_Array vec vs) = match dt with
      | .DTYPE_Array v _ t => do return DVALUE_Array v (← freeze_elts t vs [])
      | _ => LLVMEvents.«raise» "freeze: type mismatch non-array type".toUTF8 := by cases dt <;> rfl

theorem freeze_fields_nil [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (acc : List dvalue) :
    freeze_fields (E := E) (B := B) [] [] acc = pure (acc.reverseAux []) := rfl

theorem freeze_fields_nil_cons [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (t : dtyp) (ts : List dtyp) (acc : List dvalue) :
    freeze_fields (E := E) (B := B) [] (t :: ts) acc = LLVMEvents.«raise» "freeze_fields: mismatched field types and values".toUTF8 := rfl

theorem freeze_fields_cons_nil [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (v : dvalue) (vs acc : List dvalue) :
    freeze_fields (E := E) (B := B) (v :: vs) [] acc = LLVMEvents.«raise» "freeze_fields: mismatched field types and values".toUTF8 := rfl

theorem freeze_fields_cons [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (v : dvalue) (vs : List dvalue) (t : dtyp) (ts : List dtyp) (acc : List dvalue) :
    freeze_fields (E := E) (B := B) (v :: vs) (t :: ts) acc =
      (freeze t v >>= fun x ↦ freeze_fields vs ts (x :: acc)) := rfl

theorem freeze_elts_nil [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (t : dtyp) (acc : List dvalue) :
    freeze_elts (E := E) (B := B) t [] acc = pure (acc.reverseAux []) := rfl

theorem freeze_elts_cons [Pa : Params] {E B : Effect}
    [DrawE -< E] [FailureE -< E] [OOME -< E] [UBE -< E]
    (t : dtyp) (v : dvalue) (vs acc : List dvalue) :
    freeze_elts (E := E) (B := B) t (v :: vs) acc =
      (freeze t v >>= fun x ↦ freeze_elts t vs (x :: acc)) := rfl

theorem I2F_freeze_bits (z : Int) {bs : List (@memory_bit PInf)} {cs : List (@memory_bit PFin)} (i : Nat)
    (h : List.Forall₂ I2F_memory_bit bs cs) :
    List.Forall₂ I2F_memory_bit (@freeze_bits PInf z i bs) (@freeze_bits PFin z i cs) := by
  induction h generalizing i with
  | nil => exact .nil
  | cons hb _ ih =>
    cases hb with
    | I2F_Bit_ptr p p' idx hp => exact .cons (.I2F_Bit_ptr p p' idx hp) (ih (i+1))
    | I2F_Bit_psn => exact .cons (.I2F_Bit_bit _) (ih (i+1))
    | I2F_Bit_bit b => exact .cons (.I2F_Bit_bit b) (ih (i+1))

theorem I2F_existsb_poison_bits {bs : List (@memory_bit PInf)} {cs : List (@memory_bit PFin)}
    (h : List.Forall₂ I2F_memory_bit bs cs) :
    bs.any (@is_poison_bit PInf) = cs.any (@is_poison_bit PFin) := by
  induction h with
  | nil => rfl
  | cons hb _ ih => cases hb <;> simp only [List.any_cons, is_poison_bit, ih]

theorem I2F_forallb_int_bits {bs : List (@memory_bit PInf)} {cs : List (@memory_bit PFin)}
    (h : List.Forall₂ I2F_memory_bit bs cs) :
    bs.all (@is_int_bit PInf) = cs.all (@is_int_bit PFin) := by
  induction h with
  | nil => rfl
  | cons hb _ ih => cases hb <;> simp only [List.all_cons, is_int_bit, ih]

theorem I2F_int_bits_to_Z {bs : List (@memory_bit PInf)} {cs : List (@memory_bit PFin)}
    (h : List.Forall₂ I2F_memory_bit bs cs) :
    @int_bits_to_Z PInf bs = @int_bits_to_Z PFin cs := by
  induction h with
  | nil => rfl
  | cons hb _ ih => cases hb <;> simp only [int_bits_to_Z, ih]

theorem I2F_draw_Z {a : @dvalue PInf} {b : @dvalue PFin} (h : I2F_dvalue a b) :
    (letI := PInf; (fun v : dvalue ↦ match v with
      | .DVALUE_Base (.DVALUE_I _ i) => unsigned i | _ => 0) a) =
    (letI := PFin; (fun v : dvalue ↦ match v with
      | .DVALUE_Base (.DVALUE_I _ i) => unsigned i | _ => 0) b) := by
  cases h with
  | I2F_dvalue_Base hb => cases hb <;> rfl
  | _ => rfl

theorem I2F_freeze_mixed_bits (sz : Positive) {z z' : Int} {bs : List (@memory_bit PInf)} {cs : List (@memory_bit PFin)}
    (hz : z = z') (h : List.Forall₂ I2F_memory_bit bs cs) :
    I2F_dvalue_bv (@freeze_mixed_bits PInf sz z bs) (@freeze_mixed_bits PFin sz z' cs) := by
  subst z'
  have h' := I2F_freeze_bits z 0 h
  dsimp only [freeze_mixed_bits]
  rw [I2F_forallb_int_bits h', I2F_int_bits_to_Z h']
  split
  · exact .I2F_BYTE_I _
  · exact .I2F_BYTE_Mixed h'

theorem I2F_freeze_base_gen {E F B : Effect}
    [@DrawE PInf -< E] [ef : FailureE -< E] [OOME -< E] [UBE -< E]
    [@DrawE PFin -< F] [ff : FailureE -< F] [OOME -< F] [UBE -< F]
    {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F}
    (hd : ∀ t, ruttc (B := B) L K V A I2F_dvalue (draw (Pa := PInf) t) (draw (Pa := PFin) t))
    (dt : dtyp) {a : @dvalue_base PInf} {b : @dvalue_base PFin} (h : I2F_dvalue_base a b) :
    ruttc (B := B) L K V A I2F_dvalue (freeze_base (Pa := PInf) dt a) (freeze_base (Pa := PFin) dt b) := by
  cases h with
  | I2F_dvalue_Poison => exact hd dt
  | I2F_dvalue_B hb =>
    cases hb with
    | I2F_BYTE_I i => exact ruttc_ret _ _ (I2F_dvalue_Base (.I2F_dvalue_B (.I2F_BYTE_I i)))
    | I2F_BYTE_Pointer p q n hp =>
      exact ruttc_ret _ _ (I2F_dvalue_Base (.I2F_dvalue_B (.I2F_BYTE_Pointer p q n hp)))
    | @I2F_BYTE_Mixed bs cs hs =>
      simp only [freeze_base, Operations.Freeze.Worker.freeze_base, I2F_existsb_poison_bits hs]
      split
      · refine ruttc_bind L K V A I2F_dvalue _ _ _ _ _ (hd _) fun x y hxy ↦ ?_
        exact ruttc_ret _ _ (I2F_dvalue_Base (.I2F_dvalue_B
          (I2F_freeze_mixed_bits _ (I2F_draw_Z hxy) hs)))
      · exact ruttc_ret _ _ (I2F_dvalue_Base (.I2F_dvalue_B (.I2F_BYTE_Mixed hs)))
  | I2F_dvalue_Pointer p q hp => exact ruttc_ret _ _ (I2F_dvalue_Base (.I2F_dvalue_Pointer p q hp))
  | I2F_dvalue_Int i => exact ruttc_ret _ _ (I2F_dvalue_Base (.I2F_dvalue_Int i))
  | I2F_dvalue_Ptr hp => exact ruttc_ret _ _ (I2F_dvalue_Base (.I2F_dvalue_Ptr hp))
  | I2F_dvalue_Double x => exact ruttc_ret _ _ (I2F_dvalue_Base (.I2F_dvalue_Double x))
  | I2F_dvalue_Float x => exact ruttc_ret _ _ (I2F_dvalue_Base (.I2F_dvalue_Float x))
  | I2F_dvalue_None => exact ruttc_ret _ _ (I2F_dvalue_Base .I2F_dvalue_None)

theorem I2F_raise_gen {E F B : Effect} [ef : FailureE -< E] [ff : FailureE -< F]
    {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F}
    (hf : ∀ u v : Unit, V (requestIn (D := FailureE) (Throw u))
      (requestIn (D := FailureE) (Throw v)))
    {X Y : Type} (R : X → Y → Prop) (s t : IRString) :
    ruttc (B := B) L K V A R (LLVMEvents.«raise» s) (LLVMEvents.«raise» t) := by
  change ruttc L K V A R
    ((pure () : CTree E B Unit) >>= fun _ ↦
      ((CTree.trigger (requestIn (D := FailureE) (Throw ())) >>= fun x ↦ pure ((ef.map (Throw ())).2 x)) >>=
        fun a ↦ (nomatch a : CTree E B X)))
    ((pure () : CTree F B Unit) >>= fun _ ↦
      ((CTree.trigger (requestIn (D := FailureE) (Throw ())) >>= fun y ↦ pure ((ff.map (Throw ())).2 y)) >>=
        fun b ↦ (nomatch b : CTree F B Y)))
  apply Tree.related_iff.mpr
  simp only [CTree.pure_bind', CTree.CTree.trigger, CTree.vis_bind, CTree.unfold_vis]
  exact .vis (hf () ()) fun x _ _ ↦ Empty.elim ((ef.map (Throw ())).2 x)

theorem I2F_freeze_fields_gen {E F B : Effect}
    [@DrawE PInf -< E] [ef : FailureE -< E] [OOME -< E] [UBE -< E]
    [@DrawE PFin -< F] [ff : FailureE -< F] [OOME -< F] [UBE -< F]
    {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F}
    (hf : ∀ u v : Unit, V (requestIn (D := FailureE) (Throw u))
      (requestIn (D := FailureE) (Throw v)))
    {xs : List (@dvalue PInf)} {ys : List (@dvalue PFin)}
    (hs : List.Forall₂ (fun a b ↦ ∀ t, ruttc (B := B) L K V A I2F_dvalue
      (freeze (Pa := PInf) t a) (freeze (Pa := PFin) t b)) xs ys)
    (dts : List dtyp) {acc : List (@dvalue PInf)} {acc' : List (@dvalue PFin)}
    (ha : List.Forall₂ I2F_dvalue acc acc') :
    ruttc (B := B) L K V A (List.Forall₂ I2F_dvalue)
      (freeze_fields (Pa := PInf) xs dts acc) (freeze_fields (Pa := PFin) ys dts acc') := by
  induction hs generalizing dts acc acc' with
  | nil =>
    cases dts with
    | nil => exact ruttc_ret _ _ (Forall2_rev_append _ _ _ ha [] [] .nil)
    | cons t ts => exact I2F_raise_gen hf _ _ _
  | cons hv _ ih =>
    cases dts with
    | nil => exact I2F_raise_gen hf _ _ _
    | cons t ts =>
      rw [freeze_fields_cons (Pa := PInf), freeze_fields_cons (Pa := PFin)]
      exact ruttc_bind L K V A I2F_dvalue _ _ _ _ _ (hv t)
        fun x y hxy ↦ ih ts (.cons hxy ha)

theorem I2F_freeze_elts_gen {E F B : Effect}
    [@DrawE PInf -< E] [ef : FailureE -< E] [OOME -< E] [UBE -< E]
    [@DrawE PFin -< F] [ff : FailureE -< F] [OOME -< F] [UBE -< F]
    {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F}
    (t : dtyp) {xs : List (@dvalue PInf)} {ys : List (@dvalue PFin)}
    (hs : List.Forall₂ (fun a b ↦ ∀ t, ruttc (B := B) L K V A I2F_dvalue
      (freeze (Pa := PInf) t a) (freeze (Pa := PFin) t b)) xs ys)
    {acc : List (@dvalue PInf)} {acc' : List (@dvalue PFin)}
    (ha : List.Forall₂ I2F_dvalue acc acc') :
    ruttc (B := B) L K V A (List.Forall₂ I2F_dvalue)
      (freeze_elts (Pa := PInf) t xs acc) (freeze_elts (Pa := PFin) t ys acc') := by
  induction hs generalizing acc acc' with
  | nil => exact ruttc_ret _ _ (Forall2_rev_append _ _ _ ha [] [] .nil)
  | cons hv _ ih =>
    rw [freeze_elts_cons (Pa := PInf), freeze_elts_cons (Pa := PFin)]
    exact ruttc_bind L K V A I2F_dvalue _ _ _ _ _ (hv t) fun x y hxy ↦ ih (.cons hxy ha)

theorem I2F_freeze_gen {E F B : Effect}
    [@DrawE PInf -< E] [ef : FailureE -< E] [OOME -< E] [UBE -< E]
    [@DrawE PFin -< F] [ff : FailureE -< F] [OOME -< F] [UBE -< F]
    {L : pred1 E} {K : pred1 F} {V : prerel E F} {A : postrel E F}
    (hd : ∀ t, ruttc (B := B) L K V A I2F_dvalue (draw (Pa := PInf) t) (draw (Pa := PFin) t))
    (hf : ∀ u v : Unit, V (requestIn (D := FailureE) (Throw u))
      (requestIn (D := FailureE) (Throw v)))
    (dt : dtyp) {a : @dvalue PInf} {b : @dvalue PFin} (h : I2F_dvalue a b) :
    ruttc (B := B) L K V A I2F_dvalue (freeze (Pa := PInf) dt a) (freeze (Pa := PFin) dt b) := by
  revert dt
  apply I2F_dvalue_ind (h := h)
  · intro x y hxy dt
    exact I2F_freeze_base_gen hd dt hxy
  · intro p xs ys _ ih dt
    rw [freeze_Struct_eq (Pa := PInf), freeze_Struct_eq (Pa := PFin)]
    cases dt with
    | DTYPE_Struct p' ts =>
      exact ruttc_bind L K V A (List.Forall₂ I2F_dvalue) _ _ _ _ _
        (I2F_freeze_fields_gen hf ih ts .nil) fun _ _ hxy ↦ ruttc_ret _ _ (.I2F_dvalue_Struct p' hxy)
    | _ => exact I2F_raise_gen hf _ _ _
  · intro v xs ys _ ih dt
    rw [freeze_Array_eq (Pa := PInf), freeze_Array_eq (Pa := PFin)]
    cases dt with
    | DTYPE_Array v' _ t =>
      exact ruttc_bind L K V A (List.Forall₂ I2F_dvalue) _ _ _ _ _
        (I2F_freeze_elts_gen t ih .nil) fun _ _ hxy ↦ ruttc_ret _ _ (.I2F_dvalue_Array v' hxy)
    | _ => exact I2F_raise_gen hf _ _ _

theorem I2F_draw_MCFG (dt : dtyp) :
    I2F_refine_MCFG I2F_dvalue (draw (Pa := PInf) dt) (draw (Pa := PFin) dt) := by
  let e := requestIn (D := @DrawE PInf) (E := @MCFGEtop PInf) (Draw dt)
  let f := requestIn (D := @DrawE PFin) (E := @MCFGEtop PFin) (Draw dt)
  change ruttc (B := Tree.NoChoice) cutUB cutOOM I2FE_MCFG I2FA_MCFG I2F_dvalue
    (id <$> CTree.trigger e) (id <$> CTree.trigger f)
  simp only [id_map]
  exact ruttc_trigger e f rfl (fun _ _ h ↦ h)

theorem I2F_freeze_base (dt : dtyp) {a : @dvalue_base PInf} {b : @dvalue_base PFin} (h : I2F_dvalue_base a b) :
    I2F_refine (freeze_base (Pa := PInf) dt a) (freeze_base (Pa := PFin) dt b) :=
  I2F_freeze_base_gen I2F_draw_MCFG dt h

theorem I2F_freeze (dt : dtyp) {a : @dvalue PInf} {b : @dvalue PFin} (h : I2F_dvalue a b) :
    I2F_refine (freeze (Pa := PInf) dt a) (freeze (Pa := PFin) dt b) :=
  I2F_freeze_gen I2F_draw_MCFG I2FE_MCFG_Throw dt h

theorem I2F_denote_int_syntax_as_int (t : dtyp) (x : int_syntax) :
    I2F_EOU I2F_dvalue (@denote_int_syntax_as_int PInf t x) (@denote_int_syntax_as_int PFin t x) := by
  cases t with
  | DTYPE_Base t =>
    cases t with
    | DTYPE_I _ => exact .I2F_EOU_ret _ _ (.I2F_dvalue_Base (.I2F_dvalue_Int _))
    | DTYPE_B _ => exact .I2F_EOU_ret _ _ (.I2F_dvalue_Base (.I2F_dvalue_B (.I2F_BYTE_I _)))
    | DTYPE_Iptr =>
      let z := Attributes.denote_int_syntax x
      change I2F_EOU I2F_dvalue (.raise_ret (@DVALUE_Base PInf (@DVALUE_Iptr PInf z)))
        ((@DVALUE_Base PFin) <$> ((@DVALUE_Iptr PFin) <$> Implementations.IPtrFinite.from_Z_bits z))
      unfold Implementations.IPtrFinite.from_Z_bits
      split
      · exact .I2F_EOU_ret _ _ (.I2F_dvalue_Base (.I2F_dvalue_Ptr (unsigned_repr _ (by assumption)).symm))
      · exact .I2F_EOU_oom _ _
    | _ => exact .I2F_EOU_error _ _
  | _ => exact .I2F_EOU_error _ _

theorem I2F_denote_float_syntax_as_float (t : dtyp) (x : float_syntax) :
    I2F_EOU I2F_dvalue (@denote_float_syntax_as_float PInf t x) (@denote_float_syntax_as_float PFin t x) := by
  cases t with
  | DTYPE_Base t =>
    cases t with
    | DTYPE_FP fp =>
      cases fp <;> simp only [denote_float_syntax_as_float]
      all_goals first | exact .I2F_EOU_error _ _ | split
      all_goals first | exact .I2F_EOU_error _ _
                      | exact .I2F_EOU_ret _ _ (.I2F_dvalue_Base (.I2F_dvalue_Float _))
                      | exact .I2F_EOU_ret _ _ (.I2F_dvalue_Base (.I2F_dvalue_Double _))
    | _ => exact .I2F_EOU_error _ _
  | _ => exact .I2F_EOU_error _ _

theorem I2F_default_dvalue_of_dtyp (t : dtyp) :
    I2F_EOU I2F_dvalue (@default_dvalue_of_dtyp PInf t) (@default_dvalue_of_dtyp PFin t) := by
  induction t using dtyp_ind with
  | base t =>
    cases t with
    | DTYPE_I _ => exact .I2F_EOU_ret _ _ (.I2F_dvalue_Base (.I2F_dvalue_Int _))
    | DTYPE_Iptr => exact .I2F_EOU_ret _ _ (.I2F_dvalue_Base (.I2F_dvalue_Ptr rfl))
    | DTYPE_Pointer =>
      exact .I2F_EOU_ret _ _ (.I2F_dvalue_Base (.I2F_dvalue_Pointer _ _ ⟨rfl, rfl⟩))
    | DTYPE_B _ => exact .I2F_EOU_ret _ _ (.I2F_dvalue_Base (.I2F_dvalue_B (.I2F_BYTE_I _)))
    | DTYPE_FP fp =>
      cases fp <;> first | exact .I2F_EOU_error _ _
                         | exact .I2F_EOU_ret _ _ (.I2F_dvalue_Base (.I2F_dvalue_Float _))
                         | exact .I2F_EOU_ret _ _ (.I2F_dvalue_Base (.I2F_dvalue_Double _))
    | _ => exact .I2F_EOU_error _ _
  | struct p ts ih =>
    simp only [default_dvalue_of_dtyp, default_fields_eq_map]
    exact I2F_EOU_bind _ _ (I2F_EOU_map_monad _ _ ts ih)
      fun _ _ h ↦ .I2F_EOU_ret _ _ (.I2F_dvalue_Struct p h)
  | array v n t ih =>
    simp only [default_dvalue_of_dtyp]
    refine I2F_EOU_bind _ _ ih fun x y hxy ↦ ?_
    apply I2F_EOU_ret _ _
    apply I2F_dvalue_Array
    simpa only [repeat_acc_eq] using Forall2_repeat I2F_dvalue x y (N_to_nat_safe n) hxy

end Vellvm.Theory.I2F.I2F_exp
