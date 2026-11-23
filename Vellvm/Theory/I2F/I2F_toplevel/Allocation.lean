import Vellvm.Semantics.TopLevel.Initialization
import Vellvm.Theory.I2F.Refinement.TreeLaws
import Vellvm.Theory.I2F.I2F_exp.Values

namespace Vellvm.Theory.I2F.I2F_toplevel
open Refinement Semantics Semantics.DynamicValues Semantics.LLVMEvents Semantics.TopLevel
open Syntax.LLVMAst Syntax.DynamicTypes Utils.ListUtil Vellvm.Tree
open Utils.rutt_cutoff (ruttc_bind ruttc_ret ruttc_trigger' ruttc_map_monad)
open ITree (Effect Subeffect)
open CTree (CTree)

private abbrev UnitRel (_ _ : Unit) : Prop := True

theorem mcfg_bind {A B C D : Type} {P : A → B → Prop} {Q : C → D → Prop}
    {x : @MCFGtop PInf A} {y : @MCFGtop PFin B} {f : A → @MCFGtop PInf C} {g : B → @MCFGtop PFin D}
    (h : I2F_refine_MCFG P x y) (k : ∀ a b, P a b → I2F_refine_MCFG Q (f a) (g b)) :
    I2F_refine_MCFG Q (x >>= f) (y >>= g) :=
  ruttc_bind cutUB cutOOM I2FE_MCFG I2FA_MCFG P Q x y f g h k

theorem mcfg_emit {E F : Effect} [i : E -< @MCFGEtop PInf] [j : F -< @MCFGEtop PFin]
    (e : E.I) (f : F.I) (R : E.O e → F.O f → Prop)
    (h : I2FE_MCFG (requestIn e) (requestIn f))
    (k : ∀ a b, I2FA_MCFG (requestIn e) a (requestIn f) b → R ((i.map e).2 a) ((j.map f).2 b)) :
    I2F_refine_MCFG R (Runtime.emit (E := E) e) (Runtime.emit (E := F) f) :=
  ruttc_trigger' (requestIn e) (requestIn f) _ _ h fun a b hab ↦ ruttc_ret _ _ (k a b hab)

private theorem allocaRelated (t : dtyp) (n : Nat) (align : Option Nat) :
    I2F_refine_MCFG I2F_dvalue (alloca (Pa := PInf) t n align) (alloca (Pa := PFin) t n align) :=
  mcfg_emit (E := @MemoryE PInf) (F := @MemoryE PFin) (@Alloca PInf t n align) (@Alloca PFin t n align) _
    ⟨rfl, rfl, rfl⟩ (fun _ _ h ↦ h)

private theorem gwriteRelated (id : raw_id) {a b} (h : I2F_dvalue a b) :
    I2F_refine_MCFG UnitRel (gwrite (Pa := PInf) id a) (gwrite (Pa := PFin) id b) :=
  mcfg_emit (E := @GlobalE PInf) (F := @GlobalE PFin) (@GlobalWrite PInf id a) (@GlobalWrite PFin id b) _
    ⟨rfl, h⟩ (fun _ _ _ ↦ trivial)

theorem mcfg_gread (id : raw_id) :
    I2F_refine_MCFG I2F_dvalue (gread (Pa := PInf) id) (gread (Pa := PFin) id) :=
  mcfg_emit (E := @GlobalE PInf) (F := @GlobalE PFin) (@GlobalRead PInf id) (@GlobalRead PFin id) _
    rfl (fun _ _ h ↦ h)

private theorem storeRelated (t : dtyp) {a b x y} (ha : I2F_dvalue a b) (hx : I2F_dvalue x y) :
    I2F_refine_MCFG UnitRel (store (Pa := PInf) t a x) (store (Pa := PFin) t b y) :=
  mcfg_emit (E := @MemoryE PInf) (F := @MemoryE PFin) (@Store PInf t a x) (@Store PFin t b y) _
    ⟨rfl, ha, hx⟩ (fun _ _ _ ↦ trivial)

private theorem loopRelated {A : Type} {f : A → @MCFGtop PInf Unit} {g : A → @MCFGtop PFin Unit}
    (h : ∀ x, I2F_refine_MCFG UnitRel (f x) (g x)) (xs : List A) :
    I2F_refine_MCFG UnitRel (loop_monad f xs) (loop_monad g xs) := by
  induction xs with
  | nil => exact ruttc_ret _ _ trivial
  | cons x xs ih => exact mcfg_bind (h x) fun _ _ _ ↦ ih

theorem I2F_allocate_global (g : «global» dtyp) : I2F_refine_MCFG (fun _ _ : Unit ↦ True)
    (@allocate_global PInf g) (@allocate_global PFin g) := by
  unfold allocate_global TopLevel.Worker.allocate_global
  split
  · exact ruttc_ret _ _ trivial
  · exact mcfg_bind (allocaRelated _ _ _) fun _ _ h ↦ gwriteRelated _ h

theorem I2F_allocate_globals (gs : List («global» dtyp)) : I2F_refine_MCFG (fun _ _ : Unit ↦ True)
    (@allocate_globals PInf gs) (@allocate_globals PFin gs) := loopRelated I2F_allocate_global gs

theorem I2F_allocate_declaration (d : declaration dtyp) : I2F_refine_MCFG (fun _ _ : Unit ↦ True)
    (@allocate_declaration PInf d) (@allocate_declaration PFin d) := by
  unfold allocate_declaration TopLevel.Worker.allocate_declaration
  split
  · exact ruttc_ret _ _ trivial
  · exact mcfg_bind (allocaRelated _ _ _) fun _ _ h ↦ gwriteRelated _ h

theorem I2F_allocate_declarations (ds : List (declaration dtyp)) : I2F_refine_MCFG (fun _ _ : Unit ↦ True)
    (@allocate_declarations PInf ds) (@allocate_declarations PFin ds) :=
  loopRelated I2F_allocate_declaration ds

theorem I2F_allocate_block_address (fb : function_id × block_id) : I2F_refine_MCFG (fun _ _ : Unit ↦ True)
    (@allocate_block_address PInf fb) (@allocate_block_address PFin fb) :=
  mcfg_bind (allocaRelated _ _ _) fun _ _ h ↦ gwriteRelated _ h

theorem I2F_allocate_block_addresses (fbs : List (function_id × block_id)) :
    I2F_refine_MCFG (fun _ _ : Unit ↦ True) (@allocate_block_addresses PInf fbs) (@allocate_block_addresses PFin fbs) :=
  loopRelated I2F_allocate_block_address fbs

private theorem foldRevRelated {A B : Type} {R : A → B → Prop} (n : Nat)
    (f : (i : Nat) → i < n → A → A) (g : (i : Nat) → i < n → B → B)
    (step : ∀ i hi x y, R x y → R (f i hi x) (g i hi y)) (a b) (h : R a b) :
    R (n.foldRev f a) (n.foldRev g b) := by
  induction n generalizing a b with
  | zero => exact h
  | succ n ih =>
    simp only [Nat.foldRev_succ]
    apply ih
    · intro i hi x y hxy; exact step i _ x y hxy
    · exact step n _ a b h

theorem I2F_i8_array_of_string (s : IRString) :
    I2F_dvalue (@i8_array_of_string PInf s) (@i8_array_of_string PFin s) := by
  apply I2F_dvalue_Array
  apply foldRevRelated
  · intro i hi xs ys h; exact .cons (.I2F_dvalue_Base (.I2F_dvalue_Int _)) h
  · exact .cons (.I2F_dvalue_Base (.I2F_dvalue_Int _)) .nil

theorem I2F_allocate_arg (arg : IRString) : I2F_refine_MCFG I2F_dvalue
    (@allocate_arg PInf arg) (@allocate_arg PFin arg) :=
  mcfg_bind (allocaRelated _ _ _) fun _ _ h ↦
    mcfg_bind (storeRelated _ h (I2F_i8_array_of_string arg)) fun _ _ _ ↦ ruttc_ret _ _ h

theorem I2F_allocate_args (args : List IRString) : I2F_refine_MCFG I2F_dvalue
    (@allocate_args PInf args) (@allocate_args PFin args) :=
  mcfg_bind (allocaRelated _ _ _) fun _ _ h ↦
    mcfg_bind (ruttc_map_monad cutUB cutOOM I2FE_MCFG I2FA_MCFG I2F_dvalue
      (@allocate_arg PInf) (@allocate_arg PFin) args (fun arg _ ↦ I2F_allocate_arg arg)) fun _ _ hs ↦
      mcfg_bind (storeRelated _ h (.I2F_dvalue_Array false hs)) fun _ _ _ ↦ ruttc_ret _ _ h

theorem I2F_build_main_args (args : List IRString) : I2F_refine_MCFG I2F_targs
    (@build_main_args PInf args) (@build_main_args PFin args) :=
  mcfg_bind (I2F_allocate_args args) fun _ _ h ↦ ruttc_ret _ _
    (List.Forall₂.cons ⟨rfl, I2F_dvalue_Base (I2F_dvalue_Int _)⟩ (.cons ⟨rfl, h⟩ .nil))

/-- Isolate the sole expression-denotation premise used for non-alias initializers. -/
theorem initializeGlobalOfExp (g : «global» dtyp)
    (he : ∀ e, I2F_refine (@Denotation.denote_exp PInf (some g.g_typ) e)
      (@Denotation.denote_exp PFin (some g.g_typ) e)) :
    I2F_refine_MCFG UnitRel (@initialize_global PInf g) (@initialize_global PFin g) := by
  unfold initialize_global TopLevel.Worker.initialize_global
  split
  · split
    · exact mcfg_bind (mcfg_gread _) fun _ _ h ↦ gwriteRelated _ h
    · exact I2F_refine_lift UnitRel (.raise_ub _) (.raise_ub _) (.I2F_EOU_ub _ _)
    · exact I2F_refine_lift UnitRel (.raise_ub _) (.raise_ub _) (.I2F_EOU_ub _ _)
  · refine mcfg_bind (mcfg_gread _) fun _ _ ha ↦ ?_
    cases g.g_exp with
    | none =>
      exact mcfg_bind (ruttc_ret _ _ (I2F_exp.I2F_poison_of_dtyp g.g_typ))
        fun _ _ hv ↦ storeRelated _ ha hv
    | some e => exact mcfg_bind (he e) fun _ _ hv ↦ storeRelated _ ha hv

theorem initializeGlobalsOfGlobal
    (h : ∀ g, I2F_refine_MCFG UnitRel (@initialize_global PInf g) (@initialize_global PFin g))
    (gs : List («global» dtyp)) :
    I2F_refine_MCFG UnitRel (@initialize_globals PInf gs) (@initialize_globals PFin gs) :=
  loopRelated h gs

theorem buildGlobalEnvironmentOfGlobals
    (h : ∀ gs, I2F_refine_MCFG UnitRel (@initialize_globals PInf gs) (@initialize_globals PFin gs))
    (m : Syntax.CFG.mcfg dtyp) :
    I2F_refine_MCFG UnitRel (@build_global_environment PInf m) (@build_global_environment PFin m) :=
  mcfg_bind (I2F_allocate_declarations _) fun _ _ _ ↦
    mcfg_bind (I2F_allocate_block_addresses _) fun _ _ _ ↦
      mcfg_bind (I2F_allocate_globals _) fun _ _ _ ↦ h _

end Vellvm.Theory.I2F.I2F_toplevel
