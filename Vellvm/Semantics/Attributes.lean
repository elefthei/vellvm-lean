import Vellvm.Semantics.Attributes.Bundles
import Vellvm.Semantics.Simulation

namespace Vellvm.Semantics.Attributes.Worker
open ITree (Effect)
open Tree LLVMEvents Interfaces.Params Instrumentation DynamicValues Syntax.DynamicTypes Syntax.LLVMAst

variable {M : Effect → Effect → Type → Type v} {N : Effect → Effect → Type → Type w}
variable [Runtime M] [Runtime N] [Diagnostics M] [Diagnostics N] [Pa : Params]
variable [Snapshots M] [Snapshots N] (s : Simulation M N)
variable {E B : Effect} [FailureE -< E] [UBE -< E] [OOME -< E] [MemoryE -< E]

theorem assert_dereferenceable_congr (or_null : Bool) (n : Nat) (v : dvalue) (msg : IRString) :
    s.R (E := E) (B := B) (assert_dereferenceable or_null n v msg) (assert_dereferenceable or_null n v msg) := by
  cases v with
  | DVALUE_Base b =>
    cases b with
    | DVALUE_Pointer p =>
      simp only [assert_dereferenceable]
      split
      · exact s.pure ()
      · apply s.bind
        · apply s.emit (E := MemoryE)
        · exact fun _ ↦ s.pure ()
    | DVALUE_Poison => exact s.raiseUB _
    | _ => exact s.«raise» _
  | _ => exact s.«raise» _

theorem assert_attrs_dereferenceable_congr (attrs : List param_attr) (v : dvalue) (msg : IRString) :
    s.R (E := E) (B := B) (assert_attrs_dereferenceable attrs v msg) (assert_attrs_dereferenceable attrs v msg) := by
  unfold assert_attrs_dereferenceable
  split
  · exact assert_dereferenceable_congr s _ _ _ _
  · exact s.pure ()

theorem assert_load_dereferenceable_congr (md : List (metadata dtyp)) (v : dvalue) (msg : IRString) :
    s.R (E := E) (B := B) (assert_load_dereferenceable md v msg) (assert_load_dereferenceable md v msg) := by
  unfold assert_load_dereferenceable
  split
  · exact assert_dereferenceable_congr s _ _ _ _
  · exact s.pure ()

theorem apply_attrs_congr (attrs : List param_attr) (msg : IRString) (dt : dtyp) (v : dvalue) :
    s.R (E := E) (B := B) (apply_attrs attrs msg dt v) (apply_attrs attrs msg dt v) :=
  s.bind (s.liftEOU _) fun _ ↦ s.bind (assert_attrs_dereferenceable_congr s _ _ _) fun _ ↦ s.pure _

theorem apply_args_attrs_congr (attrss : List (List param_attr)) (msg : IRString) (args : List (dtyp × dvalue)) :
    s.R (E := E) (B := B) (apply_args_attrs attrss msg args) (apply_args_attrs attrss msg args) := by
  induction args generalizing attrss with
  | nil => exact s.pure []
  | cons tv vs ih =>
    obtain ⟨t, v⟩ := tv
    exact s.bind (apply_attrs_congr s _ _ _ _) fun _ ↦ s.bind (ih _) fun _ ↦ s.pure _

theorem check_call_return_congr (fattrs : List fn_attr) (ret_attrs : List param_attr)
    (ranges : Option (List (int_syntax × int_syntax))) (loc : IRString) (ret_t : dtyp)
    (args : List dvalue) (res : exc ⊕ dvalue) :
    s.R (E := E) (B := B) (check_call_return fattrs ret_attrs ranges loc ret_t args res)
      (check_call_return fattrs ret_attrs ranges loc ret_t args res) := by
  apply s.bind (s.liftEOU _)
  intro _
  cases res with
  | inl _ => exact s.pure _
  | inr v => exact s.bind (apply_attrs_congr s _ _ _ _) fun _ ↦ s.pure _

theorem assume_violated_congr {A : Type} (loc tag : IRString) :
    s.R (E := E) (B := B) (X := A) (assume_violated loc tag) (assume_violated loc tag) := s.raiseUB _

theorem assume_malformed_congr {A : Type} (loc tag : IRString) :
    s.R (E := E) (B := B) (X := A) (assume_malformed loc tag) (assume_malformed loc tag) := s.«raise» _

theorem assume_nonnull_congr (loc : IRString) (vs : List dvalue) :
    s.R (E := E) (B := B) (assume_nonnull loc vs) (assume_nonnull loc vs) := by
  unfold assume_nonnull
  repeat' first | exact assume_violated_congr s _ _ | exact assume_malformed_congr s _ _ | exact s.pure () | split

theorem assume_noundef_congr (loc : IRString) (vs : List dvalue) :
    s.R (E := E) (B := B) (assume_noundef loc vs) (assume_noundef loc vs) := by
  unfold assume_noundef
  repeat' first | exact assume_violated_congr s _ _ | exact assume_malformed_congr s _ _ | exact s.pure () | split

theorem assume_align_congr (loc : IRString) (vs : List dvalue) :
    s.R (E := E) (B := B) (assume_align loc vs) (assume_align loc vs) := by
  unfold assume_align
  repeat' first | exact assume_violated_congr s _ _ | exact assume_malformed_congr s _ _
                | exact s.pure () | (split <;> try dsimp only)

theorem assume_dereferenceable_congr (or_null : Bool) (loc : IRString) (vs : List dvalue) :
    s.R (E := E) (B := B) (assume_dereferenceable or_null loc vs) (assume_dereferenceable or_null loc vs) := by
  unfold assume_dereferenceable
  repeat' first | exact assert_dereferenceable_congr s _ _ _ _ | exact assume_violated_congr s _ _
                | exact assume_malformed_congr s _ _ | exact s.pure () | split

theorem assume_bundle_checks_congr :
    List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ ∀ loc vs, s.R (a.2 loc vs) (b.2 loc vs))
      (assume_bundle_checks (M := M) (E := E) (B := B)) (assume_bundle_checks (M := N) (E := E) (B := B)) :=
  .cons ⟨rfl, assume_nonnull_congr s⟩ <| .cons ⟨rfl, assume_noundef_congr s⟩ <|
  .cons ⟨rfl, assume_align_congr s⟩ <| .cons ⟨rfl, assume_dereferenceable_congr s false⟩ <|
  .cons ⟨rfl, assume_dereferenceable_congr s true⟩ .nil

private theorem lookupChecks {L R : Type*} (P : L → R → Prop) (tag : IRString)
    {xs : List (IRString × L)} {ys : List (IRString × R)}
    (h : List.Forall₂ (fun a b ↦ a.1 = b.1 ∧ P a.2 b.2) xs ys) :
    Option.Rel P ((xs.find? (fun p ↦ p.1 == tag)).map Prod.snd)
      ((ys.find? (fun p ↦ p.1 == tag)).map Prod.snd) := by
  induction h with
  | nil => exact .none
  | cons h _ ih =>
    simp only [List.find?_cons, h.1]
    split
    · exact .some h.2
    · exact ih

theorem bundle_check_congr (f : exp dtyp) (tag : IRString) :
    Option.Rel (fun l r ↦ ∀ loc vs, s.R (l loc vs) (r loc vs))
      (bundle_check (M := M) (E := E) (B := B) f tag) (bundle_check (M := N) (E := E) (B := B) f tag) := by
  unfold bundle_check
  split
  · exact lookupChecks _ tag (assume_bundle_checks_congr s)
  · exact .none

end Vellvm.Semantics.Attributes.Worker
