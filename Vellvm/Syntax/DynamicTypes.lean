module

public import Vellvm.Syntax.LLVMAst
public import Vellvm.Utils.ListUtil

@[expose] public section
namespace Vellvm.Syntax.DynamicTypes
open Vellvm.Syntax.LLVMAst Vellvm.Utils.ListUtil

/-- Scalar types after resolving named types and erasing pointee annotations. -/
inductive dtyp_base : Type where
  | DTYPE_I (sz : Positive)
  | DTYPE_Iptr
  | DTYPE_Pointer
  | DTYPE_Void
  | DTYPE_FP (fp : floating_point_variant)
  | DTYPE_Label
  | DTYPE_Token
  | DTYPE_Metadata
  | DTYPE_X86_mmx
  | DTYPE_Opaque
  | DTYPE_B (sz : Positive)
  deriving DecidableEq
export dtyp_base (DTYPE_I DTYPE_Iptr DTYPE_Pointer DTYPE_Void DTYPE_FP DTYPE_Label DTYPE_Token
  DTYPE_Metadata DTYPE_X86_mmx DTYPE_Opaque DTYPE_B)

inductive dtyp : Type where
  | DTYPE_Base (dt : dtyp_base)
  | DTYPE_Struct (packed : Bool) (fields : List dtyp)
  | DTYPE_Array (vector : Bool) (sz : Nat) (t : dtyp)
export dtyp (DTYPE_Base DTYPE_Struct DTYPE_Array)

instance : Coe dtyp_base dtyp := ⟨DTYPE_Base⟩

def dtyp_base_eq_dec : DecidableEq dtyp_base := inferInstance
mutual
  def dtyp_eq_dec (x y : dtyp) : Decidable (x = y) := by
    cases x with
    | DTYPE_Base a =>
      cases y with
      | DTYPE_Base b => exact decidable_of_iff (a = b) (by simp)
      | _ => exact .isFalse (by intro h; cases h)
    | DTYPE_Struct p ts =>
      cases y with
      | DTYPE_Struct q us =>
        letI := dtyp_list_eq_dec ts us
        exact decidable_of_iff (p = q ∧ ts = us) (by simp)
      | _ => exact .isFalse (by intro h; cases h)
    | DTYPE_Array v n t =>
      cases y with
      | DTYPE_Array w m u =>
        letI := dtyp_eq_dec t u
        exact decidable_of_iff (v = w ∧ n = m ∧ t = u) (by simp)
      | _ => exact .isFalse (by intro h; cases h)

  def dtyp_list_eq_dec (xs ys : List dtyp) : Decidable (xs = ys) := by
    cases xs with
    | nil => cases ys <;> first | exact .isTrue rfl | exact .isFalse (by intro h; cases h)
    | cons a as =>
      cases ys with
      | nil => exact .isFalse (by intro h; cases h)
      | cons b bs =>
        letI := dtyp_eq_dec a b
        letI := dtyp_list_eq_dec as bs
        exact decidable_of_iff (a = b ∧ as = bs) (by simp)
end
attribute [instance_reducible, instance] dtyp_eq_dec

def visit (P : dtyp → Sort u) (base : ∀ t, P (DTYPE_Base t))
    (struct : ∀ p ts, (∀ t ∈ ts, P t) → P (DTYPE_Struct p ts))
    (array : ∀ v n t, P t → P (DTYPE_Array v n t)) (dt : dtyp) : P dt :=
  match dt with
  | .DTYPE_Base t => base t
  | .DTYPE_Struct p ts => struct p ts fun t _ ↦ visit P base struct array t
  | .DTYPE_Array v n t => array v n t (visit P base struct array t)
termination_by sizeOf dt
decreasing_by all_goals decreasing_tactic

theorem dtyp_ind (P : dtyp → Prop) (base : ∀ t, P (DTYPE_Base t))
    (struct : ∀ p ts, (∀ t ∈ ts, P t) → P (DTYPE_Struct p ts))
    (array : ∀ v n t, P t → P (DTYPE_Array v n t)) (dt : dtyp) : P dt :=
  visit P base struct array dt

def dtyp_rec (P : dtyp → Type) (base : ∀ t, P (DTYPE_Base t))
    (struct : ∀ p ts, (∀ t ∈ ts, P t) → P (DTYPE_Struct p ts))
    (array : ∀ v n t, P t → P (DTYPE_Array v n t)) (dt : dtyp) : P dt :=
  visit P base struct array dt

def dtyp_base_eqb (x y : dtyp_base) : Bool := decide (x = y)
def dtyp_eqb (x y : dtyp) : Bool := decide (x = y)

theorem dtyp_eqb_refl (dt : dtyp) : dtyp_eqb dt dt = true := by simp [dtyp_eqb]
theorem dtyp_eqb_eq (x y : dtyp) : dtyp_eqb x y = true → x = y := of_decide_eq_true

def vector_dtyp_base : dtyp_base → Prop
  | .DTYPE_I _ | .DTYPE_Iptr | .DTYPE_Pointer | .DTYPE_FP _ | .DTYPE_B _ => True
  | _ => False

def vector_dtyp_base_dec (t : dtyp_base) : Decidable (vector_dtyp_base t) := by
  cases t <;> unfold vector_dtyp_base <;> infer_instance

def dtyp_measure : dtyp → Nat
  | .DTYPE_Base _ => 1
  | .DTYPE_Struct _ ts => (ts.map dtyp_measure).sum + 2
  | .DTYPE_Array _ _ t => dtyp_measure t + 2

theorem dtyp_measure_gt_0 (dt : dtyp) : 0 < dtyp_measure dt := by
  cases dt <;> simp [dtyp_measure]

def Decidable_eq_N : DecidableEq Nat := inferInstance

def NO_VOID_base : dtyp_base → Prop
  | .DTYPE_Void => False
  | _ => True

def NO_VOID : dtyp → Prop
  | .DTYPE_Base t => NO_VOID_base t
  | .DTYPE_Struct _ ts => ts.foldr (fun x rest ↦ NO_VOID x ∧ rest) True
  | .DTYPE_Array _ _ t => NO_VOID t

theorem NO_VOID_Struct_fields (p : Bool) (dts : List dtyp) :
    NO_VOID (DTYPE_Struct p dts) → ∀ dt ∈ dts, NO_VOID dt := by
  rw [NO_VOID]
  induction dts with
  | nil => simp
  | cons a ts ih =>
    intro h dt hm
    rcases List.mem_cons.mp hm with rfl | hm
    · exact h.1
    · exact ih h.2 _ hm

def NO_VOID_base_dec (t : dtyp_base) : Decidable (NO_VOID_base t) := by
  cases t <;> unfold NO_VOID_base <;> infer_instance

def NO_VOID_dec : ∀ dt, Decidable (NO_VOID dt) := by
  apply dtyp_rec
  · intro t; rw [NO_VOID]; exact NO_VOID_base_dec t
  · intro p ts ih
    rw [NO_VOID]
    cases FORALL_dec NO_VOID ts (fun x hx ↦ match ih x hx with
      | .isTrue h => .inl h | .isFalse h => .inr h) with
    | inl h => exact .isTrue h
    | inr h => exact .isFalse h
  · intro v n t ih; rw [NO_VOID]; exact ih

end Vellvm.Syntax.DynamicTypes
