/- Port of Vellvm, Syntax/AstLib.v. -/
module

public import Vellvm.Syntax.LLVMAst
public import Vellvm.Utils.StringUtil
public import Mathlib.Order.Std
public import Std.Data.ByteSlice

@[expose] public section
namespace Vellvm.Syntax.AstLib
open LLVMAst

instance eq_dec_int : BEq int_ast := inferInstance
instance eqv_int : HasEquiv.{1,0} int_ast := ⟨(· = ·)⟩

namespace RawIDOrd
abbrev t := raw_id
abbrev eq (x y : t) := x = y
theorem eq_refl (x : t) : x = x := rfl
theorem eq_sym {x y : t} : x = y → y = x := Eq.symm
theorem eq_trans {x y z : t} : x = y → y = z → x = z := Eq.trans

def lt : t → t → Prop
  | .Anon a, .Anon b | .Raw a, .Raw b => a < b
  | .Name a, .Name b => a < b
  | .Anon _, _ | .Name _, .Raw _ => True
  | _, _ => False

theorem lt_trans {a b c : t} : lt a b → lt b c → lt a c := by
  cases a <;> cases b <;> cases c <;> simp [lt] <;> exact Std.lt_trans

theorem lt_not_eq {a b : t} (h : lt a b) : ¬eq a b := by
  rintro rfl
  cases a <;> exact Std.lt_irrefl h

def cmp : t → t → Ordering
  | .Anon a, .Anon b | .Raw a, .Raw b => Ord.compare a b
  | .Name a, .Name b => Ord.compare a b
  | .Anon _, _ | .Name _, .Raw _ => .lt
  | _, _ => .gt

theorem cmp_lt (a b : t) : cmp a b = .lt ↔ lt a b := by
  cases a <;> cases b <;> simp [cmp, lt, Std.compare_eq_lt]

theorem cmp_eq (a b : t) : cmp a b = .eq ↔ a = b := by
  cases a <;> cases b <;> simp [cmp, Std.compare_eq_iff_eq]

theorem cmp_antisym (a b : t) : cmp a b = (cmp b a).swap := by
  cases a <;> cases b <;> simp only [cmp] <;> first | rfl | exact Std.OrientedCmp.eq_swap

theorem compare_helper_lt {a b : t} : cmp a b = .lt → lt a b := (cmp_lt ..).mp
theorem compare_helper_gt {a b : t} (h : cmp a b = .gt) : lt b a := by
  exact (cmp_lt ..).mp (by rw [cmp_antisym b a, h]; rfl)
theorem compare_helper_eq {a b : t} : cmp a b = .eq → a = b := (cmp_eq ..).mp

inductive Compare (a b : t) where
  | LT : lt a b → Compare a b
  | EQ : eq a b → Compare a b
  | GT : lt b a → Compare a b

def compare (a b : t) : Compare a b :=
  match h : cmp a b with
  | .lt => .LT (compare_helper_lt h)
  | .eq => .EQ (compare_helper_eq h)
  | .gt => .GT (compare_helper_gt h)

deriving instance DecidableEq for raw_id
def eq_dec : DecidableEq t := inferInstance

instance rawOrd : Ord raw_id := ⟨cmp⟩
instance : Std.TransOrd raw_id where
  eq_swap := cmp_antisym _ _
  isLE_trans := by
    intro a b c
    change (cmp a b).isLE → (cmp b c).isLE → (cmp a c).isLE
    cases a <;> cases b <;> cases c <;> simp [cmp, Std.isLE_compare] <;> exact Std.le_trans
instance : Std.LawfulEqOrd raw_id where
  compare_self := (cmp_eq _ _).mpr rfl
  eq_of_compare := (cmp_eq _ _).mp
instance : LinearOrder raw_id := .ofStd raw_id
end RawIDOrd

instance eq_dec_raw_id : BEq raw_id := ⟨fun a b ↦ decide (a = b)⟩
instance eqv_raw_id : HasEquiv.{1,0} raw_id := ⟨(· = ·)⟩

namespace InstrIDDec
abbrev t := instr_id
deriving instance DecidableEq for instr_id
def eq_dec : DecidableEq instr_id := inferInstance
end InstrIDDec
namespace InstrID
export InstrIDDec (t eq_dec)
end InstrID
instance eq_dec_instr_id : BEq instr_id := ⟨fun a b ↦ decide (a = b)⟩
instance eqv_instr_id : HasEquiv.{1,0} instr_id := ⟨(· = ·)⟩

namespace IdentDec
abbrev t := «ident»
deriving instance DecidableEq for «ident»
def eq_dec : DecidableEq «ident» := inferInstance
end IdentDec
namespace Ident
export IdentDec (t eq_dec)
end Ident
instance eq_dec_ident : BEq «ident» := ⟨fun a b ↦ decide (a = b)⟩
instance eqv_ident : HasEquiv.{1,0} «ident» := ⟨(· = ·)⟩

theorem typ_ind (P : typ → Prop)
    (hI : ∀ sz, P (TYPE_I sz)) (hB : ∀ sz, P (TYPE_B sz)) (hIP : P TYPE_Iptr)
    (hPtr : ∀ t, P t → P (TYPE_Pointer (some t))) (hOptr : P (TYPE_Pointer none))
    (hVoid : P TYPE_Void) (hFP : ∀ f, P (TYPE_FP f)) (hL : P TYPE_Label) (hT : P TYPE_Token)
    (hM : P TYPE_Metadata) (hX : P TYPE_X86_mmx) (hA : ∀ n t, P t → P (TYPE_Array n t))
    (hF : ∀ r ts va, P r → (∀ u ∈ ts, P u) → P (TYPE_Function r ts va))
    (hS : ∀ ts, (∀ u ∈ ts, P u) → P (TYPE_Struct ts)) (hPS : ∀ ts, (∀ u ∈ ts, P u) → P (TYPE_Packed_struct ts))
    (hO : P TYPE_Opaque) (hV : ∀ n t, P t → P (TYPE_Vector n t))
    (hId : ∀ i, P (TYPE_Identified i)) : ∀ t, P t := by
  refine typ.rec (motive_1 := P)
    (motive_2 := fun o ↦ match o with | some t => P t | none => True)
    (motive_3 := fun ts ↦ ∀ t ∈ ts, P t)
    hI hB hIP ?_ hVoid hFP hL hT hM hX hA hF hS hPS hO hV hId
    trivial (fun _ ih ↦ ih) (by simp) (fun _ _ hh ht ↦ List.forall_mem_cons.mpr ⟨hh, ht⟩)
  exact fun | none, _ => hOptr | some t, ih => hPtr t ih

def typ_rect' (P : typ → Type u)
    (hI : ∀ sz, P (TYPE_I sz)) (hB : ∀ sz, P (TYPE_B sz)) (hIP : P TYPE_Iptr)
    (hPtr : ∀ t, P t → P (TYPE_Pointer (some t))) (hOptr : P (TYPE_Pointer none))
    (hVoid : P TYPE_Void) (hFP : ∀ f, P (TYPE_FP f)) (hL : P TYPE_Label) (hT : P TYPE_Token)
    (hM : P TYPE_Metadata) (hX : P TYPE_X86_mmx) (hA : ∀ n t, P t → P (TYPE_Array n t))
    (hF : ∀ r ts va, P r → (∀ u, (P u → typ → P u) → List typ → P u → P u) → P (TYPE_Function r ts va))
    (hS : ∀ ts, (∀ u, (P u → typ → P u) → List typ → P u → P u) → P (TYPE_Struct ts)) (hPS : ∀ ts, (∀ u, (P u → typ → P u) → List typ → P u → P u) → P (TYPE_Packed_struct ts))
    (hO : P TYPE_Opaque) (hV : ∀ n t, P t → P (TYPE_Vector n t))
    (hId : ∀ i, P (TYPE_Identified i)) : ∀ t, P t := by
  let first (l : List typ) (u : typ) (f : P u → typ → P u) (_ : List typ) (d : P u) : P u :=
    match l with | [] => d | x :: _ => f d x
  let rec go : (t : typ) → P t
    | .TYPE_I n => hI n
    | .TYPE_B n => hB n
    | .TYPE_Iptr => hIP
    | .TYPE_Pointer none => hOptr
    | .TYPE_Pointer (some t) => hPtr t (go t)
    | .TYPE_Void => hVoid
    | .TYPE_FP f => hFP f
    | .TYPE_Label => hL
    | .TYPE_Token => hT
    | .TYPE_Metadata => hM
    | .TYPE_X86_mmx => hX
    | .TYPE_Array n t => hA n t (go t)
    | .TYPE_Function r ts va => hF r ts va (go r) (first ts)
    | .TYPE_Struct ts => hS ts (first ts)
    | .TYPE_Packed_struct ts => hPS ts (first ts)
    | .TYPE_Opaque => hO
    | .TYPE_Vector n t => hV n t (go t)
    | .TYPE_Identified i => hId i
  exact go

section
variable {T : Type} (P : exp T → Prop) (Q : metadata T → Prop)
variable (hid : ∀ i, P (EXP_Ident i)) (hi : ∀ x, P (EXP_Integer x))
  (hf : ∀ f, P (EXP_Float f)) (hb : ∀ b, P (EXP_Bool b)) (hn : P EXP_Null)
  (hz : P EXP_Zero_initializer)
  (hcs : ∀ l : List (texp T), (∀ p ∈ l, P p.2) → P (EXP_Cstring l))
  (hu : P EXP_Undef) (hp : P EXP_Poison)
  (hs : ∀ l : List (texp T), (∀ p ∈ l, P p.2) → P (EXP_Struct l))
  (hps : ∀ l : List (texp T), (∀ p ∈ l, P p.2) → P (EXP_Packed_struct l))
  (ha : ∀ l : List (texp T), (∀ p ∈ l, P p.2) → P (EXP_Array l))
  (hv : ∀ l : List (texp T), (∀ p ∈ l, P p.2) → P (EXP_Vector l))
  (hib : ∀ op t x y, P x → P y → P (OP_IBinop op t x y))
  (hneg : ∀ fm (x : texp T), P x.2 → P (OP_Fneg fm x))
  (hic : ∀ s cmp t x y, P x → P y → P (OP_ICmp s cmp t x y))
  (hfb : ∀ op fm t x y, P x → P y → P (OP_FBinop op fm t x y))
  (hfc : ∀ op fm t x y, P x → P y → P (OP_FCmp op fm t x y))
  (hc : ∀ c s x t, P x → P (OP_Conversion c s x t))
  (hgep : ∀ f t (p : texp T) (l : List (texp T)), P p.2 → (∀ a ∈ l, P a.2) →
    P (OP_GetElementPtr f t p l))
  (hxe : ∀ x i : texp T, P x.2 → P i.2 → P (OP_ExtractElement x i))
  (hie : ∀ x e i : texp T, P x.2 → P e.2 → P i.2 → P (OP_InsertElement x e i))
  (hsh : ∀ x y m : texp T, P x.2 → P y.2 → P m.2 → P (OP_ShuffleVector x y m))
  (hxv : ∀ (x : texp T) i, P x.2 → P (OP_ExtractValue x i))
  (hiv : ∀ (x y : texp T) i, P x.2 → P y.2 → P (OP_InsertValue x y i))
  (hsel : ∀ f (c x y : texp T), P c.2 → P x.2 → P y.2 → P (OP_Select f c x y))
  (hfr : ∀ x : texp T, P x.2 → P (OP_Freeze x))
  (hasm : ∀ s a i u t c, P (EXP_Asm s a i u t c))
section
variable (hmd : ∀ m, Q m → P (EXP_Metadata m)) (hspl : ∀ x : texp T, P x.2 → P (EXP_Splat x))
  (hba : ∀ f b, P (EXP_BlockAddress f b)) (hmn : Q METADATA_Null) (hmi : ∀ i, Q (METADATA_Id i))
  (hmc : ∀ v : texp T, P v.2 → Q (METADATA_Const v))
  (hml : ∀ l, (∀ m ∈ l, Q m) → Q (METADATA_Node l))
  (hmp : ∀ x y, Q x → Q y → Q (METADATA_Pair x y)) (hmdg : ∀ s t, Q (METADATA_Debug s t))
  (hmfi : ∀ f, Q (METADATA_File_info f))
include hid hi hf hb hn hz hcs hu hp hs hps ha hv hib hneg hic hfb hfc hc hgep hxe hie hsh hxv hiv hsel hfr hasm hmd hspl hba hmn hmi hmc hml hmp hmdg hmfi

theorem exp_ind_full : ∀ x, P x :=
  exp.rec (motive_1 := P) (motive_2 := Q) (motive_3 := fun l ↦ ∀ p ∈ l, P p.2)
    (motive_4 := fun p ↦ P p.2) (motive_5 := fun l ↦ ∀ m ∈ l, Q m)
    hid hi hf hb hn hz hcs hu hp hs hps ha hv hib hic hfb hneg hfc hc hgep hxe hie hsh hxv hiv hsel hfr hasm hmd hspl hba hmn hmi hmc hml hmp hmdg hmfi
    (by simp) (fun _ _ hh ht ↦ List.forall_mem_cons.mpr ⟨hh, ht⟩) (fun _ _ ih ↦ ih)
    (by simp) (fun _ _ hh ht ↦ List.forall_mem_cons.mpr ⟨hh, ht⟩)

theorem metadata_ind : ∀ m, Q m :=
  metadata.rec (motive_1 := P) (motive_2 := Q) (motive_3 := fun l ↦ ∀ p ∈ l, P p.2)
    (motive_4 := fun p ↦ P p.2) (motive_5 := fun l ↦ ∀ m ∈ l, Q m)
    hid hi hf hb hn hz hcs hu hp hs hps ha hv hib hic hfb hneg hfc hc hgep hxe hie hsh hxv hiv hsel hfr hasm hmd hspl hba hmn hmi hmc hml hmp hmdg hmfi
    (by simp) (fun _ _ hh ht ↦ List.forall_mem_cons.mpr ⟨hh, ht⟩) (fun _ _ ih ↦ ih)
    (by simp) (fun _ _ hh ht ↦ List.forall_mem_cons.mpr ⟨hh, ht⟩)

theorem exp_metadata_mut_ind : (∀ e, P e) ∧ (∀ m, Q m) :=
  ⟨exp_ind_full P Q hid hi hf hb hn hz hcs hu hp hs hps ha hv hib hneg hic hfb hfc hc hgep hxe hie hsh hxv hiv hsel hfr hasm hmd hspl hba hmn hmi hmc hml hmp hmdg hmfi,
   metadata_ind P Q hid hi hf hb hn hz hcs hu hp hs hps ha hv hib hneg hic hfb hfc hc hgep hxe hie hsh hxv hiv hsel hfr hasm hmd hspl hba hmn hmi hmc hml hmp hmdg hmfi⟩
end

variable (hmd : ∀ m, (∀ t e, m = METADATA_Const (t,e) → P e) → P (EXP_Metadata m))
  (hspl : ∀ x : texp T, P x.2 → P (EXP_Splat x)) (hba : ∀ f b, P (EXP_BlockAddress f b))
include hid hi hf hb hn hz hcs hu hp hs hps ha hv hib hneg hic hfb hfc hc hgep hxe hie hsh hxv hiv hsel hfr hasm hmd hspl hba

theorem exp_ind : ∀ x, P x := by
  apply exp_ind_full P (fun m ↦ ∀ t e, m = METADATA_Const (t,e) → P e)
    hid hi hf hb hn hz hcs hu hp hs hps ha hv hib hneg hic hfb hfc hc hgep hxe hie hsh hxv hiv hsel hfr hasm hmd hspl hba
  all_goals intros <;> first | contradiction | cases ‹_ = _›; assumption
end

def is_void_typ : typ → Bool
  | .TYPE_Void | .TYPE_Function .TYPE_Void _ _ => true
  | _ => false

def is_void_instr : instr typ → Bool
  | .INSTR_Comment _ | .INSTR_Fence _ _ | .INSTR_Store _ _ _ => true
  | .INSTR_Call (t, _) _ _ _ => is_void_typ t
  | _ => false

def iop_is_div : ibinop → Bool
  | .UDiv _ | .SDiv _ | .URem | .SRem => true
  | _ => false

def iop_is_signed : ibinop → Bool
  | .SDiv _ | .SRem => true
  | _ => false

def iop_is_shift : ibinop → Bool
  | .Shl _ _ | .AShr _ | .LShr _ => true
  | _ => false

def fop_is_div : fbinop → Bool
  | .FDiv | .FRem => true
  | _ => false

theorem Name_inj {s₁ s₂ : IRString} : Name s₁ = Name s₂ → s₁ = s₂ := raw_id.Name.inj

def is_METADATA_File_info : metadata T → Option file_info
  | .METADATA_File_info f => some f
  | _ => none

def get_file_info (l : List (metadata T)) := l.findSome? is_METADATA_File_info

def no_loc_string : IRString := "[??:??.??-??.??]".toUTF8

def location_string : Option file_info → IRString
  | none => no_loc_string
  | some f => "[".toUTF8 ++ f.filename ++ ":".toUTF8 ++ Utils.StringUtil.show_Z f.start_line ++
    ".".toUTF8 ++ Utils.StringUtil.show_Z f.start_col ++ "-".toUTF8 ++ Utils.StringUtil.show_Z f.end_line ++
    ".".toUTF8 ++ Utils.StringUtil.show_Z f.end_col ++ "]".toUTF8

def location_error_string (l : List (metadata T)) := location_string (get_file_info l)

end Vellvm.Syntax.AstLib
