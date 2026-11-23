/-
Copyright (c) 2026 Vellvm developers. Distributed under the MIT License.
Port of src/rocq/Syntax/TypToDtyp.v.
-/
module

public import Vellvm.Syntax.AstLib
public import Vellvm.Syntax.DynamicTypes
public import Vellvm.Syntax.CFG
public import Vellvm.Syntax.Traversal
public import Vellvm.Utils.ListUtil

@[expose] public section
namespace Vellvm.Syntax.TypToDtyp
open LLVMAst AstLib DynamicTypes
open Vellvm.Numeric.Rocqlib (lex_ord wf_lex_ord)
open Vellvm.Utils.ListUtil (map_In)

universe u v

inductive typ_order : typ → typ → Prop where
  | typ_order_Pointer (t : typ) : typ_order t (TYPE_Pointer (some t))
  | typ_order_Array (sz : Nat) (t : typ) : typ_order t (TYPE_Array sz t)
  | typ_order_Vector (sz : Nat) (t : typ) : typ_order t (TYPE_Vector sz t)
  | typ_order_Struct (fs : List typ) (t : typ) : t ∈ fs → typ_order t (TYPE_Struct fs)
  | typ_order_Packed_struct (fs : List typ) (t : typ) : t ∈ fs → typ_order t (TYPE_Packed_struct fs)
  | typ_order_Function_args (ret : typ) (args : List typ) (v : Bool) (t : typ) :
      t ∈ args → typ_order t (TYPE_Function ret args v)
  | typ_order_Function_ret (ret : typ) (args : List typ) (v : Bool) :
      typ_order ret (TYPE_Function ret args v)

export typ_order (typ_order_Pointer typ_order_Array typ_order_Vector typ_order_Struct
  typ_order_Packed_struct typ_order_Function_args typ_order_Function_ret)

section
variable (P : typ → typ → Prop)
  (ptr : ∀ t, P t (TYPE_Pointer (some t)))
  (arr : ∀ n t, P t (TYPE_Array n t))
  (vec : ∀ n t, P t (TYPE_Vector n t))
  (str : ∀ fs t, t ∈ fs → P t (TYPE_Struct fs))
  (packed : ∀ fs t, t ∈ fs → P t (TYPE_Packed_struct fs))
  (arg : ∀ r as v t, t ∈ as → P t (TYPE_Function r as v))
  (ret : ∀ r as v, P r (TYPE_Function r as v))

include ptr arr vec str packed arg ret

theorem typ_order_ind {s t} (h : typ_order s t) : P s t := by
  cases h <;> solve_by_elim

theorem typ_order_sind {s t} (h : typ_order s t) : P s t :=
  typ_order_ind P ptr arr vec str packed arg ret h
end

/-- Remove the first binding only, so lookup and removal agree in the presence of shadowing. -/
def remove_key {A : Type u} {B : Type v} (eq_dec : DecidableEq A) (a : A) :
    List (A × B) → List (A × B)
  | [] => []
  | (k,b) :: tail => match eq_dec a k with
    | .isTrue _ => tail
    | .isFalse _ => (k,b) :: remove_key eq_dec a tail

theorem wf_typ_order : WellFounded typ_order := by
  apply Subrelation.wf (r := (measure sizeOf).rel) _ (measure sizeOf).wf
  intro s t h
  change sizeOf s < sizeOf t
  cases h <;> simp_wf <;> first | omega | (have := List.sizeOf_lt_of_mem (by assumption); omega)

theorem wf_lt_typ_order : WellFounded (lex_ord Nat.lt typ_order) :=
  wf_lex_ord Nat.lt_wfRel.wf wf_typ_order

theorem remove_key_in {A : Type u} {B : Type v} (a : A) (b : B) (eq_dec : DecidableEq A)
    (l : List (A × B)) (h : (a,b) ∈ l) : (remove_key eq_dec a l).length < l.length := by
  induction l with
  | nil => contradiction
  | cons kv l ih =>
    obtain ⟨k,v⟩ := kv
    cases e : eq_dec a k with
    | isTrue _ => simp [remove_key, e]
    | isFalse ne =>
      rcases List.mem_cons.mp h with eq | mem
      · exact (ne (congrArg Prod.fst eq)).elim
      · simpa [remove_key, e] using ih mem

abbrev TypeEnv := List («ident» × typ)
abbrev Arguments := (_ : TypeEnv) × typ
abbrev lookup (env : TypeEnv) (id : «ident») :=
  env.find? (fun e ↦ @decide (id = e.1) (Ident.eq_dec id e.1))

theorem typ_to_dtyp_base_option_func_obligation_1 (env : TypeEnv) (id : «ident») {k t}
    (h : some (k,t) = lookup env id) : (remove_key Ident.eq_dec id env).length < env.length := by
  have hit := List.mem_of_find?_eq_some h.symm
  have sat := List.find?_some h.symm
  have same : id = k := @of_decide_eq_true _ (Ident.eq_dec id k) sat
  subst k
  exact remove_key_in _ _ _ _ hit

theorem typ_to_dtyp_base_option_func_obligation_2 :
    WellFounded (fun x y : Arguments ↦ x.1.length < y.1.length) :=
  (measure (fun x : Arguments ↦ x.1.length)).wf

section
local instance : WellFoundedRelation Arguments :=
  ⟨_, typ_to_dtyp_base_option_func_obligation_2⟩

def typ_to_dtyp_base_option_func : Arguments → Option dtyp_base
  | ⟨env, t⟩ => match t with
    | .TYPE_I sz => some (.DTYPE_I sz)
    | .TYPE_B sz => some (.DTYPE_B sz)
    | .TYPE_Iptr => some .DTYPE_Iptr
    | .TYPE_Pointer _ | .TYPE_Function .. => some .DTYPE_Pointer
    | .TYPE_Void => some .DTYPE_Void
    | .TYPE_FP fp => some (.DTYPE_FP fp)
    | .TYPE_Label => some .DTYPE_Label
    | .TYPE_Token => some .DTYPE_Token
    | .TYPE_Metadata => some .DTYPE_Metadata
    | .TYPE_X86_mmx => some .DTYPE_X86_mmx
    | .TYPE_Opaque => some .DTYPE_Opaque
    | .TYPE_Identified id => match _h : lookup env id with
      | none => none
      | some (_, u) => typ_to_dtyp_base_option_func ⟨remove_key Ident.eq_dec id env, u⟩
    | .TYPE_Array .. | .TYPE_Vector .. | .TYPE_Struct _ | .TYPE_Packed_struct _ => none
termination_by x => x
decreasing_by exact typ_to_dtyp_base_option_func_obligation_1 _ _ _h.symm
end

def typ_to_dtyp_base_option (env : TypeEnv) (t : typ) : Option dtyp_base :=
  typ_to_dtyp_base_option_func ⟨env,t⟩

theorem typ_to_dtyp_base_option_equation (env : TypeEnv) (t : typ) :
    typ_to_dtyp_base_option env t = match t with
      | .TYPE_I sz => some (.DTYPE_I sz)
      | .TYPE_B sz => some (.DTYPE_B sz)
      | .TYPE_Iptr => some .DTYPE_Iptr
      | .TYPE_Pointer _ | .TYPE_Function .. => some .DTYPE_Pointer
      | .TYPE_Void => some .DTYPE_Void
      | .TYPE_FP fp => some (.DTYPE_FP fp)
      | .TYPE_Label => some .DTYPE_Label
      | .TYPE_Token => some .DTYPE_Token
      | .TYPE_Metadata => some .DTYPE_Metadata
      | .TYPE_X86_mmx => some .DTYPE_X86_mmx
      | .TYPE_Opaque => some .DTYPE_Opaque
      | .TYPE_Identified id => match lookup env id with
        | some (_, u) => typ_to_dtyp_base_option (remove_key Ident.eq_dec id env) u
        | none => none
      | .TYPE_Array .. | .TYPE_Vector .. | .TYPE_Struct _ | .TYPE_Packed_struct _ => none := by
  rw [typ_to_dtyp_base_option, typ_to_dtyp_base_option_func.eq_def]
  cases t <;> simp only
  split <;> simp_all only [typ_to_dtyp_base_option]

abbrev decreases (env : TypeEnv) (t : typ) (outer : TypeEnv) (s : typ) :=
  lex_ord Nat.lt typ_order (env.length, t) (outer.length, s)
abbrev RecursiveCall (env : TypeEnv) (s : typ) :=
  ∀ env' t, decreases env' t env s → dtyp

theorem typ_to_dtyp_func_obligation_1 (env : TypeEnv) {s} (_ : RecursiveCall env s)
    (_ : none = typ_to_dtyp_base_option env s) {sz t} (h : TYPE_Array sz t = s) :
    decreases env t env s := h ▸ .right _ (typ_order_Array sz t)

theorem typ_to_dtyp_func_obligation_2 (env : TypeEnv) {s} (_ : RecursiveCall env s)
    (_ : none = typ_to_dtyp_base_option env s) {fs} (h : TYPE_Struct fs = s) (t) (ht : t ∈ fs) :
    decreases env t env s := h ▸ .right _ (typ_order_Struct fs t ht)

theorem typ_to_dtyp_func_obligation_3 (env : TypeEnv) {s} (_ : RecursiveCall env s)
    (_ : none = typ_to_dtyp_base_option env s) {fs} (h : TYPE_Packed_struct fs = s) (t)
    (ht : t ∈ fs) : decreases env t env s := h ▸ .right _ (typ_order_Packed_struct fs t ht)

theorem typ_to_dtyp_func_obligation_4 (env : TypeEnv) {s} (_ : RecursiveCall env s)
    (_ : none = typ_to_dtyp_base_option env s) {id} (_ : TYPE_Identified id = s) {k t}
    (hit : some (k,t) = lookup env id) : decreases (remove_key Ident.eq_dec id env) t env s :=
  .left _ _ (typ_to_dtyp_base_option_func_obligation_1 env id hit)

theorem typ_to_dtyp_func_obligation_5 :
    WellFounded (fun x y : Arguments ↦ decreases x.1 x.2 y.1 y.2) :=
  InvImage.wf (fun x : Arguments ↦ (x.1.length, x.2)) wf_lt_typ_order

section
local instance : WellFoundedRelation Arguments := ⟨_, typ_to_dtyp_func_obligation_5⟩

def typ_to_dtyp_func : Arguments → dtyp
  | ⟨env, t⟩ => match typ_to_dtyp_base_option env t with
    | some dt => DTYPE_Base dt
    | none => match t with
      | .TYPE_Array sz u => DTYPE_Array false sz (typ_to_dtyp_func ⟨env,u⟩)
      | .TYPE_Struct fs => DTYPE_Struct false (map_In fs fun u _ ↦ typ_to_dtyp_func ⟨env,u⟩)
      | .TYPE_Packed_struct fs => DTYPE_Struct true (map_In fs fun u _ ↦ typ_to_dtyp_func ⟨env,u⟩)
      | .TYPE_Vector sz u => match typ_to_dtyp_base_option env u with
        | none => DTYPE_Base DTYPE_Void
        | some dt => match vector_dtyp_base_dec dt with
          | .isTrue _ => DTYPE_Array true sz (DTYPE_Base dt)
          | .isFalse _ => DTYPE_Base DTYPE_Void
      | .TYPE_Identified id => match _h : lookup env id with
        | none => DTYPE_Base DTYPE_Void
        | some (_, u) => typ_to_dtyp_func ⟨remove_key Ident.eq_dec id env,u⟩
      | _ => DTYPE_Base DTYPE_Void
termination_by x => x
decreasing_by
  exact Prod.Lex.right _ (typ_order_Array _ _)
  all_goals first
    | exact Prod.Lex.right _ (typ_order_Struct _ _ (by assumption))
    | exact Prod.Lex.right _ (typ_order_Packed_struct _ _ (by assumption))
    | exact Prod.Lex.left _ _ (typ_to_dtyp_base_option_func_obligation_1 _ _ _h.symm)
end

/-- Erase pointee types and inline the first matching binding at each named type. -/
def typ_to_dtyp (env : TypeEnv) (t : typ) : dtyp := typ_to_dtyp_func ⟨env,t⟩

theorem typ_to_dtyp_equation (env : TypeEnv) (t : typ) :
    typ_to_dtyp env t = match typ_to_dtyp_base_option env t with
      | some dt => DTYPE_Base dt
      | none => match t with
        | .TYPE_Array sz u => DTYPE_Array false sz (typ_to_dtyp env u)
        | .TYPE_Struct fs => DTYPE_Struct false (map_In fs fun u _ ↦ typ_to_dtyp env u)
        | .TYPE_Packed_struct fs => DTYPE_Struct true (map_In fs fun u _ ↦ typ_to_dtyp env u)
        | .TYPE_Vector sz u => match typ_to_dtyp_base_option env u with
          | some dt => match vector_dtyp_base_dec dt with
            | .isTrue _ => DTYPE_Array true sz (DTYPE_Base dt)
            | .isFalse _ => DTYPE_Base DTYPE_Void
          | none => DTYPE_Base DTYPE_Void
        | .TYPE_Identified id => match lookup env id with
          | some (_,u) => typ_to_dtyp (remove_key Ident.eq_dec id env) u
          | none => DTYPE_Base DTYPE_Void
        | _ => DTYPE_Base DTYPE_Void := by
  rw [typ_to_dtyp, typ_to_dtyp_func.eq_def]
  cases h : typ_to_dtyp_base_option env t <;> cases t <;> simp only [h] <;>
    first | rfl | (split <;> simp_all only [typ_to_dtyp])

open Traversal CFG

class ConvertTyp (F : Type → Type) where
  convert_typ : TypeEnv → F typ → F dtyp

export ConvertTyp (convert_typ)

instance ConvertTyp_exp : ConvertTyp exp := ⟨fun env ↦ tfmap (F := exp) (typ_to_dtyp env)⟩
instance ConvertTyp_instr : ConvertTyp instr := ⟨fun env ↦ tfmap (F := instr) (typ_to_dtyp env)⟩
instance ConvertTyp_term : ConvertTyp terminator :=
  ⟨fun env ↦ tfmap (F := terminator) (typ_to_dtyp env)⟩
instance ConvertTyp_code : ConvertTyp code := ⟨fun env ↦ tfmap (F := code) (typ_to_dtyp env)⟩
instance ConvertTyp_phi : ConvertTyp phi := ⟨fun env ↦ tfmap (F := phi) (typ_to_dtyp env)⟩
instance ConvertTyp_block : ConvertTyp block := ⟨fun env ↦ tfmap (F := block) (typ_to_dtyp env)⟩
instance ConvertTyp_declaration : ConvertTyp declaration :=
  ⟨fun env ↦ tfmap (F := declaration) (typ_to_dtyp env)⟩
instance ConvertTyp_cfg : ConvertTyp cfg := ⟨fun env ↦ tfmap (F := cfg) (typ_to_dtyp env)⟩
instance ConvertTyp_mcfg : ConvertTyp mcfg := ⟨fun env ↦ tfmap (F := mcfg) (typ_to_dtyp env)⟩
instance ConvertTyp_list {A : Type → Type} [TFunctor A] : ConvertTyp (fun T ↦ List (A T)) :=
  ⟨fun env ↦ tfmap (F := fun T ↦ List (A T)) (typ_to_dtyp env)⟩

theorem convert_typ_list_app {F : Type → Type} [TFunctor F] (a b : List (F typ)) (env : TypeEnv) :
    convert_typ (F := fun T ↦ List (F T)) env (a ++ b) =
      convert_typ (F := fun T ↦ List (F T)) env a ++ convert_typ (F := fun T ↦ List (F T)) env b :=
  List.map_append

def convert_types (m : mcfg typ) : mcfg dtyp := convert_typ (F := mcfg) m.m_type_defs m

def convert_types_closed_exp (e : exp typ) : exp dtyp := convert_typ (F := exp) [] e

theorem convert_typ_ocfg_app (a b : ocfg typ) (env : TypeEnv) :
    convert_typ (F := ocfg) env (a ++ b) =
      convert_typ (F := ocfg) env a ++ convert_typ (F := ocfg) env b :=
  convert_typ_list_app (F := block) a b env

theorem convert_typ_code_app (a b : code typ) (env : TypeEnv) :
    convert_typ (F := code) env (a ++ b) =
      convert_typ (F := code) env a ++ convert_typ (F := code) env b :=
  tfmap_list_app _ _ _ a b (typ_to_dtyp env)

theorem convert_typ_mcfg_app (a b : mcfg typ) :
    convert_typ (F := mcfg) [] (modul_app a b) =
      modul_app (convert_typ (F := mcfg) [] a) (convert_typ (F := mcfg) [] b) := by
  have mapFirst (f : IRString → IRString) (x y) :
      (opt_first x y).map f = opt_first (x.map f) (y.map f) := by cases x <;> rfl
  simp only [convert_typ, tfmap, modul_app, endo, mapFirst, List.map_append]

theorem convert_types_app_mcfg (a b : mcfg typ) (ha : a.m_type_defs = []) (hb : b.m_type_defs = []) :
    convert_types (modul_app a b) = modul_app (convert_types a) (convert_types b) := by
  simp only [convert_types, m_type_defs_app, ha, hb, List.nil_append, convert_typ_mcfg_app]

theorem mcfg_of_tle_app (x y : toplevel_entities typ (block typ × List (block typ)))
    (hx : (mcfg_of_modul (modul_of_toplevel_entities x)).m_type_defs = [])
    (hy : (mcfg_of_modul (modul_of_toplevel_entities y)).m_type_defs = []) :
    convert_types (mcfg_of_tle (x ++ y)) =
      modul_app (convert_types (mcfg_of_tle x)) (convert_types (mcfg_of_tle y)) := by
  unfold mcfg_of_tle
  rw [modul_of_toplevel_entities_app, mcfg_of_app_modul, convert_types_app_mcfg _ _ hx hy]

theorem mcfg_of_tle_cons (x : toplevel_entity typ (block typ × List (block typ)))
    (y : toplevel_entities typ (block typ × List (block typ)))
    (hx : (mcfg_of_modul (modul_of_toplevel_entities [x])).m_type_defs = [])
    (hy : (mcfg_of_modul (modul_of_toplevel_entities y)).m_type_defs = []) :
    convert_types (mcfg_of_tle (x :: y)) =
      modul_app (convert_types (mcfg_of_tle [x])) (convert_types (mcfg_of_tle y)) :=
  mcfg_of_tle_app [x] y hx hy

end Vellvm.Syntax.TypToDtyp
