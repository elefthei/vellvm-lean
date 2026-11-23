import PortChecks.SourceType
import Vellvm.Syntax.TypToDtyp

namespace PortChecks.TypToDtyp
open Vellvm.Syntax.LLVMAst Vellvm.Syntax.DynamicTypes Vellvm.Syntax.AstLib
open Vellvm.Syntax.CFG Vellvm.Syntax.Traversal Vellvm.Syntax.TypToDtyp
open Vellvm.Numeric.Rocqlib (lex_ord)
open Vellvm.Utils.ListUtil (map_In)

universe u v

private abbrev OrderCases := ∀ (P : typ → typ → Prop),
  (∀ t, P t (TYPE_Pointer (some t))) → (∀ n t, P t (TYPE_Array n t)) →
  (∀ n t, P t (TYPE_Vector n t)) → (∀ fs t, t ∈ fs → P t (TYPE_Struct fs)) →
  (∀ fs t, t ∈ fs → P t (TYPE_Packed_struct fs)) →
  (∀ r as v t, t ∈ as → P t (TYPE_Function r as v)) →
  (∀ r as v, P r (TYPE_Function r as v)) → ∀ {s t}, typ_order s t → P s t

#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|typ_order_ind"
  typ_order_ind : OrderCases
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|typ_order_sind"
  typ_order_sind : OrderCases
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|wf_typ_order"
  wf_typ_order : WellFounded typ_order
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|wf_lt_typ_order"
  wf_lt_typ_order : WellFounded (lex_ord Nat.lt typ_order)
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|remove_key_in"
  remove_key_in : ∀ {A : Type u} {B : Type v} (a : A) (b : B) (d : DecidableEq A)
    (l : List (A × B)), (a,b) ∈ l → (remove_key d a l).length < l.length

private abbrev Env := List («ident» × typ)
private abbrev lookup (env : Env) (id : «ident») :=
  env.find? (fun e ↦ @decide (id = e.1) (Ident.eq_dec id e.1))
private abbrev less (env : Env) (t : typ) (env' : Env) (s : typ) :=
  lex_ord Nat.lt typ_order (env.length, t) (env'.length, s)
private abbrev recCall (env : Env) (s : typ) :=
  ∀ env' t, less env' t env s → dtyp
private abbrev Args := (_ : Env) × typ

#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|typ_to_dtyp_base_option_func_obligation_1"
  typ_to_dtyp_base_option_func_obligation_1 : ∀ env id {k t}, some (k,t) = lookup env id →
    (remove_key Ident.eq_dec id env).length < env.length
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|typ_to_dtyp_base_option_func_obligation_2"
  typ_to_dtyp_base_option_func_obligation_2 : WellFounded (fun x y : Args ↦ x.1.length < y.1.length)
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|typ_to_dtyp_base_option_equation"
  typ_to_dtyp_base_option_equation : ∀ env t, typ_to_dtyp_base_option env t = match t with
    | .TYPE_I n => some (.DTYPE_I n)
    | .TYPE_B n => some (.DTYPE_B n)
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
    | .TYPE_Array .. | .TYPE_Vector .. | .TYPE_Struct _ | .TYPE_Packed_struct _ => none

#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|typ_to_dtyp_func_obligation_1"
  typ_to_dtyp_func_obligation_1 : ∀ env {s}, recCall env s → none = typ_to_dtyp_base_option env s →
    ∀ {sz t}, TYPE_Array sz t = s → less env t env s
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|typ_to_dtyp_func_obligation_2"
  typ_to_dtyp_func_obligation_2 : ∀ env {s}, recCall env s → none = typ_to_dtyp_base_option env s →
    ∀ {fs}, TYPE_Struct fs = s → ∀ t ∈ fs, less env t env s
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|typ_to_dtyp_func_obligation_3"
  typ_to_dtyp_func_obligation_3 : ∀ env {s}, recCall env s → none = typ_to_dtyp_base_option env s →
    ∀ {fs}, TYPE_Packed_struct fs = s → ∀ t ∈ fs, less env t env s
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|typ_to_dtyp_func_obligation_4"
  typ_to_dtyp_func_obligation_4 : ∀ env {s}, recCall env s → none = typ_to_dtyp_base_option env s →
    ∀ {id}, TYPE_Identified id = s → ∀ {k t}, some (k,t) = lookup env id →
      less (remove_key Ident.eq_dec id env) t env s
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|typ_to_dtyp_func_obligation_5"
  typ_to_dtyp_func_obligation_5 : WellFounded (fun x y : Args ↦ less x.1 x.2 y.1 y.2)
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|typ_to_dtyp_equation"
  typ_to_dtyp_equation : ∀ env t, typ_to_dtyp env t = match typ_to_dtyp_base_option env t with
    | some dt => DTYPE_Base dt
    | none => match t with
      | .TYPE_Array n u => DTYPE_Array false n (typ_to_dtyp env u)
      | .TYPE_Struct fs => DTYPE_Struct false (map_In fs fun u _ ↦ typ_to_dtyp env u)
      | .TYPE_Packed_struct fs => DTYPE_Struct true (map_In fs fun u _ ↦ typ_to_dtyp env u)
      | .TYPE_Vector n u => match typ_to_dtyp_base_option env u with
        | some dt => match vector_dtyp_base_dec dt with
          | .isTrue _ => DTYPE_Array true n (DTYPE_Base dt)
          | .isFalse _ => DTYPE_Base DTYPE_Void
        | none => DTYPE_Base DTYPE_Void
      | .TYPE_Identified id => match lookup env id with
        | some (_,u) => typ_to_dtyp (remove_key Ident.eq_dec id env) u
        | none => DTYPE_Base DTYPE_Void
      | _ => DTYPE_Base DTYPE_Void

#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|ConvertTyp_exp"
  ConvertTyp_exp : ConvertTyp exp
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|ConvertTyp_instr"
  ConvertTyp_instr : ConvertTyp instr
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|ConvertTyp_term"
  ConvertTyp_term : ConvertTyp terminator
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|ConvertTyp_code"
  ConvertTyp_code : ConvertTyp code
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|ConvertTyp_phi"
  ConvertTyp_phi : ConvertTyp phi
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|ConvertTyp_block"
  ConvertTyp_block : ConvertTyp block
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|ConvertTyp_declaration"
  ConvertTyp_declaration : ConvertTyp declaration
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|ConvertTyp_cfg"
  ConvertTyp_cfg : ConvertTyp cfg
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|ConvertTyp_mcfg"
  ConvertTyp_mcfg : ConvertTyp mcfg
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|ConvertTyp_list"
  ConvertTyp_list : ∀ {A : Type → Type} [TFunctor A], ConvertTyp (fun T ↦ List (A T))

#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|convert_typ_list_app"
  convert_typ_list_app : ∀ {F : Type → Type} [TFunctor F] (a b : List (F typ)) (env : Env),
    convert_typ (F := fun T ↦ List (F T)) env (a ++ b) =
      convert_typ (F := fun T ↦ List (F T)) env a ++ convert_typ (F := fun T ↦ List (F T)) env b
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|convert_typ_ocfg_app"
  convert_typ_ocfg_app : ∀ (a b : ocfg typ) (env : Env),
    convert_typ (F := ocfg) env (a ++ b) =
      convert_typ (F := ocfg) env a ++ convert_typ (F := ocfg) env b
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|convert_typ_code_app"
  convert_typ_code_app : ∀ (a b : code typ) (env : Env),
    convert_typ (F := code) env (a ++ b) =
      convert_typ (F := code) env a ++ convert_typ (F := code) env b
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|convert_typ_mcfg_app"
  convert_typ_mcfg_app : ∀ (a b : mcfg typ),
    convert_typ (F := mcfg) [] (modul_app a b) =
      modul_app (convert_typ (F := mcfg) [] a) (convert_typ (F := mcfg) [] b)
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|convert_types_app_mcfg"
  convert_types_app_mcfg : ∀ (a b : mcfg typ), m_type_defs a = [] → m_type_defs b = [] →
    convert_types (modul_app a b) = modul_app (convert_types a) (convert_types b)
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|mcfg_of_tle_app"
  mcfg_of_tle_app : ∀ (xs ys : toplevel_entities typ (block typ × List (block typ))),
    m_type_defs (mcfg_of_modul (modul_of_toplevel_entities xs)) = [] →
    m_type_defs (mcfg_of_modul (modul_of_toplevel_entities ys)) = [] →
      convert_types (mcfg_of_tle (xs ++ ys)) =
        modul_app (convert_types (mcfg_of_tle xs)) (convert_types (mcfg_of_tle ys))
#source_check "src/rocq/Syntax/TypToDtyp.v|Vellvm.Syntax.TypToDtyp|mcfg_of_tle_cons"
  mcfg_of_tle_cons : ∀ (x : toplevel_entity typ (block typ × List (block typ)))
    (ys : toplevel_entities typ (block typ × List (block typ))),
    m_type_defs (mcfg_of_modul (modul_of_toplevel_entities [x])) = [] →
    m_type_defs (mcfg_of_modul (modul_of_toplevel_entities ys)) = [] →
      convert_types (mcfg_of_tle (x :: ys)) =
        modul_app (convert_types (mcfg_of_tle [x])) (convert_types (mcfg_of_tle ys))

end PortChecks.TypToDtyp
