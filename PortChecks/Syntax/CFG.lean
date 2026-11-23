import PortChecks.SourceType
import Vellvm.Syntax.CFG

open Vellvm.Syntax.LLVMAst Vellvm.Syntax.CFG Vellvm.Utils.ListUtil
universe u v

#source_check "src/rocq/Syntax/CFG.v|Vellvm.Syntax.CFG|cmd_ind"
  cmd_ind : ∀ {T : Type} (P : cmd T → Prop), (∀ i, P (Inst i)) → (∀ t, P (Term t)) → ∀ c, P c

#source_check "src/rocq/Syntax/CFG.v|Vellvm.Syntax.CFG|cmd_sind"
  cmd_sind : ∀ {T : Type} (P : cmd T → Prop), (∀ i, P (Inst i)) → (∀ t, P (Term t)) → ∀ c, P c

#source_check "src/rocq/Syntax/CFG.v|Vellvm.Syntax.CFG|modul_defns_of_mcfg_defns_map_cfg_of_definition"
  modul_defns_of_mcfg_defns_map_cfg_of_definition : ∀ {T} (l : List (definition T (block T × List (block T)))),
    modul_defns_of_mcfg_defns (l.map (fun d ↦ mk_definition d.df_prototype d.df_args (cfg_of_definition d))) =
      some (l.map annotate_definition)

#source_check "src/rocq/Syntax/CFG.v|Vellvm.Syntax.CFG|modul_of_mcfg_of_modul"
  modul_of_mcfg_of_modul : ∀ {T} (m : modul T (block T × List (block T))),
    modul_of_mcfg (mcfg_of_modul m) = some { m with m_definitions := m.m_definitions.map annotate_definition }

#source_check "src/rocq/Syntax/CFG.v|Vellvm.Syntax.CFG|modul_of_toplevel_entities_cons"
  modul_of_toplevel_entities_cons : ∀ {T X} (e : toplevel_entity T X) es, modul_of_toplevel_entities (e :: es) =
    modul_app (modul_of_toplevel_entities [e]) (modul_of_toplevel_entities es)

#source_check "src/rocq/Syntax/CFG.v|Vellvm.Syntax.CFG|modul_of_toplevel_entities_app"
  modul_of_toplevel_entities_app : ∀ {T X} (l r : toplevel_entities T X), modul_of_toplevel_entities (l ++ r) =
    modul_app (modul_of_toplevel_entities l) (modul_of_toplevel_entities r)

#source_check "src/rocq/Syntax/CFG.v|Vellvm.Syntax.CFG|m_definitions_app"
  m_definitions_app : ∀ {T X} (a b : modul T X), (modul_app a b).m_definitions = a.m_definitions ++ b.m_definitions

#source_check "src/rocq/Syntax/CFG.v|Vellvm.Syntax.CFG|m_name_app"
  m_name_app : ∀ {T X} (a b : modul T X), (modul_app a b).m_name = opt_first a.m_name b.m_name

#source_check "src/rocq/Syntax/CFG.v|Vellvm.Syntax.CFG|m_target_app"
  m_target_app : ∀ {T X} (a b : modul T X), (modul_app a b).m_target = opt_first a.m_target b.m_target

#source_check "src/rocq/Syntax/CFG.v|Vellvm.Syntax.CFG|m_datalayout_app"
  m_datalayout_app : ∀ {T X} (a b : modul T X), (modul_app a b).m_datalayout = opt_first a.m_datalayout b.m_datalayout

#source_check "src/rocq/Syntax/CFG.v|Vellvm.Syntax.CFG|m_type_defs_app"
  m_type_defs_app : ∀ {T X} (a b : modul T X), (modul_app a b).m_type_defs = a.m_type_defs ++ b.m_type_defs

#source_check "src/rocq/Syntax/CFG.v|Vellvm.Syntax.CFG|m_globals_app"
  m_globals_app : ∀ {T X} (a b : modul T X), (modul_app a b).m_globals = a.m_globals ++ b.m_globals

#source_check "src/rocq/Syntax/CFG.v|Vellvm.Syntax.CFG|m_declarations_app"
  m_declarations_app : ∀ {T X} (a b : modul T X), (modul_app a b).m_declarations = a.m_declarations ++ b.m_declarations

#source_check "src/rocq/Syntax/CFG.v|Vellvm.Syntax.CFG|map_option_cons_inv"
  map_option_cons_inv : ∀ {A : Type u} {B : Type v} (f : A → Option B) a l {r}, map_option f (a :: l) = some r →
    ∃ b r', f a = some b ∧ map_option f l = some r' ∧ r = b :: r'

#source_check "src/rocq/Syntax/CFG.v|Vellvm.Syntax.CFG|map_option_cons"
  map_option_cons : ∀ {A : Type u} {B : Type v} (f : A → Option B) a {b} l {r}, f a = some b →
    map_option f l = some r → map_option f (a :: l) = some (b :: r)

#source_check "src/rocq/Syntax/CFG.v|Vellvm.Syntax.CFG|map_option_app_inv"
  map_option_app_inv : ∀ {A : Type u} {B : Type v} (f : A → Option B) l₁ l₂ {r}, map_option f (l₁ ++ l₂) = some r →
    ∃ s t, map_option f l₁ = some s ∧ map_option f l₂ = some t ∧ r = s ++ t

#source_check "src/rocq/Syntax/CFG.v|Vellvm.Syntax.CFG|mcfg_of_app_modul"
  mcfg_of_app_modul : ∀ {T} (p q : modul T (block T × List (block T))),
    mcfg_of_modul (modul_app p q) = modul_app (mcfg_of_modul p) (mcfg_of_modul q)

-- Later definitions of the same label cannot shadow the head block.
example {T} (b : block T) (bs : List (block T)) :
    Vellvm.Syntax.RawIdMaps.RM.find b.blk_id (ocfg_map (b :: bs)) = some b := by simp [ocfg_map]
