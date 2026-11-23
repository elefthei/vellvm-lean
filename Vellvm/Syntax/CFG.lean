/- Port of Vellvm, Syntax/CFG.v. -/
module

public import Vellvm.Syntax.CFG.Types
public import Vellvm.Syntax.RawIdMaps
public import Vellvm.Utils.ListUtil

@[expose] public section
namespace Vellvm.Syntax.CFG
open LLVMAst RawIdMaps Utils.ListUtil

def target_of : toplevel_entity T X → Option IRString
  | .TLE_Target x => some x
  | _ => none

def datalayout_of : toplevel_entity T X → Option IRString
  | .TLE_Datalayout x => some x
  | _ => none

def filename_of : toplevel_entity T X → Option IRString
  | .TLE_Source_filename x => some x
  | _ => none

def globals_of : toplevel_entity T X → List («global» T)
  | .TLE_Global x => [x]
  | _ => []

def declarations_of : toplevel_entity T X → List (declaration T)
  | .TLE_Declaration x => [x]
  | _ => []

def definitions_of : toplevel_entity T X → List (definition T X)
  | .TLE_Definition x => [x]
  | _ => []

def type_defs_of : toplevel_entity T X → List («ident» × T)
  | .TLE_Type_decl i t => [(i, t)]
  | _ => []

def modul_of_toplevel_entities (xs : toplevel_entities T X) : modul T X :=
  ⟨xs.findSome? filename_of, xs.findSome? target_of, xs.findSome? datalayout_of,
   xs.flatMap type_defs_of, xs.flatMap globals_of, xs.flatMap declarations_of, xs.flatMap definitions_of⟩

def tle_of_name : Option IRString → toplevel_entities T X
  | none => []
  | some x => [.TLE_Source_filename x]

def tle_of_target : Option IRString → toplevel_entities T X
  | none => []
  | some x => [.TLE_Target x]

def tle_of_datalayout : Option IRString → toplevel_entities T X
  | none => []
  | some x => [.TLE_Datalayout x]

def tle_of_type_defs (xs : List («ident» × T)) : toplevel_entities T X := xs.map (Function.uncurry TLE_Type_decl)
def tle_of_globals (xs : List («global» T)) : toplevel_entities T X := xs.map TLE_Global
def tle_of_declarations (xs : List (declaration T)) : toplevel_entities T X := xs.map TLE_Declaration
def tle_of_definitions (xs : List (definition T X)) : toplevel_entities T X := xs.map TLE_Definition

def toplevel_entities_of_modul (m : modul T X) : toplevel_entities T X :=
  tle_of_name m.m_name ++ tle_of_target m.m_target ++ tle_of_datalayout m.m_datalayout ++
  tle_of_type_defs m.m_type_defs ++ tle_of_globals m.m_globals ++ tle_of_declarations m.m_declarations ++
  tle_of_definitions m.m_definitions

abbrev Body (T : Type) := block T × List (block T)

def init_of_definition (d : definition T (Body T)) := d.df_instrs.1.blk_id

def annotate_indirectbr (f : function_id) (b : block T) : block T :=
  match b.blk_term with
  | ((i, .TERM_IndirectBr v labels _), md) => { b with blk_term := ((i, .TERM_IndirectBr v labels (some f)), md) }
  | _ => b

def cfg_of_definition (d : definition T (Body T)) : cfg T :=
  ⟨init_of_definition d, (d.df_instrs.1 :: d.df_instrs.2).map (annotate_indirectbr d.df_prototype.dc_name), d.df_args⟩

def mcfg_of_modul (m : modul T (Body T)) : mcfg T :=
  { m with m_definitions := m.m_definitions.map fun d ↦ { d with df_instrs := cfg_of_definition d } }

def find_block (bs : List (block T)) (k : block_id) : Option (block T) :=
  bs.find? (fun b ↦ decide (b.blk_id = k))

/-- Folding from the right makes the first block win on a repeated label, as in `find_block`. -/
def ocfg_map (bs : List (block T)) : rmap (block T) :=
  bs.foldr (fun b m ↦ RM.add b.blk_id b m) (RM.empty _)

def modul_defns_of_mcfg_defns : List (definition T (cfg T)) → Option (List (definition T (Body T)))
  | [] => some []
  | d :: ds => do
    let x :: xs := d.df_instrs.blks | none
    return { d with df_instrs := (x, xs) } :: (← modul_defns_of_mcfg_defns ds)

def modul_of_mcfg (m : mcfg T) : Option (modul T (Body T)) := do
  return { m with m_definitions := ← modul_defns_of_mcfg_defns m.m_definitions }

abbrev Addresses := List (function_id × block_id)

mutual
  def exp_block_addresses : exp T → Addresses
    | .EXP_BlockAddress f b => [(f,b)]
    | .EXP_Cstring l | .EXP_Struct l | .EXP_Packed_struct l | .EXP_Array l | .EXP_Vector l => texps_block_addresses l
    | .OP_Conversion _ _ x _ | .OP_ExtractValue (_,x) _ | .OP_Freeze (_,x) | .OP_Fneg _ (_,x)
    | .EXP_Splat (_,x) => exp_block_addresses x
    | .OP_IBinop _ _ x y | .OP_ICmp _ _ _ x y | .OP_FBinop _ _ _ x y | .OP_FCmp _ _ _ x y
    | .OP_ExtractElement (_,x) (_,y) | .OP_InsertValue (_,x) (_,y) _ => exp_block_addresses x ++ exp_block_addresses y
    | .OP_InsertElement (_,x) (_,y) (_,z) | .OP_ShuffleVector (_,x) (_,y) (_,z)
    | .OP_Select _ (_,x) (_,y) (_,z) => exp_block_addresses x ++ exp_block_addresses y ++ exp_block_addresses z
    | .OP_GetElementPtr _ _ (_,x) l => exp_block_addresses x ++ texps_block_addresses l
    | .EXP_Ident _ | .EXP_Integer _ | .EXP_Float _ | .EXP_Bool _ | .EXP_Null | .EXP_Zero_initializer
    | .EXP_Undef | .EXP_Poison | .EXP_Asm _ _ _ _ _ _ | .EXP_Metadata _ => []

  def texps_block_addresses : List (texp T) → Addresses
    | [] => []
    | (_,x) :: xs => exp_block_addresses x ++ texps_block_addresses xs
end

def instr_block_addresses : instr T → Addresses
  | .INSTR_Op v => exp_block_addresses v
  | .INSTR_Call f args _ _ => texps_block_addresses (f :: args.map Prod.fst)
  | .INSTR_Load _ p _ | .INSTR_VAArg p _ => texps_block_addresses [p]
  | .INSTR_Store v p _ => texps_block_addresses [v, p]
  | .INSTR_AtomicCmpXchg c => texps_block_addresses [c.c_ptr, c.c_cmp, c.c_new]
  | .INSTR_AtomicRMW a => texps_block_addresses [a.a_ptr, a.a_val]
  | .INSTR_Comment _ | .INSTR_Alloca _ _ | .INSTR_Fence _ _ | .INSTR_LandingPad _ _ _ => []

def term_block_addresses : terminator T → Addresses
  | .TERM_IndirectBr v labels f => texps_block_addresses [v] ++
    match f with | some fn => labels.map (fun b ↦ (fn, b)) | none => []
  | .TERM_Ret v | .TERM_Br v _ _ | .TERM_Switch v _ _ | .TERM_Resume v => texps_block_addresses [v]
  | .TERM_Invoke f args _ _ _ _ => texps_block_addresses (f :: args.map Prod.fst)
  | .TERM_Ret_void | .TERM_Br_1 _ | .TERM_Unreachable => []

def block_block_addresses (b : block T) : Addresses :=
  b.blk_phis.flatMap (fun ((_, .Phi _ _ args), _) ↦ args.flatMap fun (_, v) ↦ exp_block_addresses v) ++
  b.blk_code.flatMap (fun ((_, i), _) ↦ instr_block_addresses i) ++ term_block_addresses b.blk_term.1.2

def mcfg_block_addresses (m : mcfg T) : Addresses :=
  m.m_globals.flatMap (fun g ↦ match g.g_exp with | some e => exp_block_addresses e | none => []) ++
  m.m_definitions.flatMap (fun d ↦ d.df_instrs.blks.flatMap block_block_addresses)

def mcfg_of_tle (p : toplevel_entities typ (Body typ)) := mcfg_of_modul (modul_of_toplevel_entities p)

def annotate_definition (d : definition T (Body T)) : definition T (Body T) :=
  let f := annotate_indirectbr d.df_prototype.dc_name
  { d with df_instrs := (f d.df_instrs.1, d.df_instrs.2.map f) }

theorem modul_defns_of_mcfg_defns_map_cfg_of_definition {T} (ds : List (definition T (Body T))) :
    modul_defns_of_mcfg_defns (ds.map (fun d ↦ { d with df_instrs := cfg_of_definition d })) =
      some (ds.map annotate_definition) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons, modul_defns_of_mcfg_defns]
    rw [ih]
    rfl

theorem modul_of_mcfg_of_modul {T} (m : modul T (Body T)) :
    modul_of_mcfg (mcfg_of_modul m) = some { m with m_definitions := m.m_definitions.map annotate_definition } := by
  simp [modul_of_mcfg, mcfg_of_modul, modul_defns_of_mcfg_defns_map_cfg_of_definition]

def opt_first (a b : Option T) : Option T := a.or b

def modul_app (a b : modul T X) : modul T X :=
  ⟨opt_first a.m_name b.m_name, opt_first a.m_target b.m_target, opt_first a.m_datalayout b.m_datalayout,
   a.m_type_defs ++ b.m_type_defs, a.m_globals ++ b.m_globals, a.m_declarations ++ b.m_declarations,
   a.m_definitions ++ b.m_definitions⟩

namespace CFGNotations
scoped infixl:60 " @@ " => modul_app
end CFGNotations

theorem modul_of_toplevel_entities_app {T X} (l r : toplevel_entities T X) :
    modul_of_toplevel_entities (l ++ r) = modul_app (modul_of_toplevel_entities l) (modul_of_toplevel_entities r) := by
  simp [modul_of_toplevel_entities, modul_app, opt_first, List.findSome?_append]

theorem modul_of_toplevel_entities_cons {T X} (e : toplevel_entity T X) (es) :
    modul_of_toplevel_entities (e :: es) = modul_app (modul_of_toplevel_entities [e]) (modul_of_toplevel_entities es) :=
  modul_of_toplevel_entities_app [e] es

theorem m_definitions_app {T X} (p₁ p₂ : modul T X) :
    (modul_app p₁ p₂).m_definitions = p₁.m_definitions ++ p₂.m_definitions := rfl

theorem m_name_app {T X} (p₁ p₂ : modul T X) :
    (modul_app p₁ p₂).m_name = opt_first p₁.m_name p₂.m_name := rfl

theorem m_target_app {T X} (p₁ p₂ : modul T X) :
    (modul_app p₁ p₂).m_target = opt_first p₁.m_target p₂.m_target := rfl

theorem m_datalayout_app {T X} (p₁ p₂ : modul T X) :
    (modul_app p₁ p₂).m_datalayout = opt_first p₁.m_datalayout p₂.m_datalayout := rfl

theorem m_type_defs_app {T X} (p₁ p₂ : modul T X) :
    (modul_app p₁ p₂).m_type_defs = p₁.m_type_defs ++ p₂.m_type_defs := rfl

theorem m_globals_app {T X} (p₁ p₂ : modul T X) :
    (modul_app p₁ p₂).m_globals = p₁.m_globals ++ p₂.m_globals := rfl

theorem m_declarations_app {T X} (p₁ p₂ : modul T X) :
    (modul_app p₁ p₂).m_declarations = p₁.m_declarations ++ p₂.m_declarations := rfl

theorem map_option_cons_inv {A : Type u} {B : Type v} (f : A → Option B) (a : A) (l : List A) {r}
    (h : map_option f (a :: l) = some r) : ∃ b r', f a = some b ∧ map_option f l = some r' ∧ r = b :: r' := by
  cases ha : f a <;> cases hl : map_option f l <;> simp_all [map_option]

theorem map_option_cons {A : Type u} {B : Type v} (f : A → Option B) (a : A) {b} (l : List A) {r}
    (ha : f a = some b) (hl : map_option f l = some r) : map_option f (a :: l) = some (b :: r) := by
  simp [map_option, ha, hl]

theorem map_option_app_inv {A : Type u} {B : Type v} (f : A → Option B) (l₁ l₂ : List A) {r}
    (h : map_option f (l₁ ++ l₂) = some r) :
    ∃ r₁ r₂, map_option f l₁ = some r₁ ∧ map_option f l₂ = some r₂ ∧ r = r₁ ++ r₂ := by
  induction l₁ generalizing r with
  | nil => exact ⟨[], r, rfl, h, rfl⟩
  | cons a l ih =>
    obtain ⟨b, rest, ha, hs, rfl⟩ := map_option_cons_inv f a (l ++ l₂) h
    obtain ⟨xs, ys, hx, hy, rfl⟩ := ih hs
    exact ⟨b :: xs, ys, map_option_cons f a l ha hx, hy, rfl⟩

theorem mcfg_of_app_modul {T} (p q : modul T (Body T)) :
    mcfg_of_modul (modul_app p q) = modul_app (mcfg_of_modul p) (mcfg_of_modul q) := by
  simp [mcfg_of_modul, modul_app]

end Vellvm.Syntax.CFG
