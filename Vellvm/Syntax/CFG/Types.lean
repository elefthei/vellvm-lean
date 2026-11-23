/- Port of Vellvm, Syntax/CFG.v: data types shared with syntax traversals. -/
module

public import Vellvm.Syntax.LLVMAst

@[expose] public section
namespace Vellvm.Syntax.CFG
open LLVMAst

inductive cmd (T : Type) where
  | Inst : instr T → cmd T
  | Term : terminator T → cmd T

export cmd (Inst Term)

def cmd_rect {T} (P : cmd T → Type u) (hi : ∀ i, P (Inst i)) (ht : ∀ t, P (Term t)) : ∀ c, P c :=
  fun | .Inst i => hi i | .Term t => ht t
abbrev cmd_rec {T} (P : cmd T → Type) := cmd_rect P
theorem cmd_ind {T} (P : cmd T → Prop) (hi : ∀ i, P (Inst i)) (ht : ∀ t, P (Term t)) : ∀ c, P c :=
  cmd.rec hi ht
abbrev cmd_sind := @cmd_ind

abbrev ocfg (T : Type) := List (block T)

structure cfg (T : Type) where
  mkCFG ::
  init : block_id
  blks : ocfg T
  args : List raw_id
export cfg (mkCFG init blks args)

structure modul (T FnBody : Type) where
  mk_modul ::
  m_name : Option IRString
  m_target : Option IRString
  m_datalayout : Option IRString
  m_type_defs : List («ident» × T)
  m_globals : List («global» T)
  m_declarations : List (declaration T)
  m_definitions : List (definition T FnBody)
export modul (mk_modul m_name m_target m_datalayout m_type_defs m_globals m_declarations m_definitions)

abbrev mcfg (T : Type) := modul T (cfg T)

end Vellvm.Syntax.CFG
