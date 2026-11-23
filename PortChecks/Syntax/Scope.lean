import PortChecks.SourceType
import Vellvm.Syntax.Scope

open Vellvm.Syntax.LLVMAst Vellvm.Syntax.CFG Vellvm.Syntax.Scope

universe u

#source_check "src/rocq/Syntax/Scope.v|Vellvm.Syntax.Scope|raw_id_eq_dec"
  raw_id_eq_dec : ∀ x y : raw_id, Decidable (x = y)

#source_check "src/rocq/Syntax/Scope.v|Vellvm.Syntax.Scope|instr_id_defs"
  instr_id_defs : Def_sites instr_id

#source_check "src/rocq/Syntax/Scope.v|Vellvm.Syntax.Scope|code_defs"
  code_defs : ∀ {T : Type}, Def_sites (code T)

#source_check "src/rocq/Syntax/Scope.v|Vellvm.Syntax.Scope|block_def_sites"
  block_def_sites : ∀ {T : Type}, Def_sites (block T)

#source_check "src/rocq/Syntax/Scope.v|Vellvm.Syntax.Scope|ocfg_def_sites"
  ocfg_def_sites : ∀ {T : Type}, Def_sites (ocfg T)

#source_check "src/rocq/Syntax/Scope.v|Vellvm.Syntax.Scope|cfg_def_sites"
  cfg_def_sites : ∀ {T : Type}, Def_sites (cfg T)

#source_check "src/rocq/Syntax/Scope.v|Vellvm.Syntax.Scope|ident_use_sites"
  ident_use_sites : Use_sites «ident»

#source_check "src/rocq/Syntax/Scope.v|Vellvm.Syntax.Scope|exp_use_sites"
  exp_use_sites : ∀ {T : Type}, Use_sites (exp T)

#source_check "src/rocq/Syntax/Scope.v|Vellvm.Syntax.Scope|texp_use_sites"
  texp_use_sites : ∀ {T : Type}, Use_sites (texp T)

#source_check "src/rocq/Syntax/Scope.v|Vellvm.Syntax.Scope|option_use_sites"
  option_use_sites : ∀ {T : Type u} [Use_sites T], Use_sites (Option T)

#source_check "src/rocq/Syntax/Scope.v|Vellvm.Syntax.Scope|landingpad_clause_use_sites"
  landingpad_clause_use_sites : ∀ {T : Type}, Use_sites (@landingpad_clause T)

#source_check "src/rocq/Syntax/Scope.v|Vellvm.Syntax.Scope|instr_use_sites"
  instr_use_sites : ∀ {T : Type}, Use_sites (instr T)

#source_check "src/rocq/Syntax/Scope.v|Vellvm.Syntax.Scope|code_use_sites"
  code_use_sites : ∀ {T : Type}, Use_sites (code T)

#source_check "src/rocq/Syntax/Scope.v|Vellvm.Syntax.Scope|term_use_sites"
  term_use_sites : ∀ {T : Type}, Use_sites (terminator T)

#source_check "src/rocq/Syntax/Scope.v|Vellvm.Syntax.Scope|phi_use_sites"
  phi_use_sites : ∀ {T : Type}, Use_sites (phi T)

#source_check "src/rocq/Syntax/Scope.v|Vellvm.Syntax.Scope|block_use_sites"
  block_use_sites : ∀ {T : Type}, Use_sites (block T)

#source_check "src/rocq/Syntax/Scope.v|Vellvm.Syntax.Scope|ocfg_use_sites"
  ocfg_use_sites : ∀ {T : Type}, Use_sites (ocfg T)

#source_check "src/rocq/Syntax/Scope.v|Vellvm.Syntax.Scope|cfg_use_sites"
  cfg_use_sites : ∀ {T : Type}, Use_sites (cfg T)
