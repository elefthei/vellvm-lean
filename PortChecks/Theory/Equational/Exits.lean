import PortChecks.SourceType
import Vellvm.Theory.Equational.Exits

open Vellvm.Semantics.Interfaces.Params Vellvm.Semantics.Denotation
open Vellvm.Syntax.DynamicTypes Vellvm.Syntax.LLVMAst Vellvm.Syntax.Scope
open Vellvm.Theory.Equational

#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_terminator_exits_in_outputs"
  denote_terminator_exits_in_outputs : ∀ [Pa : Params]
      (term : (instr_id × terminator dtyp) × List (metadata dtyp)),
    has_post (denote_terminator term)
      (Sum.elim (fun id ↦ id ∈ terminator_outputs term.1.2) (fun _ ↦ True))

#source_check "src/rocq/Theory/Equational.v|Vellvm.Theory.Equational|denote_bk_exits_in_outputs"
  denote_bk_exits_in_outputs : ∀ [Pa : Params] (vararg : Option Pa.PTR.ptr) (b : block dtyp)
      (from_ : block_id),
    has_post (denote_block b from_ vararg) (Sum.elim (fun id ↦ id ∈ successors b) (fun _ ↦ True))
