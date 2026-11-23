import Vellvm.Semantics.Denotation
import Vellvm.Semantics.InterpretationStack

namespace Vellvm.Semantics.Notations.SemNotations

scoped notation "ℑs" => InterpretationStack.interp_mcfg

scoped notation:max "⟦" e " at? " t "⟧e" => Denotation.denote_exp t e
scoped notation:max "⟦" e " at " t "⟧e" => Denotation.denote_exp (some t) e
scoped notation:max "⟦" e "⟧e" => Denotation.denote_exp none e
scoped notation:max "⟦" e " at? " t "⟧e'" => Denotation.denote_exp' t e
scoped notation:max "⟦" e " at " t "⟧e'" => Denotation.denote_exp' (some t) e
scoped notation:max "⟦" e "⟧e'" => Denotation.denote_exp' none e
scoped notation:max "⟦" i "⟧i" => Denotation.denote_instr i
scoped notation:max "⟦" c "⟧c" => Denotation.denote_code c
scoped notation:max "⟦" t "⟧t" => Denotation.denote_terminator t
scoped notation:max "⟦" p "⟧Φ " pred:max => Denotation.denote_phi pred p
scoped notation:max "⟦" ps "⟧Φs " pred:max => Denotation.denote_phis pred ps
scoped notation:max "⟦" b "⟧b" => Denotation.denote_block b
scoped notation:max "⟦" bs "⟧bs" => Denotation.denote_ocfg bs
scoped notation:max "⟦" f "⟧cfg" => Denotation.denote_cfg f
scoped notation:max "⟦" f "⟧f" => Denotation.denote_function f

end Vellvm.Semantics.Notations.SemNotations
