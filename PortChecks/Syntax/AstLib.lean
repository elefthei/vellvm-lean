import PortChecks.SourceType
import Vellvm.Syntax.AstLib

open Vellvm Vellvm.Syntax.LLVMAst Vellvm.Syntax.AstLib

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib|eq_dec_int"
  eq_dec_int : BEq int_ast

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib|eqv_int"
  eqv_int : HasEquiv.{1,0} int_ast

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib.RawIDOrd|eq_refl"
  RawIDOrd.eq_refl : ∀ x : raw_id, x = x

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib.RawIDOrd|eq_sym"
  RawIDOrd.eq_sym : ∀ {x y : raw_id}, x = y → y = x

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib.RawIDOrd|eq_trans"
  RawIDOrd.eq_trans : ∀ {x y z : raw_id}, x = y → y = z → x = z

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib.RawIDOrd|lt_trans"
  RawIDOrd.lt_trans : ∀ {a b c}, RawIDOrd.lt a b → RawIDOrd.lt b c → RawIDOrd.lt a c

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib.RawIDOrd|lt_not_eq"
  RawIDOrd.lt_not_eq : ∀ {a b}, RawIDOrd.lt a b → ¬RawIDOrd.eq a b

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib.RawIDOrd|cmp_lt"
  RawIDOrd.cmp_lt : ∀ a b, RawIDOrd.cmp a b = .lt ↔ RawIDOrd.lt a b

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib.RawIDOrd|cmp_eq"
  RawIDOrd.cmp_eq : ∀ a b, RawIDOrd.cmp a b = .eq ↔ a = b

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib.RawIDOrd|cmp_antisym"
  RawIDOrd.cmp_antisym : ∀ a b, RawIDOrd.cmp a b = (RawIDOrd.cmp b a).swap

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib.RawIDOrd|compare_helper_lt"
  RawIDOrd.compare_helper_lt : ∀ {a b}, RawIDOrd.cmp a b = .lt → RawIDOrd.lt a b

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib.RawIDOrd|compare_helper_gt"
  RawIDOrd.compare_helper_gt : ∀ {a b}, RawIDOrd.cmp a b = .gt → RawIDOrd.lt b a

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib.RawIDOrd|compare_helper_eq"
  RawIDOrd.compare_helper_eq : ∀ {a b}, RawIDOrd.cmp a b = .eq → a = b

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib|eq_dec_raw_id"
  eq_dec_raw_id : BEq raw_id

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib|eqv_raw_id"
  eqv_raw_id : HasEquiv.{1,0} raw_id

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib.InstrIDDec|eq_dec"
  InstrIDDec.eq_dec : ∀ x y : instr_id, Decidable (x = y)

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib|eq_dec_instr_id"
  eq_dec_instr_id : BEq instr_id

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib|eqv_instr_id"
  eqv_instr_id : HasEquiv.{1,0} instr_id

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib.IdentDec|eq_dec"
  IdentDec.eq_dec : ∀ x y : «ident», Decidable (x = y)

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib|eq_dec_ident"
  eq_dec_ident : BEq «ident»

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib|eqv_ident"
  eqv_ident : HasEquiv.{1,0} «ident»

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib|Name_inj"
  Name_inj : ∀ {a b : IRString}, Name a = Name b → a = b

private abbrev TypeCases (P : typ → Sort u) (argsIH : List typ → Sort v) :=
  (∀ n, P (TYPE_I n)) → (∀ n, P (TYPE_B n)) → P TYPE_Iptr →
  (∀ t, P t → P (TYPE_Pointer (some t))) → P (TYPE_Pointer none) → P TYPE_Void →
  (∀ f, P (TYPE_FP f)) → P TYPE_Label → P TYPE_Token → P TYPE_Metadata → P TYPE_X86_mmx →
  (∀ n t, P t → P (TYPE_Array n t)) →
  (∀ r xs va, P r → argsIH xs → P (TYPE_Function r xs va)) →
  (∀ xs, argsIH xs → P (TYPE_Struct xs)) → (∀ xs, argsIH xs → P (TYPE_Packed_struct xs)) →
  P TYPE_Opaque → (∀ n t, P t → P (TYPE_Vector n t)) → (∀ i, P (TYPE_Identified i)) → ∀ t, P t

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib|typ_ind"
  typ_ind : ∀ P : typ → Prop, TypeCases P (fun xs ↦ ∀ t ∈ xs, P t)

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib|typ_rect'"
  typ_rect' : ∀ P : typ → Type _, TypeCases P (fun _ ↦ ∀ u, (P u → typ → P u) → List typ → P u → P u)

private abbrev ExprCases {T : Type} (P : exp T → Prop) (metadataIH : metadata T → Prop)
    (result : Prop) :=
  (∀ i, P (EXP_Ident i)) → (∀ n, P (EXP_Integer n)) → (∀ f, P (EXP_Float f)) →
  (∀ b, P (EXP_Bool b)) → P EXP_Null → P EXP_Zero_initializer →
  (∀ xs : List (texp T), (∀ p ∈ xs, P p.2) → P (EXP_Cstring xs)) → P EXP_Undef → P EXP_Poison →
  (∀ xs : List (texp T), (∀ p ∈ xs, P p.2) → P (EXP_Struct xs)) →
  (∀ xs : List (texp T), (∀ p ∈ xs, P p.2) → P (EXP_Packed_struct xs)) →
  (∀ xs : List (texp T), (∀ p ∈ xs, P p.2) → P (EXP_Array xs)) →
  (∀ xs : List (texp T), (∀ p ∈ xs, P p.2) → P (EXP_Vector xs)) →
  (∀ op t x y, P x → P y → P (OP_IBinop op t x y)) →
  (∀ flags (v : texp T), P v.2 → P (OP_Fneg flags v)) →
  (∀ s op t x y, P x → P y → P (OP_ICmp s op t x y)) →
  (∀ op flags t x y, P x → P y → P (OP_FBinop op flags t x y)) →
  (∀ op flags t x y, P x → P y → P (OP_FCmp op flags t x y)) →
  (∀ c src x dst, P x → P (OP_Conversion c src x dst)) →
  (∀ flags t (p : texp T) (xs : List (texp T)), P p.2 → (∀ x ∈ xs, P x.2) → P (OP_GetElementPtr flags t p xs)) →
  (∀ x y : texp T, P x.2 → P y.2 → P (OP_ExtractElement x y)) →
  (∀ x y z : texp T, P x.2 → P y.2 → P z.2 → P (OP_InsertElement x y z)) →
  (∀ x y z : texp T, P x.2 → P y.2 → P z.2 → P (OP_ShuffleVector x y z)) →
  (∀ (x : texp T) ns, P x.2 → P (OP_ExtractValue x ns)) →
  (∀ (x y : texp T) ns, P x.2 → P y.2 → P (OP_InsertValue x y ns)) →
  (∀ flags (x y z : texp T), P x.2 → P y.2 → P z.2 → P (OP_Select flags x y z)) →
  (∀ x : texp T, P x.2 → P (OP_Freeze x)) →
  (∀ s a i u t c, P (EXP_Asm s a i u t c)) →
  (∀ m, metadataIH m → P (EXP_Metadata m)) → (∀ x : texp T, P x.2 → P (EXP_Splat x)) →
  (∀ f b, P (EXP_BlockAddress f b)) → result

private abbrev MutualCases {T} (P : exp T → Prop) (Q : metadata T → Prop) (result : Prop) :=
  ExprCases P Q (Q METADATA_Null → (∀ id, Q (METADATA_Id id)) →
    (∀ p : texp T, P p.2 → Q (METADATA_Const p)) →
    (∀ xs, (∀ x ∈ xs, Q x) → Q (METADATA_Node xs)) →
    (∀ a b, Q a → Q b → Q (METADATA_Pair a b)) → (∀ s t, Q (METADATA_Debug s t)) →
    (∀ f, Q (METADATA_File_info f)) → result)

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib|exp_ind_full"
  exp_ind_full : ∀ {T : Type} (P : exp T → Prop) (Q : metadata T → Prop), MutualCases P Q (∀ e, P e)

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib|metadata_ind"
  metadata_ind : ∀ {T : Type} (P : exp T → Prop) (Q : metadata T → Prop), MutualCases P Q (∀ m, Q m)

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib|exp_metadata_mut_ind"
  exp_metadata_mut_ind : ∀ {T : Type} (P : exp T → Prop) (Q : metadata T → Prop), MutualCases P Q ((∀ e, P e) ∧ (∀ m, Q m))

#source_check "src/rocq/Syntax/AstLib.v|Vellvm.Syntax.AstLib|exp_ind"
  exp_ind : ∀ {T : Type} (P : exp T → Prop),
    ExprCases P (fun m ↦ ∀ t e, m = METADATA_Const (t, e) → P e) (∀ e, P e)

example : RawIDOrd.cmp (Anon 600) (Name .empty) = .lt ∧
    RawIDOrd.cmp (Name .empty) (Raw (-5)) = .lt ∧
    RawIDOrd.cmp (Name ⟨#[255]⟩) (Name ⟨#[0, 0]⟩) = .gt := by decide
