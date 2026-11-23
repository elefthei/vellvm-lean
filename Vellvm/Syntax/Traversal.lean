/- Copyright (c) 2026 Vellvm developers. Distributed under the MIT License. -/
module

public import Vellvm.Syntax.AstLib
public import Vellvm.Syntax.CFG.Types
public import CTree.Interp.Fold

@[expose] public section
namespace Vellvm.Syntax.Traversal
open LLVMAst ITree

universe u v w

class Endo (T : Type u) where
  endo : T → T

export Endo (endo)

instance {T : Type u} : CoeFun (Endo T) (fun _ ↦ T → T) := ⟨fun e ↦ e.endo⟩

instance Endo_list {T : Type} [Endo T] : Endo (List T) := ⟨List.map endo⟩
instance Endo_option {T : Type} [Endo T] : Endo (Option T) := ⟨Option.map endo⟩
instance Endo_prod {T U : Type} [Endo T] [Endo U] : Endo (T × U) := ⟨Prod.map endo endo⟩

instance Endo_ident [Endo raw_id] : Endo «ident» := ⟨fun
  | .ID_Local i => .ID_Local (endo i)
  | .ID_Global i => .ID_Global (endo i)⟩

instance Endo_instr_id [Endo raw_id] : Endo instr_id := ⟨fun
  | .IId i => .IId (endo i)
  | .IVoid n => .IVoid n⟩

def mapTyp [Endo raw_id] : typ → typ
  | .TYPE_Pointer (some t) => .TYPE_Pointer (some (mapTyp t))
  | .TYPE_Array n t => .TYPE_Array n (mapTyp t)
  | .TYPE_Function t args vararg => .TYPE_Function (mapTyp t) (args.map mapTyp) vararg
  | .TYPE_Struct ts => .TYPE_Struct (ts.map mapTyp)
  | .TYPE_Packed_struct ts => .TYPE_Packed_struct (ts.map mapTyp)
  | .TYPE_Vector n t => .TYPE_Vector n (mapTyp t)
  | .TYPE_Identified i => .TYPE_Identified (endo i)
  | t => t

instance Endo_typ [Endo raw_id] : Endo typ := ⟨mapTyp⟩

section Expression
variable {U V : Type} [Endo raw_id] [Endo ibinop] [Endo icmp] [Endo fbinop] [Endo fcmp]
variable (f : U → V) (debugText : IRString → IRString)

-- Endo and tfmap differ on debug strings, but visit the same expression and metadata children.
mutual
  def mapExp : exp U → exp V
    | .EXP_Ident i => .EXP_Ident (endo i)
    | .EXP_Integer n => .EXP_Integer n
    | .EXP_Float n => .EXP_Float n
    | .EXP_Bool b => .EXP_Bool b
    | .EXP_Null => .EXP_Null
    | .EXP_Zero_initializer => .EXP_Zero_initializer
    | .EXP_Undef => .EXP_Undef
    | .EXP_Poison => .EXP_Poison
    | .EXP_Cstring ts => .EXP_Cstring (mapTExps ts)
    | .EXP_Struct ts => .EXP_Struct (mapTExps ts)
    | .EXP_Packed_struct ts => .EXP_Packed_struct (mapTExps ts)
    | .EXP_Array ts => .EXP_Array (mapTExps ts)
    | .EXP_Vector ts => .EXP_Vector (mapTExps ts)
    | .OP_IBinop op t x y => .OP_IBinop (endo op) (f t) (mapExp x) (mapExp y)
    | .OP_ICmp ss op t x y => .OP_ICmp ss (endo op) (f t) (mapExp x) (mapExp y)
    | .OP_FBinop op fm t x y => .OP_FBinop (endo op) fm (f t) (mapExp x) (mapExp y)
    | .OP_Fneg fm x => .OP_Fneg fm (mapTExp x)
    | .OP_FCmp op fm t x y => .OP_FCmp (endo op) fm (f t) (mapExp x) (mapExp y)
    | .OP_Conversion op s x t => .OP_Conversion op (f s) (mapExp x) (f t)
    | .OP_GetElementPtr fl t p ix => .OP_GetElementPtr fl (f t) (mapTExp p) (mapTExps ix)
    | .OP_ExtractElement x i => .OP_ExtractElement (mapTExp x) (mapTExp i)
    | .OP_InsertElement x y i => .OP_InsertElement (mapTExp x) (mapTExp y) (mapTExp i)
    | .OP_ShuffleVector x y i => .OP_ShuffleVector (mapTExp x) (mapTExp y) (mapTExp i)
    | .OP_ExtractValue x ix => .OP_ExtractValue (mapTExp x) ix
    | .OP_InsertValue x y ix => .OP_InsertValue (mapTExp x) (mapTExp y) ix
    | .OP_Select fm c x y => .OP_Select fm (mapTExp c) (mapTExp x) (mapTExp y)
    | .OP_Freeze x => .OP_Freeze (mapTExp x)
    | .EXP_Asm s a i u t c => .EXP_Asm s a i u t c
    | .EXP_Metadata m => .EXP_Metadata (mapMD m)
    | .EXP_Splat x => .EXP_Splat (mapTExp x)
    | .EXP_BlockAddress fn b => .EXP_BlockAddress (endo fn) (endo b)

  def mapTExp : texp U → texp V
    | (t, e) => (f t, mapExp e)

  def mapTExps : List (texp U) → List (texp V)
    | [] => []
    | x :: xs => mapTExp x :: mapTExps xs

  def mapMD : metadata U → metadata V
    | .METADATA_Null => .METADATA_Null
    | .METADATA_Id i => .METADATA_Id (endo i)
    | .METADATA_Const x => .METADATA_Const (mapTExp x)
    | .METADATA_Node xs => .METADATA_Node (mapMDs xs)
    | .METADATA_Pair x y => .METADATA_Pair (mapMD x) (mapMD y)
    | .METADATA_Debug a b => .METADATA_Debug (debugText a) (debugText b)
    | .METADATA_File_info i => .METADATA_File_info i

  def mapMDs : List (metadata U) → List (metadata V)
    | [] => []
    | x :: xs => mapMD x :: mapMDs xs
end
end Expression

variable {T : Type}

section
variable [Endo T] [Endo raw_id] [Endo ibinop] [Endo icmp] [Endo fbinop] [Endo fcmp] [Endo IRString]

def f_exp : exp T → exp T := mapExp endo endo
def endo_metadata : metadata T → metadata T := mapMD endo endo
instance Endo_exp : Endo (exp T) := ⟨f_exp⟩
instance Endo_metadata : Endo (metadata T) := ⟨endo_metadata⟩
end

instance Endo_texp [Endo T] [Endo (exp T)] : Endo (texp T) := ⟨Prod.map endo endo⟩
instance Endo_tint_literal : Endo tint_literal := ⟨id⟩

instance Endo_clause [Endo T] [Endo (exp T)] : Endo (@landingpad_clause T) := ⟨fun
  | .CATCH x => .CATCH (endo x)
  | .FILTER x => .FILTER (endo x)⟩

instance Endo_operand [Endo T] [Endo (exp T)] [Endo (metadata T)] : Endo (@operand T) := ⟨fun
  | .SSA_value x => .SSA_value (endo x)
  | .Metadata_string m => .Metadata_string (endo m)⟩

instance Endo_operand_bundle [Endo T] [Endo (exp T)] [Endo (metadata T)] [Endo IRString] :
    Endo (@operand_bundle T) := ⟨fun b ↦ ⟨endo b.ob_tag, endo b.ob_ops⟩⟩

instance Endo_instr [Endo T] [Endo (exp T)] [Endo (metadata T)] [Endo raw_id] [Endo IRString]
    [Endo param_attr] [Endo (annotation T)] : Endo (instr T) := ⟨fun
  | .INSTR_Op op => .INSTR_Op (endo op)
  | .INSTR_Call fn xs atts obs => .INSTR_Call (endo fn) (endo xs) (endo atts) (endo obs)
  | .INSTR_Alloca t atts => .INSTR_Alloca (endo t) (endo atts)
  | .INSTR_Load t p atts => .INSTR_Load (endo t) (endo p) (endo atts)
  | .INSTR_Store x p atts => .INSTR_Store (endo x) (endo p) (endo atts)
  | .INSTR_LandingPad t b cs => .INSTR_LandingPad (endo t) b (endo cs)
  | i => i⟩

instance Endo_terminator [Endo T] [Endo (exp T)] [Endo (metadata T)] [Endo IRString]
    [Endo raw_id] [Endo param_attr] [Endo (annotation T)] : Endo (terminator T) := ⟨fun
  | .TERM_Ret x => .TERM_Ret (endo x)
  | .TERM_Ret_void => .TERM_Ret_void
  | .TERM_Br x b c => .TERM_Br (endo x) (endo b) (endo c)
  | .TERM_Br_1 b => .TERM_Br_1 (endo b)
  | .TERM_Switch x b bs => .TERM_Switch (endo x) (endo b) (endo bs)
  | .TERM_IndirectBr x bs fn => .TERM_IndirectBr (endo x) (endo bs) (endo fn)
  | .TERM_Resume x => .TERM_Resume (endo x)
  | .TERM_Invoke fn xs b c atts obs => .TERM_Invoke (endo fn) (endo xs) (endo b) (endo c) (endo atts) (endo obs)
  | .TERM_Unreachable => .TERM_Unreachable⟩

instance Endo_phi [Endo T] [Endo raw_id] [Endo (exp T)] : Endo (phi T) := ⟨fun
  | .Phi fm t xs => .Phi fm (endo t) (endo xs)⟩

instance Endo_block [Endo raw_id] [Endo (code T)] [Endo (terminator T)] [Endo (phi T)]
    [Endo (metadata T)] : Endo (block T) := ⟨fun b ↦
  ⟨endo b.blk_id, endo b.blk_phis, endo b.blk_code, endo b.blk_term, b.blk_comments⟩⟩

instance Endo_annotation [Endo T] [Endo raw_id] [Endo (exp T)] [Endo (metadata T)] :
    Endo (annotation T) := ⟨fun
  | .ANN_metadata l => .ANN_metadata (endo l)
  | .ANN_prefix x => .ANN_prefix (endo x)
  | .ANN_prologue x => .ANN_prologue (endo x)
  | .ANN_personality x => .ANN_personality (endo x)
  | a => a⟩

instance Endo_global [Endo raw_id] [Endo T] [Endo Bool] [Endo int_ast] [Endo IRString]
    [Endo (exp T)] [Endo (metadata T)] : Endo («global» T) := ⟨fun g ↦
  ⟨endo g.g_ident, endo g.g_typ, endo g.g_constant, endo g.g_exp,
    endo g.g_externally_initialized, endo g.g_alias, endo g.g_annotations⟩⟩

instance Endo_declaration [Endo function_id] [Endo T] [Endo IRString] [Endo int_ast]
    [Endo param_attr] [Endo fn_attr] [Endo (annotation T)] [Endo (exp T)] : Endo (declaration T) :=
  ⟨fun d ↦ ⟨endo d.dc_name, endo d.dc_type, endo d.dc_param_attrs, endo d.dc_attrs, endo d.dc_annotations⟩⟩

instance Endo_definition {F : Type} [Endo (declaration T)] [Endo raw_id] [Endo F] :
    Endo (definition T F) := ⟨fun d ↦ ⟨endo d.df_prototype, endo d.df_args, endo d.df_instrs⟩⟩

instance Endo_toplevel_entity {F : Type} [Endo F] [Endo T] [Endo («global» T)] [Endo raw_id]
    [Endo (metadata T)] [Endo (declaration T)] [Endo (definition T F)] [Endo fn_attr]
    [Endo int_ast] [Endo IRString] : Endo (toplevel_entity T F) := ⟨fun
  | .TLE_Comment s => .TLE_Comment s
  | .TLE_Target s => .TLE_Target (endo s)
  | .TLE_Datalayout s => .TLE_Datalayout (endo s)
  | .TLE_Declaration d => .TLE_Declaration (endo d)
  | .TLE_Definition d => .TLE_Definition (endo d)
  | .TLE_Type_decl i t => .TLE_Type_decl (endo i) (endo t)
  | .TLE_Source_filename s => .TLE_Source_filename (endo s)
  | .TLE_Global g => .TLE_Global (endo g)
  | .TLE_Metadata i b m => .TLE_Metadata (endo i) b (endo m)
  | .TLE_Attribute_group i a => .TLE_Attribute_group (endo i) (endo a)⟩

/-- The fiber of a container signature at a fixed answer type (Rocq's `E X`). -/
abbrev RequestAt (E : Effect.{u}) (X : Type u) := { e : E.I // E.O e = X }

instance Endo_of_sum1 {A B : Effect.{u}} {X : Type u} [Endo (RequestAt A X)]
    [Endo (RequestAt B X)] : Endo (RequestAt (A ⊕ₑ B) X) := ⟨fun
  | ⟨.inl i, h⟩ => let j := endo (⟨i, h⟩ : RequestAt A X); ⟨.inl j.val, j.property⟩
  | ⟨.inr i, h⟩ => let j := endo (⟨i, h⟩ : RequestAt B X); ⟨.inr j.val, j.property⟩⟩

instance Endo_itree {X : Type u} {E B : Effect.{u}} [Endo X] [ev : ∀ T, Endo (RequestAt E T)] :
    Endo (CTree.CTree E B X) := ⟨fun t ↦ endo <$> CTree.translate (fun i ↦
      let j := (ev (E.O i)).endo ⟨i, rfl⟩
      ⟨j.val, cast j.property⟩) t⟩

instance (priority := low) Endo_id (T : Type) : Endo T := ⟨id⟩

class TFunctor (F : Type → Type) where
  tfmap : {U V : Type} → (U → V) → F U → F V

export TFunctor (tfmap)

def compose {A : Type u} {B : Type v} {C : Type w} (f : A → B) (g : B → C) : A → C := g ∘ f

instance TFunctor_list : TFunctor List := ⟨List.map⟩
instance TFunctor_list' {F : Type → Type} [TFunctor F] : TFunctor (fun T ↦ List (F T)) :=
  ⟨fun f ↦ List.map (tfmap f)⟩
instance TFunctor_option {F : Type → Type} [TFunctor F] : TFunctor (fun T ↦ Option (F T)) :=
  ⟨fun f ↦ Option.map (tfmap f)⟩

section
variable [Endo raw_id] [Endo ibinop] [Endo icmp] [Endo fbinop] [Endo fcmp]

def ft_exp {U V : Type} (f : U → V) : exp U → exp V := mapExp f id
def ft_metadata {U V : Type} (f : U → V) : metadata U → metadata V := mapMD f id
instance TFunctor_exp : TFunctor exp := ⟨ft_exp⟩
end

instance TFunctor_metadata [TFunctor exp] [Endo raw_id] [Endo IRString] : TFunctor metadata :=
  ⟨ft_metadata⟩

instance TFunctor_texp [TFunctor exp] : TFunctor texp := ⟨fun f ↦ Prod.map f (tfmap f)⟩

instance TFunctor_cmpxchg [Endo Bool] [Endo icmp] [Endo int_ast] [Endo IRString]
    [Endo ordering] [TFunctor texp] : TFunctor cmpxchg := ⟨fun f c ↦
  ⟨endo c.c_weak, endo c.c_volatile, tfmap (F := texp) f c.c_ptr,
    tfmap (F := texp) f c.c_cmp, tfmap (F := texp) f c.c_new, endo c.c_syncscope,
    endo c.c_success_ordering, endo c.c_failure_ordering, endo c.c_align⟩⟩

instance TFunctor_atomicrmw [Endo Bool] [Endo atomic_rmw_operation] [Endo IRString]
    [Endo ordering] [Endo int_ast] [TFunctor texp] : TFunctor atomicrmw := ⟨fun f a ↦
  ⟨endo a.a_volatile, endo a.a_operation, tfmap (F := texp) f a.a_ptr,
    tfmap (F := texp) f a.a_val, endo a.a_syncscope, endo a.a_ordering, endo a.a_align⟩⟩

instance TFunctor_landingpad_clause [TFunctor exp] : TFunctor (@landingpad_clause) := ⟨fun f ↦ fun
  | .CATCH x => .CATCH (tfmap (F := texp) f x)
  | .FILTER x => .FILTER (tfmap (F := texp) f x)⟩

instance TFunctor_operand [TFunctor exp] : TFunctor (@operand) := ⟨fun f ↦ fun
  | .SSA_value x => .SSA_value (tfmap (F := texp) f x)
  | .Metadata_string m => .Metadata_string (tfmap f m)⟩

instance TFunctor_operand_bundle [TFunctor exp] : TFunctor (@operand_bundle) := ⟨fun f b ↦
  ⟨b.ob_tag, b.ob_ops.map (tfmap (F := @operand) f)⟩⟩

instance TFunctor_instr [TFunctor exp] [TFunctor annotation] : TFunctor instr := ⟨fun f i ↦
  let te := tfmap (F := texp) f
  match i with
  | .INSTR_Comment s => .INSTR_Comment s
  | .INSTR_Op x => .INSTR_Op (tfmap f x)
  | .INSTR_Call fn xs anns obs =>
    .INSTR_Call (te fn) (xs.map (Prod.map te id)) (anns.map (tfmap f)) (obs.map (tfmap (F := @operand_bundle) f))
  | .INSTR_Alloca t anns => .INSTR_Alloca (f t) (anns.map (tfmap f))
  | .INSTR_Load t p anns => .INSTR_Load (f t) (te p) (anns.map (tfmap f))
  | .INSTR_Store x p anns => .INSTR_Store (te x) (te p) (anns.map (tfmap f))
  | .INSTR_Fence s o => .INSTR_Fence s o
  | .INSTR_AtomicCmpXchg c => .INSTR_AtomicCmpXchg (tfmap f c)
  | .INSTR_AtomicRMW a => .INSTR_AtomicRMW (tfmap f a)
  | .INSTR_VAArg x t => .INSTR_VAArg (te x) (f t)
  | .INSTR_LandingPad t b cs => .INSTR_LandingPad (f t) b (cs.map (tfmap (F := @landingpad_clause) f))⟩

instance TFunctor_tident [Endo «ident»] : TFunctor (@tident) := ⟨fun f ↦ Prod.map f endo⟩

instance TFunctor_terminator [Endo tint_literal] [Endo raw_id] [TFunctor exp] [TFunctor annotation] :
    TFunctor terminator := ⟨fun f t ↦
  let te := tfmap (F := texp) f
  match t with
  | .TERM_Ret x => .TERM_Ret (te x)
  | .TERM_Ret_void => .TERM_Ret_void
  | .TERM_Br x b c => .TERM_Br (te x) (endo b) (endo c)
  | .TERM_Br_1 b => .TERM_Br_1 (endo b)
  | .TERM_Switch x b bs => .TERM_Switch (te x) (endo b) (endo bs)
  | .TERM_IndirectBr x bs fn => .TERM_IndirectBr (te x) (endo bs) (endo fn)
  | .TERM_Resume x => .TERM_Resume (te x)
  | .TERM_Invoke fn xs b c anns obs => .TERM_Invoke (te fn) (xs.map (Prod.map te id))
    (endo b) (endo c) (anns.map (tfmap f)) (obs.map (tfmap (F := @operand_bundle) f))
  | .TERM_Unreachable => .TERM_Unreachable⟩

instance TFunctor_phi [Endo raw_id] [TFunctor exp] : TFunctor phi := ⟨fun f ↦ fun
  | .Phi fm t xs => .Phi fm (f t) (xs.map (Prod.map endo (tfmap f)))⟩

instance TFunctor_code [Endo raw_id] [TFunctor instr] [TFunctor metadata] : TFunctor code :=
  ⟨fun f ↦ List.map (Prod.map (Prod.map endo (tfmap f)) (List.map (tfmap f)))⟩

instance TFunctor_block [Endo raw_id] [TFunctor instr] [TFunctor terminator] [TFunctor phi]
    [TFunctor metadata] : TFunctor block := ⟨fun f b ↦
  ⟨endo b.blk_id, b.blk_phis.map (Prod.map (Prod.map endo (tfmap f)) (List.map (tfmap f))),
    tfmap (F := code) f b.blk_code,
    Prod.map (Prod.map endo (tfmap f)) (List.map (tfmap f)) b.blk_term, b.blk_comments⟩⟩

instance TFunctor_annotation [TFunctor exp] [Endo raw_id] [TFunctor metadata] [Endo param_attr] :
    TFunctor annotation := ⟨fun f a ↦
  let te := tfmap (F := texp) f
  match a with
  | .ANN_linkage x => .ANN_linkage x
  | .ANN_preemption_specifier x => .ANN_preemption_specifier x
  | .ANN_visibility x => .ANN_visibility x
  | .ANN_dll_storage x => .ANN_dll_storage x
  | .ANN_thread_local_storage x => .ANN_thread_local_storage x
  | .ANN_unnamed_addr x => .ANN_unnamed_addr x
  | .ANN_addrspace x => .ANN_addrspace x
  | .ANN_section x => .ANN_section x
  | .ANN_partition x => .ANN_partition x
  | .ANN_comdat x => .ANN_comdat x
  | .ANN_align x => .ANN_align x
  | .ANN_no_sanitize => .ANN_no_sanitize
  | .ANN_no_sanitize_address => .ANN_no_sanitize_address
  | .ANN_no_sanitize_hwaddress => .ANN_no_sanitize_hwaddress
  | .ANN_sanitize_address_dyninit => .ANN_sanitize_address_dyninit
  | .ANN_metadata xs => .ANN_metadata (xs.map (tfmap f))
  | .ANN_cconv x => .ANN_cconv x
  | .ANN_gc x => .ANN_gc x
  | .ANN_prefix x => .ANN_prefix (te x)
  | .ANN_prologue x => .ANN_prologue (te x)
  | .ANN_personality x => .ANN_personality (te x)
  | .ANN_inalloca => .ANN_inalloca
  | .ANN_num_elements x => .ANN_num_elements (te x)
  | .ANN_volatile => .ANN_volatile
  | .ANN_tail x => .ANN_tail x
  | .ANN_fast_math_flag x => .ANN_fast_math_flag x
  | .ANN_ret_attribute x => .ANN_ret_attribute (endo x)
  | .ANN_fun_attribute x => .ANN_fun_attribute (endo x)
  | .ANN_atomic => .ANN_atomic
  | .ANN_syncscope x => .ANN_syncscope x
  | .ANN_ordering x => .ANN_ordering x⟩

instance TFunctor_global [Endo raw_id] [Endo Bool] [Endo int_ast] [TFunctor exp] [TFunctor metadata] :
    TFunctor «global» := ⟨fun f g ↦
  ⟨endo g.g_ident, f g.g_typ, endo g.g_constant, g.g_exp.map (tfmap f),
    endo g.g_externally_initialized, endo g.g_alias, g.g_annotations.map (tfmap f)⟩⟩

instance TFunctor_declaration [Endo function_id] [Endo IRString] [Endo int_ast] [Endo param_attr]
    [Endo linkage] [Endo visibility] [Endo dll_storage] [Endo cconv] [Endo fn_attr]
    [TFunctor exp] [TFunctor metadata] : TFunctor declaration := ⟨fun f d ↦
  ⟨endo d.dc_name, f d.dc_type, endo d.dc_param_attrs, endo d.dc_attrs, d.dc_annotations.map (tfmap f)⟩⟩

instance TFunctor_definition {F : Type → Type} [TFunctor declaration] [Endo raw_id] [TFunctor F] :
    TFunctor (fun T ↦ definition T (F T)) := ⟨fun f d ↦
  ⟨tfmap f d.df_prototype, endo d.df_args, tfmap (F := F) f d.df_instrs⟩⟩

instance TFunctor_toplevel_entity {F : Type → Type} [TFunctor F] [TFunctor «global»] [Endo raw_id]
    [TFunctor metadata] [TFunctor declaration] [TFunctor (fun T ↦ definition T (F T))]
    [Endo fn_attr] [Endo int_ast] [Endo IRString] : TFunctor (fun T ↦ toplevel_entity T (F T)) :=
  ⟨fun f e ↦ match e with
  | .TLE_Comment s => .TLE_Comment s
  | .TLE_Target s => .TLE_Target (endo s)
  | .TLE_Datalayout s => .TLE_Datalayout (endo s)
  | .TLE_Declaration d => .TLE_Declaration (tfmap f d)
  | .TLE_Definition d => .TLE_Definition (tfmap (F := fun T ↦ definition T (F T)) f d)
  | .TLE_Type_decl i t => .TLE_Type_decl (endo i) (f t)
  | .TLE_Source_filename s => .TLE_Source_filename (endo s)
  | .TLE_Global g => .TLE_Global (tfmap f g)
  | .TLE_Metadata i b m => .TLE_Metadata (tfmap f i) b (tfmap f m)
  | .TLE_Attribute_group i a => .TLE_Attribute_group (endo i) (endo a)⟩

theorem tfmap_list_app {U V : Type} (r : Endo raw_id) (i : TFunctor instr) (m : TFunctor metadata)
    (c1 c2 : code U) (f : U → V) :
    @tfmap code (@TFunctor_code r i m) U V f (c1 ++ c2) =
    @tfmap code (@TFunctor_code r i m) U V f c1 ++ @tfmap code (@TFunctor_code r i m) U V f c2 :=
  List.map_append ..

open CFG

instance Endo_modul {F : Type} [Endo F] [Endo IRString] [Endo T] [Endo («global» T)]
    [Endo (declaration T)] [Endo fn_attr] [Endo raw_id] : Endo (@modul T F) := ⟨fun m ↦
  ⟨endo m.m_name, endo m.m_target, endo m.m_datalayout, endo m.m_type_defs,
    endo m.m_globals, endo m.m_declarations, endo m.m_definitions⟩⟩

instance Endo_cfg [Endo raw_id] [Endo (block T)] : Endo (cfg T) := ⟨fun g ↦
  ⟨endo g.init, endo g.blks, endo g.args⟩⟩

instance Endo_mcfg {F : Type} [Endo T] [Endo F] [Endo IRString] [Endo raw_id]
    [Endo («global» T)] [Endo (declaration T)] [Endo (definition T F)] : Endo (@modul T F) :=
  ⟨fun m ↦ ⟨endo m.m_name, endo m.m_target, endo m.m_datalayout, endo m.m_type_defs,
    endo m.m_globals, endo m.m_declarations, endo m.m_definitions⟩⟩

instance TFunctor_modul {F : Type → Type} [TFunctor F] [Endo IRString] [TFunctor «global»]
    [TFunctor declaration] [Endo raw_id] : TFunctor (fun T ↦ @modul T (F T)) := ⟨fun f m ↦
  ⟨endo m.m_name, endo m.m_target, endo m.m_datalayout, m.m_type_defs.map (Prod.map id f),
    m.m_globals.map (tfmap f), m.m_declarations.map (tfmap f),
    m.m_definitions.map (tfmap (F := fun T ↦ definition T (F T)) f)⟩⟩

instance TFunctor_cfg [Endo raw_id] [TFunctor block] : TFunctor cfg := ⟨fun f g ↦
  ⟨endo g.init, g.blks.map (tfmap f), endo g.args⟩⟩

instance TFunctor_mcfg {F : Type → Type} [TFunctor F] [Endo IRString] [Endo raw_id]
    [TFunctor «global»] [TFunctor declaration] [TFunctor (fun T ↦ definition T (F T))] :
    TFunctor (fun T ↦ @modul T (F T)) := ⟨fun f m ↦
  ⟨endo m.m_name, endo m.m_target, endo m.m_datalayout, m.m_type_defs.map (Prod.map id f),
    m.m_globals.map (tfmap f), m.m_declarations.map (tfmap f),
    m.m_definitions.map (tfmap (F := fun T ↦ definition T (F T)) f)⟩⟩

def swap_raw_id (x y i : raw_id) : raw_id := if i == x then y else if i == y then x else i

def swap_endo_raw_id (x y : raw_id) : Endo raw_id := ⟨swap_raw_id x y⟩

def swap_code (x y : raw_id) (T : Type) : Endo (code T) :=
  letI := swap_endo_raw_id x y
  inferInstance

def swap_cfg (x y : raw_id) (T : Type) : Endo (cfg T) :=
  letI := swap_endo_raw_id x y
  inferInstance

def swap_mcfg (x y : raw_id) (T : Type) : Endo (mcfg T) :=
  letI := swap_endo_raw_id x y
  ⟨tfmap (F := fun U ↦ @modul U (cfg U)) id⟩

def subst_cfg_endo_cfg (fid : function_id) (new_f : cfg T) : Endo (definition T (cfg T)) :=
  ⟨fun d ↦ if d.df_prototype.dc_name == fid then {d with df_instrs := new_f} else d⟩

def subst_cfg (fid : function_id) (new_f : cfg T) : Endo (mcfg T) :=
  letI := subst_cfg_endo_cfg fid new_f
  inferInstance

end Vellvm.Syntax.Traversal
