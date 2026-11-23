/- Printing probes from Vellvm's Syntax/SurfaceSyntax.v; see LICENSE.md. -/
module

public import Vellvm.Syntax.CFG
public import Vellvm.Syntax.SurfaceSyntax.Display

@[expose] public section
namespace Vellvm.Syntax.SurfaceSyntax
open LLVMAst CFG

-- Notation rather than helper constants keeps the constructors visible when unfolding the examples.
local notation "i32" => typ.TYPE_I ⟨32, by decide⟩
local notation:max "named " s:arg => raw_id.Name (String.toUTF8 s)
local notation:max "localRef " r:arg => exp.EXP_Ident (ID_Local r)
local notation:max "ref " s:arg => localRef (named s)
local notation:max "intLiteral " n:arg => exp.EXP_Integer (Number.signed_int.ofInt n)
local notation:max "add " x:arg y:arg => instr.INSTR_Op (exp.OP_IBinop (ibinop.Add false false) i32 x y)
local notation "i32Ptr" => typ.TYPE_Pointer (some i32)
local notation "align4" => [annotation.ANN_align (Number.signed_int.ofInt 4)]
local notation:max "jump " s:arg n:arg =>
  block.mk_block (named s) [] [] ((instr_id.IVoid n, terminator.TERM_Br_1 (named "merge")), []) none

/-- The straight-line source example, before translation from top-level entities to CFGs. -/
def add_twice : mcfg typ :=
  mcfg_of_tle [.TLE_Definition {
    df_prototype := {
      dc_name := named "main"
      dc_type := .TYPE_Function i32 [i32, .TYPE_Pointer (some (.TYPE_Pointer (some (.TYPE_I ⟨8, by decide⟩))))] false
      dc_param_attrs := ([], [])
      dc_attrs := []
      dc_annotations := [] }
    df_args := [named "argc", named "arcv"]
    df_instrs := ({
      blk_id := .Anon 0
      blk_phis := []
      blk_code := [((.IId (.Anon 1), add (intLiteral 5) (intLiteral 9)), []),
                   ((.IId (.Anon 2), add (localRef (.Anon 1)) (intLiteral 15)), [])]
      blk_term := ((.IVoid 0, .TERM_Ret (i32, localRef (.Anon 2))), [])
      blk_comments := none }, []) }]

/-- A four-block CFG exercising aligned memory instructions, branches and phi display. -/
def test_branch : mcfg typ :=
  ⟨none, none, none, [], [], [], [⟨
    ⟨named "test", .TYPE_Function i32 [i32] false, ([], [[]]), [], []⟩,
    [named "x"], ⟨named "entry", [
      { blk_id := named "entry"
        blk_phis := []
        blk_code := [
          ((.IId (named "a"), .INSTR_Alloca i32 align4), []),
          ((.IVoid 0, .INSTR_Store (i32, intLiteral 5) (i32Ptr, ref "a") align4), []),
          ((.IId (named "b"), .INSTR_Load i32 (i32Ptr, ref "a") align4), []),
          ((.IId (named "c"), add (ref "b") (ref "x")), []),
          ((.IId (named "cond"), .INSTR_Op (.OP_ICmp false .Slt i32 (ref "c") (intLiteral 0))), [])]
        blk_term := ((.IVoid 1, .TERM_Br (.TYPE_I ⟨1, by decide⟩, ref "cond")
          (named "neg") (named "pos")), [])
        blk_comments := none },
      jump "neg" 2, jump "pos" 3,
      { blk_id := named "merge"
        blk_phis := [((named "r", .Phi [] i32 [(named "neg", ref "c"), (named "pos", ref "c")]), [])]
        blk_code := []
        blk_term := ((.IVoid 4, .TERM_Ret (i32, ref "r")), [])
        blk_comments := none }
    ], [named "x"]⟩⟩]⟩

end Vellvm.Syntax.SurfaceSyntax
