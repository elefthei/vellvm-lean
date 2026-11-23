import Vellvm.Frontend.Parser

open Vellvm.Syntax.LLVMAst Vellvm.Frontend

/-- Exercise all four entry points, including the empty tail prefix's Menhir position. -/
def main : IO Unit := do
  let file := "parser-check.ll".toUTF8
  let source := "define i8 @f(i8) {\n  %3 = call i8 @g(i8 %0)\n  ret i8 %3\n}".toUTF8
  let .ok ([.TLE_Definition f], _) := Parser.toplevel_entities source file
    | throw (IO.userError "definition rejected")
  let (.Anon 1, [.Anon 0], [((.IId (.Anon 3), .INSTR_Call ..), [.METADATA_File_info loc])]) :=
      (f.df_instrs.1.blk_id, f.df_args, f.df_instrs.1.blk_code)
    | throw (IO.userError "argument, block or instruction ID mismatch")
  unless loc.filename == file && loc.start_line == 2 && loc.start_col == 6 && loc.end_col == 24 do
    throw (IO.userError "call span mismatch")
  let .ok (.INSTR_Call .., _) := Parser.test_call "call i8 @g(i8 0)".toUTF8 file
    | throw (IO.userError "assertion call rejected")
  let indexed := "define ptr @p(ptr %p) {\n %x = getelementptr i8, ptr %p, i64 3, !dbg !1\n ret ptr %x\n}"
  let .ok ([.TLE_Definition g], _) := Parser.toplevel_entities indexed.toUTF8 file
    | throw (IO.userError "indexed GEP instruction rejected")
  let [((_, .INSTR_Op (.OP_GetElementPtr _ _ _ [_])), [_, .METADATA_Pair ..])] := g.df_instrs.1.blk_code
    | throw (IO.userError "GEP index or trailing metadata lost")
  let .ok ((.TYPE_FP .FP_float, .EXP_Float (.FS_decimal ..)), _) :=
      Parser.texp "float 127.900000000000005684341886080801486968994140625".toUTF8 file
    | throw (IO.userError "32-bit literal was checked during parsing")
  let quoted := ByteArray.mk #[34, 255, 34]
  let .ok (.METADATA_Id (.Name id), _) := Parser.metadata_id quoted file
    | throw (IO.userError "quoted metadata ID rejected")
  unless id == quoted do throw (IO.userError "quoted metadata ID corrupted")
  let .error e := Parser.toplevel_entities "define void @f(i8) { 0: ret void }".toUTF8 file
    | throw (IO.userError "decreasing anonymous ID accepted")
  let .invalidAnonymousId msg := e.kind | throw (IO.userError "wrong ID error category")
  unless msg == "Unexpected sequential id: expected >= 1 but found 0" do throw (IO.userError msg)
  let .error e := Parser.toplevel_entities "target triple = xyz".toUTF8 file 7
    | throw (IO.userError "malformed target accepted")
  unless e.message .toplevel_entities ==
      "Parsing error: line 7, column 16, token 'xyz': Error token encountered ".toUTF8 do
    throw (IO.userError "wrong lexical position or diagnostic text")
