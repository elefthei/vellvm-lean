import Vellvm.Frontend.Lexer

open Vellvm.Frontend

private def numericFixture : Option Bool := do
  let l := Lexer.init "i21: i21z i21 -00.1E+02 s0x0a".toUTF8 .empty
  let (⟨.LABEL label, _, _⟩, l) ← l.next.toOption | none
  let (⟨.KW_UNKNOWN name, _, _⟩, l) ← l.next.toOption | none
  let (⟨.I width, _, _⟩, l) ← l.next.toOption | none
  let (⟨.FLOAT (.FS_decimal (.DecimalExp (.Neg (.D0 (.D0 .Nil))) (.D1 .Nil)
    (.Pos (.D0 (.D2 .Nil))))), _, _⟩, l) ← l.next.toOption | none
  let (⟨.INTEGER (.IntHexadecimal (.Neg (.D0 (.Da .Nil)))), _, _⟩, _) ← l.next.toOption | none
  return label == "i21".toUTF8 && name == "i21z".toUTF8 && width.val == 21

private def metadataFixture : Option Bool := do
  let l := Lexer.init ";comment\r\n#dbg_val((a)) !DIType(x(\n)y) ret: ret !ret".toUTF8 .empty
  let (⟨.METADATA_DEBUG di body, p, _⟩, l) ← l.next.toOption | none
  let (⟨.fixed .KW_RET_COLON, _, _⟩, l) ← l.next.toOption | none
  let (⟨.fixed .KW_RET, _, _⟩, l) ← l.next.toOption | none
  let (⟨.METADATA_NAME name, _, _⟩, l) ← l.next.toOption | none
  return di == "Type".toUTF8 && body == "x(\n)y".toUTF8 && p.line == 3 && p.column == 2 &&
    name == "ret".toUTF8 && l.histogram["ret"]? == some 1

private def stringFixture : Option Bool := do
  let s := ByteArray.mk #[34, 255, 92, 50, 50, 92, 120, 34]
  let (⟨.STRING raw, p, _⟩, _) ← (Lexer.init s .empty).next.toOption | none
  return p.column == 7 && unescape raw == ByteArray.mk #[255, 34, 92, 120] &&
    unescape (escape raw) == raw

private def errorFixture : Bool :=
  match (Lexer.init "0xH012".toUTF8 .empty).next with
  | .error { kind := .failure msg, lexeme, .. } =>
    msg == "got ill-sized hex literal: 012" && lexeme == "0xH012".toUTF8
  | _ => false

def main : IO Unit := do
  unless numericFixture == some true do throw (IO.userError "lexer: numeric spellings or precedence")
  unless metadataFixture == some true do throw (IO.userError "lexer: metadata positions or histogram")
  unless stringFixture == some true do throw (IO.userError "lexer: string bytes or escapes")
  unless errorFixture do throw (IO.userError "lexer: invalid hexadecimal width")
