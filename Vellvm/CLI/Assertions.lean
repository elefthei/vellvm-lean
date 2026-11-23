/-
 *                     Vellvm - the Verified LLVM project
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>
 *   Distributed under the GNU General Public License, version 3 or later.
-/
import Vellvm.CLI.Run
import Vellvm.Semantics.TopLevel.Linking
import Vellvm.Semantics.Denotation.Expressions
import Vellvm.Syntax.TypToDtyp

namespace Vellvm.CLI
open Frontend Platform Syntax LLVMAst DynamicTypes Semantics Interfaces.Params DynamicValues

attribute [local instance] P

private inductive Expectation where
  | equal (ty : dtyp) (expected : Value)
  | succeeds | fails | ub (line : Int)

private structure Assertion where
  expect : Expectation
  entry : raw_id
  args : List (dtyp × Value)

private inductive Directive where
  | eq | succeeds | fails | ub (digits : ByteSlice)

private def skipSpace (s : ByteArray) (i : Nat) :=
  (s.findIdx? (fun b ↦ b != 32 && b != 9) i).getD s.size

/-- Only spaces and tabs are whitespace in assertion headers. An unrecognized header is a comment. -/
private def header (s : ByteArray) (start : Nat) : Option (Directive × Nat) := do
  let semi := skipSpace s start
  guard (s[semi]? == some 59)
  let a := skipSpace s (semi + 1)
  let wordAt := fun (i : Nat) (word : String) ↦
    s.toByteSlice i (i + word.utf8ByteSize) == word.toUTF8.toByteSlice
  guard (wordAt a "ASSERT")
  let k := skipSpace s (a + 6)
  guard (k > a + 6)
  let (op, next) : Directive × Nat ←
    if wordAt k "EQ" then pure (.eq, k + 2)
    else if wordAt k "SUCCEEDS" then pure (.succeeds, k + 8)
    else if wordAt k "FAILS" then pure (.fails, k + 5)
    else do
      guard (wordAt k "UB")
      let d := skipSpace s (k + 2)
      guard (d > k + 2)
      let e := (s.findIdx? (fun b ↦ b < 48 || b > 57) d).getD s.size
      guard (e > d)
      pure (.ub (s.toByteSlice d e), e)
  let colon := skipSpace s next
  guard (s[colon]? == some 58)
  return (op, skipSpace s (colon + 1))

private def closedValue (x : texp typ) : Except IRString (dtyp × Value) := do
  let ty := TypToDtyp.typ_to_dtyp [] x.1
  let some v := Denotation.denote_closed_exp ty (TypToDtyp.convert_types_closed_exp x.2)
    | throw ("Assertion includes unsupported expression:\n\t".toUTF8 ++ ShowAST.show_typ x.1 ++
        " ".toUTF8 ++ ShowAST.show_exp false x.2)
  return (ty, v)

private def callData (i : instr typ) : Except IRString (raw_id × List (dtyp × Value)) := do
  let .INSTR_Call (_, callee) args _ _ := i
    | throw "Assertion includes unsupported instruction (must be a call)".toUTF8
  let args ← args.mapM fun arg ↦ closedValue arg.1
  let .EXP_Ident (.ID_Global entry) := callee | throw "found non-function name".toUTF8
  return (entry, args)

private def parseCall (msg : String) (s : ByteArray) : Except IRString (instr typ) := do
  let .ok (i, _) := Parser.test_call s .empty | throw (msg.toUTF8 ++ s)
  return i

private def parseLine (s : ByteArray) (start stop : Nat) : Except IRString (Option Assertion) := do
  let some (op, body) := header s start | return none
  match op with
  | .eq =>
    -- The first `.*` in the source regex is greedy: split on the last equals sign.
    let mut j := stop
    while j > body do
      j := j - 1
      if s[j]! == 61 then
        let lhs := s.extract body j
        let .ok (x, _) := Parser.texp lhs .empty
          | throw ("Ill-formed ASSERT EQ left-hand-side: ".toUTF8 ++ lhs)
        let i ← parseCall "Ill-formed ASSERT EQ right-hand-side: " (s.extract (j + 1) stop)
        let (ty, expected) ← closedValue x
        let (entry, args) ← callData i
        return some ⟨.equal ty expected, entry, args⟩
    return none
  | _ =>
    let msg := match op with
      | .succeeds => "ill-formed assert succeeds: "
      | .fails => "ill-formed assert fails: "
      | _ => "ill-formed assert UB: "
    let (entry, args) ← callData (← parseCall msg (s.extract body stop))
    match op with
    | .ub digits =>
      let some n := Parser.ocamlInt? digits.toByteArray | throw "int_of_string".toUTF8
      return some ⟨.ub n, entry, args⟩
    | .succeeds => return some ⟨.succeeds, entry, args⟩
    | _ => return some ⟨.fails, entry, args⟩

private def parseAssertions (s : ByteArray) : Action (List Assertion) := do
  let mut start := 0
  let mut cases := []
  while start < s.size do
    let stop := (s.findIdx? (· == 10) start).getD s.size
    match parseLine s start stop with
    | .error m => throw (.failure m)
    | .ok (some a) => cases := a :: cases
    | .ok none => pure ()
    start := stop + 1
  return cases.reverse

#guard (header " ;\tASSERT UB 0005 : call".toUTF8 0).map Prod.snd == some 20
#guard (header "; ASSERT UBS : call".toUTF8 0).isNone

private def Assertion.name (a : Assertion) : IRString := Id.run do
  if let .ub n := a.expect then return s!"UB expected on line {n}".toUTF8
  let fn := match a.entry with
    | .Raw n => s!"_RAW_{n}".toUTF8
    | id => "@".toUTF8 ++ ShowAST.show_raw_id id
  let args := ShowAST.concat_str_sep ", ".toUTF8 (a.args.map fun (_, v) ↦ show_dvalue v)
  let call := fn ++ "(".toUTF8 ++ args ++ ")".toUTF8
  match a.expect with
  | .equal _ v => return show_dvalue v ++ " = ".toUTF8 ++ call
  | .fails => return "FAILS ".toUTF8 ++ call
  | _ => return call

private def assertEqual (ty : dtyp) (expected got : Value) : Action Unit := do
  unless dvalue_is_canonical ty got do
    throw (.failure ("ASSERT EQ failed: the result is not a canonical value of type ".toUTF8 ++
      ShowAST.show_dtyp ty ++ "\ngot:\n\t".toUTF8 ++ show_dvalue got))
  let equal ← if dvalue_is_poison expected then pure (dvalue_eqb expected got) else
    match ty with
    | .DTYPE_Base (.DTYPE_I _) | .DTYPE_Base .DTYPE_Iptr | .DTYPE_Base .DTYPE_Pointer =>
      if dvalue_is_poison got then pure false else
        match Operations.Compare.eval_icmp false .Eq ty expected got with
        | .raise_ret (.DVALUE_Base (.DVALUE_I _ x)) => pure (Numeric.Integers.eq x Numeric.Integers.one)
        | .raise_ret _ => fail "non-i1 value"
        | .raise_error m => throw (.failure ("ERROR: ".toUTF8 ++ m))
        | .raise_oom m => throw (.failure ("OOM: ".toUTF8 ++ m))
        | .raise_ub m => throw (.failure ("UB: ".toUTF8 ++ m))
    | _ => pure (dvalue_eqb expected got)
  unless equal do
    throw (.failure ("ASSERT EQ failed: \ngot:\n\t".toUTF8 ++ show_dvalue got ++
      "\nasserted:\n\t".toUTF8 ++ show_dvalue expected))

private def runAssertion (loc : IO.Ref (Option file_info)) (cfg : Config) (debug : Bool)
    (path : String) (prog : Driver.Program) (a : Assertion) : Action Unit := do
  let invoke := fun ty ↦ runCall loc debug ty a.entry a.args prog
  let void := DTYPE_Base DTYPE_Void
  match a.expect with
  | .equal ty expected =>
    verb cfg s!"running ASSERT in {path}\n"
    match ← invoke ty with
    | .ok got => assertEqual ty expected got
    | .error e => throw (.failure e.describe)
  | .succeeds => if let .error e ← invoke void then throw (.failure e.describe)
  | .ub _ =>
    match ← invoke void with
    | .error (.undefinedBehavior _) => pure ()
    | .error e => throw (.failure e.describe)
    | .ok v => throw (.failure (a.name ++ " but got ".toUTF8 ++ show_dvalue v))
  | .fails =>
    if let .ok (.ok v) ← (invoke void).toBaseIO then
      throw (.failure ("expected uncaught exception, but got ".toUTF8 ++ show_dvalue v))

private structure Group where
  path : String
  prog : Driver.Program
  cases : List Assertion

private def runSuite (cfg : Config) (debug : Bool) (linkFiles : List Driver.Program)
    (groups : List Group) : Action UInt32 := do
  let loc ← IO.mkRef (none : Option file_info)
  let mut passed := 0
  let mut failed := 0
  let mut report := ByteArray.empty
  for g in groups do
    let prog := TopLevel.link_all linkFiles g.prog
    let mut details := ByteArray.empty
    let mut bad := false
    for a in g.cases do
      try
        runAssertion loc cfg debug g.path prog a
        passed := passed + 1
        if cfg.verbose then details := details ++ " PASSED - ".toUTF8 ++ a.name ++ "\n".toUTF8
      catch e =>
        let msg := match e with
          | .failure m => m
          | _ => "test threw exception: ".toUTF8 ++ e.describe
        bad := true
        failed := failed + 1
        details := details ++ " FAILED - ".toUTF8 ++ a.name ++ "\n\t   ERROR: ".toUTF8 ++ msg ++ "\n".toUTF8
    if bad then report := report ++ s!"\n{g.path}:".toUTF8 ++ details
    else if cfg.verbose then
      let status := if g.cases.isEmpty then "NO ASSERT" else "PASSED"
      report := report ++ s!"\n{g.path}: {status}".toUTF8
  let total := passed + failed
  (← IO.getStdout).write (report ++ "\n(*-------------------------------------- *)\n".toUTF8 ++
    s!"Passed: {passed}/{total}\nFailed: {failed}/{total}\n\n".toUTF8)
  return if failed == 0 then 0 else 1

def testFile (cfg : Config) (debug : Bool) (linkFiles : List Driver.Program) (path : String) :
    Action UInt32 := do
  configure cfg
  verb cfg s!"* processing file: {path}\n"
  let (_, ext) ← basenameExt path
  unless ext == "ll" do fail s!"found unsupported file type: {path}"
  let cases ← parseAssertions (← readInput path)
  verb cfg "Parsed successfully\n"
  let (prog, _) ← Driver.parseFile path
  verb cfg "AST retrieved successfully\n"
  runSuite cfg debug linkFiles [⟨path, prog, cases⟩]

private def readGroup (path : String) : Action Group := do
  let bytes ← readInput path
  let cases ← parseAssertions bytes
  match Parser.toplevel_entities bytes path.toUTF8 with
  | .ok (prog, _) => return ⟨path, prog, cases⟩
  | .error e => match e.kind with
    | .invalidAnonymousId m => fail m
    | .zeroWidthAssertion => throw (.exception (e.message .toplevel_entities))
    | _ => throw (.failure (s!"Error in file {path}: ".toUTF8 ++ e.message .toplevel_entities))

def testDir (cfg : Config) (debug : Bool) (linkFiles : List Driver.Program) (path : String) :
    Action UInt32 := do
  let out ← IO.getStdout
  IO.println s!"===> TESTING ASSERTIONS IN: {path}"
  let mut groups := []
  for file in ← llFiles cfg path ["perf"] do
    let (_, ext) ← basenameExt file
    unless ext == "ll" do continue
    try groups := (← readGroup file) :: groups
    catch e =>
      let detail := match e with
        | .failure m => "\n\t".toUTF8 ++ m
        | _ => .empty
      out.write ((s!"FAILURE {file}".toUTF8 ++ detail).push 10)
      out.flush
  runSuite cfg debug linkFiles groups.reverse

end Vellvm.CLI
