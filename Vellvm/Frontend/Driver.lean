/-
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
-/
module

public import Vellvm.Frontend.Platform
public import Vellvm.Frontend.Parser
import Vellvm.Syntax.ReprAST

public section
namespace Vellvm.Frontend.Driver
open Vellvm.Syntax Platform

abbrev Program := List Parser.Entity

def parseFile (path : String) : Action (Program × Histogram) := do
  let bytes ← readInput path
  match Parser.toplevel_entities bytes path.toUTF8 with
  | .ok parsed => return parsed
  | .error e =>
    match e.kind with
    | .invalidAnonymousId msg =>
      throw (.exception ("Parse_util.InvalidAnonymousId(".toUTF8 ++ quote msg.toUTF8 ++ ")".toUTF8))
    | .zeroWidthAssertion =>
      throw (.exception "File \"ml/libvellvm/Camlcoq.ml\", line 73, characters 20-26: Assertion failed".toUTF8)
    | _ => throw (.failure (s!"Error in file {path}: ".toUTF8 ++ e.message .toplevel_entities))

/-- The source closes each channel without flushing its Format formatter. Its initial box only
emits once at least 78 bytes of *text* have accumulated; forced newlines have zero width. -/
private def formatReady (textBytes : Nat) : Bool := textBytes >= 78

example : !formatReady 77 && formatReady 78 := by decide

def outputFile (path : String) (prog : Program) : IO Unit := do
  let h ← IO.FS.Handle.mk path .writeNew
  let text := ShowAST.showProg prog
  if formatReady text.size then h.write text

private def llBasename (cfg : Config) (path : String) : Action String := do
  verb cfg s!"* processing file: {path}\n"
  let (name, ext) ← basenameExt path
  unless ext == "ll" do fail s!"found unsupported file type: {path}"
  return name

private def histogramFile (cfg : Config) (path : String) : Action Unit := do
  let base ← llBasename cfg path
  let (_, hist) ← parseFile path
  let h ← IO.FS.Handle.mk (← genName cfg base ".hist") .writeNew
  let text := (histogramText hist).toUTF8
  if formatReady text.size then h.write (text.push 10)

/-- Before the box opens, retain at most one margin of bytes. After it opens, stream each TLE. -/
private def astChunk (h : IO.FS.Handle) (pending : Option ByteArray) (newlines : Nat)
    (chunk : ByteArray) : IO (Option ByteArray) := do
  if let some prefixBytes := pending then
    unless formatReady (prefixBytes.size + chunk.size - newlines) do return some (prefixBytes ++ chunk)
    h.write prefixBytes
  h.write chunk
  return none

/-- `frontend -print-ast` writes both printers; `vellvm -print-ast` uses only the internal list. -/
def astFile (cfg : Config) (path : String) (withLLVM : Bool) : Action Unit := do
  let base ← llBasename cfg path
  let (prog, _) ← parseFile path
  let out ← genName cfg base ".v.ast"
  if withLLVM then outputFile out prog
  let h ← IO.FS.Handle.mk out (if withLLVM then .append else .writeNew)
  let mut pending := some (if withLLVM then
    "\n\nInternal Coq representation of the ast:\n\n[".toUTF8 else "[".toUTF8)
  let newlines := if withLLVM then 4 else 0
  let mut first := true
  for tle in prog do
    unless first do pending ← astChunk h pending newlines ";".toUTF8
    first := false
    pending ← astChunk h pending newlines (ReprAST.repr_tle tle)
  discard <| astChunk h pending newlines "]".toUTF8

/-- The first Clang rejection skips the test; rejection of the printed program fails it. -/
def parsePPTest (cfg : Config) (path : String) : Action Unit := do
  verb cfg s!"* processing file: {path}\n"
  let (name, _) ← basenameExt path
  let vll ← genName cfg name ".v.ll"
  let out ← genName cfg name ".out.ll"
  unless ← clangParse cfg path out do return ()
  let (prog, _) ← parseFile path
  outputFile vll prog
  unless ← clangParse cfg vll out do fail s!"vellvm output bad file: {vll}"

def testPPDir (cfg : Config) (dir : String) : Action UInt32 := do
  IO.println s!"===> RUNNING PRETTY PRINTING TESTS IN: {dir}"
  (← IO.getStdout).flush
  let files ← llFiles cfg dir ["perf"]
  let mut passed := 0
  let mut failed := 0
  let mut details := ByteArray.empty
  for file in files do
    try
      parsePPTest cfg file
      passed := passed + 1
      if cfg.verbose then details := details ++ s!" PASSED - {file}\n".toUTF8
    catch e =>
      let msg := match e with
        | .failure m => m
        | _ => "test threw exception: ".toUTF8 ++ e.describe
      failed := failed + 1
      details := details ++ s!" FAILED - {file}\n\t   ERROR: ".toUTF8 ++ msg ++ "\n".toUTF8
  let total := passed + failed
  if failed > 0 then
    IO.print s!"\nParsing files in: {dir}\n:"
    (← IO.getStdout).write details
  else if cfg.verbose then
    let result := if total == 0 then "NO ASSERT" else "PASSED"
    IO.print s!"\nParsing files in: {dir}\n: {result}"
  IO.print s!"\n(*-------------------------------------- *)\nPassed: {passed}/{total}\nFailed: {failed}/{total}\n\n"
  return if failed == 0 then 0 else 1

private def usage := "USAGE: ./vellvm [options] <files>\n\n" ++
  "  -set-test-dir set the path to the tests directory [default='../tests']\n" ++
  "  -test run comprehensive parsing test suite:\n\tequivalent to running with -test-pp-dir <test-dir> (default '../tests')\n" ++
  "  -test-pp-dir run the parsing/pretty-printing tests on all .ll files in the given directory\n" ++
  "  -test-pp run the parsing/pretty-printing tests on the provided .ll files (overrides histogram)\n" ++
  "  -print-ast run the parsing on the given .ll file and write its internal ast and domination tree to a .v.ast file in the output directory (see -op)\n" ++
  "  -histogram-only create only the .hist file for each of the .ll inputs\n" ++
  "  -print-ast-dir run the parsing on the given directory and write its internal ast and domination tree to a .v.ast file in the output directory (see -op)\n" ++
  "  -op set the path to the output files directory  [default='output']\n" ++
  "  -v enables more verbose compilation output\n" ++
  "  -help  Display this list of options\n  --help  Display this list of options\n"

private def badArg (msg : String) : Action UInt32 := do
  (← IO.getStderr).write ((← argv0) ++ s!": {msg}.\n{usage}".toUTF8)
  return 2

def frontend (argv : List String) : Action UInt32 := do
  IO.println "(* -------- Vellvm Test Harness -------- *)"
  (← IO.getStdout).flush
  let mut cfg : Config := {}
  let mut testDir := "../tests"
  let mut pp := false
  let mut hist := false
  let mut files := []
  let mut args := argv
  repeat
    let flag :: rest := args | break
    args := rest
    unless flag.startsWith "-" do
      files := flag :: files
      continue
    if flag == "-help" || flag == "--help" then IO.print usage; return 0
    let split := flag.splitOn "="
    let key := split.head!
    let inlineValue := if split.tail!.isEmpty then none else some ("=".intercalate split.tail!)
    match key with
    | "-v" | "-histogram-only" | "-test-pp" | "-test" =>
      if let some arg := inlineValue then
        return ← badArg s!"wrong argument '{arg}'; option '{flag}' expects no argument"
      match key with
      | "-v" => cfg := { cfg with verbose := true }
      | "-histogram-only" => hist := true
      | "-test-pp" => pp := true
      | _ =>
        IO.println "============== RUNNING TEST SUITE =============="
        return ← testPPDir cfg testDir
    | "-op" | "-set-test-dir" | "-print-ast" | "-print-ast-dir" | "-test-pp-dir" =>
      let some arg := inlineValue <|> args.head? | return ← badArg s!"option '{flag}' needs an argument"
      if inlineValue.isNone then args := args.drop 1
      match key with
      | "-op" => cfg := { cfg with output := arg }
      | "-set-test-dir" => testDir := arg
      | "-print-ast" => configure cfg; astFile cfg arg true
      | "-print-ast-dir" =>
        configure cfg
        for file in ← llFiles cfg arg do astFile cfg file true
      | _ => return ← testPPDir cfg arg
    | _ => return ← badArg s!"unknown option '{flag}'"
  configure cfg
  configure cfg
  for file in files do
    if pp then parsePPTest cfg file else if hist then histogramFile cfg file else astFile cfg file true
  return 0

end Vellvm.Frontend.Driver
