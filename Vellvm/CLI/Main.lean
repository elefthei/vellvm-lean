/-
 *                     Vellvm - the Verified LLVM project
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>
 *   Distributed under the GNU General Public License, version 3 or later.
-/
import Vellvm.CLI.Assertions
import Vellvm.CLI.Debugger

namespace Vellvm.CLI
open Frontend Platform Driver Semantics Semantics.DynamicValues

private def usage := "USAGE: ./vellvm [options] <files>\n\n" ++
  "  -test run comprehensive test suite\n\tequivalent to running:\n\t -test-pp-dir ../tests, then\n\t -test-dir ../tests\n" ++
  "  -test-file run the assertions in a given file\n" ++
  "  -test-dir run all .ll files in the given directory\n" ++
  "  -test-pp-file run the parsing/pretty-printing tests on the given .ll\n" ++
  "  -test-pp-dir run the parsing/pretty-printing tests on all .ll files in the given directory\n" ++
  "  -print-ast run the parsing on the given .ll file and write its internal ast representation to a .v.ast file in the output directory.\n" ++
  "  -args interpret the rest of the command line arguments as 'argv' for \n       EACH .ll file that vellvm interprets. Note that all strings after \n       -args will be interpreted as members of argv, and not arguments to vellvm.\n" ++
  "  -O transform the source\n" ++
  "  -emit-llvm save the resulting .ll as .v.ll in the output directory\n" ++
  "  -op set the path to the output files directory  [default='output']\n" ++
  "  -l link one .ll file\n" ++
  "  -L link all .ll files in the given directory\n" ++
  "  -interpret interpret ll program starting from 'main'\n" ++
  "  -i interpret ll program starting from 'main' (same as -interpret)\n" ++
  "  -debug enable debugging trace output\n" ++
  "  -debugger debug an ll program (use `h` at prompt to get help)\n" ++
  "  -v enables more verbose compilation output\n" ++
  "  -help  Display this list of options\n  --help  Display this list of options\n"

private def badArg (msg : String) : Action UInt32 := do
  (← IO.getStderr).write ((← argv0) ++ s!": {msg}.\n{usage}".toUTF8)
  return 2

private def processFile (cfg : Config) (optimize emit : Bool) (path : String) : Action Program := do
  let (base, _) ← basenameExt path
  verb cfg s!"* processing file: {path}\n"
  let (prog, _) ← parseFile path
  -- The reference's transform is identity, but its verbose action is observable.
  if optimize then verb cfg s!" - optimizing file: {path}\n"
  if emit then
    let dest ← genName cfg base ".v.ll"
    verb cfg s!" - emitting   file: {dest}\n"
    outputFile dest prog
  return prog

private def linkFile (cfg : Config) (path : String) : Action Program := do
  verb cfg s!"* linking file: {path}"
  return (← parseFile path).1

private def finish : Result → Action UInt32
  | .error e => throw (.failure e.describe)
  | .ok v => do
    (← IO.getStdout).write (("Program terminated with: ".toUTF8 ++ @show_dvalue P v).push 10)
    return 0

def vellvm (argv : List String) : Action UInt32 := do
  let mut cfg : Config := {}
  configure cfg
  IO.println "(* -------- Vellvm Test Harness -------- *)"
  (← IO.getStdout).flush
  let mut links : List Program := []
  let mut interpret := false
  let mut interactive := false
  let mut debug := false
  let mut optimize := false
  let mut emit := false
  let mut programArgs : List IRString := ["todo".toUTF8]
  let mut args := argv
  repeat
    let flag :: rest := args | break
    args := rest
    unless flag.startsWith "-" do
      links := (← processFile cfg optimize emit flag) :: links
      continue
    if flag == "-help" || flag == "--help" then IO.print usage; return 0
    let parts := flag.splitOn "="
    let key := parts.head!
    let value := if parts.tail!.isEmpty then none else some ("=".intercalate parts.tail!)
    match key with
    | "-test" | "-args" | "-O" | "-emit-llvm" | "-interpret" | "-i" | "-debug" | "-debugger" | "-v" =>
      if let some arg := value then
        return ← badArg s!"wrong argument '{arg}'; option '{flag}' expects no argument"
      match key with
      | "-test" =>
        IO.println "============== RUNNING TEST SUITE =============="
        let pp ← testPPDir cfg "../tests"
        let assertions ← testDir cfg debug links "../tests"
        return if pp == 0 && assertions == 0 then 0 else 1
      | "-args" => programArgs := args.map String.toUTF8; break
      | "-O" => optimize := true
      | "-emit-llvm" => emit := true
      | "-interpret" | "-i" => interpret := true
      | "-debug" => debug := true
      | "-debugger" => interactive := true
      | _ => cfg := { cfg with verbose := true }
    | "-op" | "-l" | "-L" | "-print-ast" | "-test-file" | "-test-dir" | "-test-pp-file" | "-test-pp-dir" =>
      let some arg := value <|> args.head? | return ← badArg s!"option '{flag}' needs an argument"
      if value.isNone then args := args.drop 1
      match key with
      | "-op" => cfg := { cfg with output := arg }
      | "-l" => links := (← linkFile cfg arg) :: links
      | "-L" => for path in ← llFiles cfg arg do links := (← linkFile cfg path) :: links
      | "-print-ast" => astFile cfg arg false
      | "-test-file" => return ← testFile cfg debug links arg
      | "-test-dir" => return ← testDir cfg debug links arg
      | "-test-pp-file" => parsePPTest cfg arg
      | _ => return ← testPPDir cfg arg
    | _ => return ← badArg s!"unknown option '{flag}'"
  if !interpret && !interactive then return 0
  let prog := TopLevel.link_all links []
  if interpret then finish (← withMain programArgs prog (fun cur ↦ cur.run debug))
  else finish (← debugger programArgs prog)

end Vellvm.CLI
