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

public import Init.System.IO
import Std

public section
namespace Vellvm.Frontend.Platform
open System

structure Config where
  output : String := "output"
  verbose : Bool := false

/-- The OCaml `%S` spelling used by uncaught exceptions, even for non-UTF-8 LLVM tokens. -/
def quote (s : ByteArray) : ByteArray := Id.run do
  let mut out := "\"".toUTF8
  for c in s do
    out := match c.toNat with
      | 8 => out ++ "\\b".toUTF8
      | 9 => out ++ "\\t".toUTF8
      | 10 => out ++ "\\n".toUTF8
      | 13 => out ++ "\\r".toUTF8
      | 34 => out ++ "\\\"".toUTF8
      | 92 => out ++ "\\\\".toUTF8
      | n => if 32 ≤ n && n < 127 then out.push c else
          (((out.push 92).push (48 + n / 100).toUInt8).push (48 + n / 10 % 10).toUInt8).push
            (48 + n % 10).toUInt8
  return out.push 34

inductive Error where
  | failure (message : ByteArray)
  | exception (description : ByteArray)
  deriving Inhabited

def Error.describe : Error → ByteArray
  | .failure m => "Failure(".toUTF8 ++ quote m ++ ")".toUTF8
  | .exception d => d

abbrev Action := EIO Error

def sysError (e : IO.Error) : Error :=
  let msg := match e with
    | .noFileOrDirectory f .. => f ++ ": No such file or directory"
    | .permissionDenied (some f) .. => f ++ ": Permission denied"
    | .inappropriateType (some f) 21 _ => f ++ ": Is a directory"
    | .inappropriateType (some f) 20 _ => f ++ ": Not a directory"
    | _ => toString e
  .exception ("Sys_error(".toUTF8 ++ quote msg.toUTF8 ++ ")".toUTF8)

instance : MonadLift IO Action := ⟨IO.toEIO sysError⟩

def fail (s : String) : Action α := throw (.failure s.toUTF8)

def run (act : Action UInt32) : IO UInt32 := do
  match ← act.toBaseIO with
  | .ok status => return status
  | .error e =>
    (← IO.getStderr).write ("Fatal error: exception ".toUTF8 ++ e.describe ++ "\n".toUTF8)
    return 2

def verb (cfg : Config) (s : String) : IO Unit := if cfg.verbose then IO.print s else pure ()

def configure (cfg : Config) : Action Unit := do
  if System.Platform.isWindows then fail "Windows not supported"
  -- The source defaults its `linux` configuration switch to false, including on Unix hosts.
  verb cfg "platform = OS X\n"
  match ← (FilePath.mk cfg.output).metadata.toBaseIO with
  | .ok _ => return ()
  | .error (.noFileOrDirectory ..) =>
    verb cfg s!"creating output directory: {cfg.output}\n"
    IO.FS.createDir cfg.output
  | .error e => throw (sysError e)

/-- Like Str.split with a one-character delimiter: drop one empty edge field at each end. -/
private def fields (s sep : String) : List String :=
  if s.isEmpty then [] else
    let xs := s.splitOn sep
    let xs := if s.startsWith sep then xs.drop 1 else xs
    if s.endsWith sep then xs.dropLast else xs

def basenameExt (path : String) : Action (String × String) := do
  let some name := (fields path "/").getLast? | fail s!"bad path: {path}"
  match (fields name ".").reverse with
  | [] => fail s!"no filename found: {name}"
  | [root] => return (root, "")
  | ext :: parts => return (String.join parts.reverse, ext)

/-- `.writeNew` at the actual output site also protects against concurrent creation. -/
def genName (cfg : Config) (base ext : String) : IO String := do
  let mut n := 0
  repeat
    let suffix := if n == 0 then "" else "_" ++ toString n
    let path := cfg.output ++ "/" ++ base ++ suffix ++ ext
    match ← (FilePath.mk path).symlinkMetadata.toBaseIO with
    | .error (.noFileOrDirectory ..) => return path
    | .error e => throw e
    | .ok _ => n := n+1

/-- OCaml `input_line` followed by `String.concat "\n"` drops only a final LF, not CR. -/
def readInput (path : String) : IO ByteArray := do
  let b ← IO.FS.readBinFile path
  return if b[b.size - 1]? == some 10 then b.extract 0 (b.size - 1) else b

/-- `IO.appPath` resolves symlinks; Arg reports the invocation's argv[0] instead. -/
def argv0 : IO ByteArray := do
  if System.Platform.isLinux then
    if let .ok args ← (IO.FS.readBinFile "/proc/self/cmdline").toBaseIO then
      if let some endPos := args.findIdx? (· == 0) then return args.extract 0 endPos
  return (← IO.appPath).toString.toUTF8

private partial def findLL (path : FilePath) (failed : IO.Ref Bool) (acc : List String) :
    IO (List String) := do
  let mut acc := acc
  try
    let m ← path.symlinkMetadata
    if path.toString.endsWith ".ll" then acc := path.toString :: acc
    if m.type == .dir then
      for d in ← path.readDir do acc ← findLL d.path failed acc
  catch e =>
    failed.set true
    match e with
    | .noFileOrDirectory p .. => IO.eprintln s!"find: '{p}': No such file or directory"
    | .permissionDenied (some p) .. => IO.eprintln s!"find: '{p}': Permission denied"
    | _ => IO.eprintln s!"find: {e}"
  return acc

private def platformError (cmd : String) (code : Nat) : Error :=
  .exception ("VellvmLib.Platform.PlatformError(".toUTF8 ++ quote cmd.toUTF8 ++ ", ".toUTF8 ++
    quote s!"Exited with status {code}.".toUTF8 ++ ")".toUTF8)

/-- Preserve `find` order reversed by the source's cons loop. No filename is shell input. -/
def llFiles (cfg : Config) (dir : String) (excluding : List String := []) : Action (List String) := do
  let tmp ← genName cfg ".ll_files" ".tmp"
  let cmd := s!"find {dir} -name \"*.ll\" -print > {tmp}"
  verb cfg s!"* {cmd}\n"
  -- Even immediate `-test` actions require an already configured, writable output directory.
  let listing ← match ← (IO.FS.Handle.mk tmp .writeNew).toBaseIO with
  | .error e =>
    let reason := match e with
      | .noFileOrDirectory .. => "Directory nonexistent"
      | .permissionDenied .. => "Permission denied"
      | _ => toString e
    IO.eprintln s!"/bin/sh: 1: cannot create {tmp}: {reason}"
    throw (platformError cmd 2)
  | .ok h => pure h
  let failed ← IO.mkRef false
  let files ← findLL dir failed []
  if ← failed.get then
    -- `sh ... raise_error` leaves the partial directory listing behind on failure.
    for file in files.reverse do listing.putStrLn file
    throw (platformError cmd 1)
  verb cfg s!"* rm -f {tmp}\n"
  IO.FS.removeFile tmp
  if excluding.isEmpty then return files
  return files.filter fun p ↦ !(p.splitOn "/").any excluding.contains

/-- Guard a path against both option parsing and Clang's `@response-file` expansion. -/
private def clangPath (s : String) : String :=
  if s.startsWith "-" || s.startsWith "@" then "./" ++ s else s

def clangParse (cfg : Config) (input output : String) : IO Bool := do
  let args := #["-S", "-emit-llvm", "-w", "-O0", "-fno-asynchronous-unwind-tables", "-mstackrealign",
    "-o", clangPath output, clangPath input]
  verb cfg ("* clang " ++ String.intercalate " " args.toList ++ "\n")
  let err := if cfg.verbose then IO.Process.Stdio.inherit else .null
  try
    let child ← IO.Process.spawn { cmd := "clang", args, stderr := err }
    return (← child.wait) == 0
  catch e =>
    match e with
    | .noFileOrDirectory .. =>
      if cfg.verbose then IO.eprintln "/bin/sh: 1: clang: not found"
      return false
    | _ => throw e

end Vellvm.Frontend.Platform
