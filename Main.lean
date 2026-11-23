import Vellvm.CLI.Main

def main (args : List String) : IO UInt32 :=
  Vellvm.Frontend.Platform.run (Vellvm.CLI.vellvm args)
