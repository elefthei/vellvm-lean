/-
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
-/
import Vellvm.Frontend.Driver

def main (args : List String) : IO UInt32 :=
  Vellvm.Frontend.Platform.run (Vellvm.Frontend.Driver.frontend args)
