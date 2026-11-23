module

@[expose] public section
namespace Vellvm

/-- Rocq strings are sequences of bytes, not necessarily UTF-8. -/
abbrev IRString := ByteArray

/-- Rocq `positive`, including nonstandard LLVM integer widths. -/
abbrev Positive := { n : Nat // 0 < n }

end Vellvm
