define i8 @frozen() {
entry:
  %x = freeze i8 poison
  ret i8 %x
}

define i8 @reused() {
entry:
  %x = freeze i8 poison
  %diff = sub i8 %x, %x
  ret i8 %diff
}
