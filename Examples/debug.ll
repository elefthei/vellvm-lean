define i32 @twice(i32 %x) {
  %z = add i32 %x, %x
  ret i32 %z
}
define i32 @main(i32 %argc, ptr %argv) {
  %v = call i32 @twice(i32 7)
  ret i32 %v
}
