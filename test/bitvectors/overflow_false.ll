; The assertion is false for x = 255 only when i8 addition has LLVM's
; modular semantics.  The legacy Int encoding considers it true for all x.

declare void @__assert_fail()
declare i8 @nondet_i8()

define i32 @main() {
entry:
  %x = call i8 @nondet_i8()
  %wrapped = add i8 %x, 1
  %incorrect = icmp ugt i8 %wrapped, %x
  br i1 %incorrect, label %safe, label %error

safe:
  ret i32 0

error:
  call void @__assert_fail()
  unreachable
}
