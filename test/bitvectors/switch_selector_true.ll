; The selector has one reachable value only.  Losing it at the switch edge
; would spuriously make the failing default branch reachable.

declare void @__assert_fail()

define i32 @main() {
entry:
  br label %dispatch

dispatch:
  switch i32 0, label %failure [
    i32 0, label %success
  ]

success:
  ret i32 0

failure:
  call void @__assert_fail()
  unreachable
}
