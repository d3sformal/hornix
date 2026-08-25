; The first iteration is safe, but the cyclic PHI update makes the second
; iteration fail.  The old and new values of %a must be distinct on the
; back-edge transition.

declare void @__assert_fail()

define void @check(i1 %condition) {
entry:
  br i1 %condition, label %ok, label %failure

ok:
  ret void

failure:
  call void @__assert_fail()
  unreachable
}

define i32 @main() {
entry:
  br label %loop

loop:
  %a = phi i1 [ false, %entry ], [ %next_a, %loop ]
  %b = phi i1 [ false, %entry ], [ %a, %loop ]
  %equal = icmp eq i1 %a, %b
  call void @check(i1 %equal)
  %next_a = xor i1 %b, true
  br label %loop
}
