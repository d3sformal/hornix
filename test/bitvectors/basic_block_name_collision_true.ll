define void @bar() {
entry:
  ret void
}

define void @foo() {
entry:
  br label %block2
block2:
  br label %block3
block3:
  br label %block4
block4:
  br label %block5
block5:
  br label %block6
block6:
  br label %block7
block7:
  br label %block8
block8:
  br label %block9
block9:
  br label %block10
block10:
  br label %block11
block11:
  br label %block12
block12:
  call void @bar()
  ret void
}

define void @foo1() {
entry:
  br label %block2
block2:
  ret void
}

define i32 @main() {
entry:
  call void @foo()
  call void @foo1()
  ret i32 0
}
