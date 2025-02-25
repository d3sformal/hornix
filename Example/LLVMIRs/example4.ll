; ModuleID = 'LLVMIRs/example4.ll'
source_filename = "example4.cpp"
target datalayout = "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-windows-msvc19.38.33134"

$"??_C@_1BK@EIOCNNHA@?$AAe?$AAx?$AAa?$AAm?$AAp?$AAl?$AAe?$AA4?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@" = comdat any

$"??_C@_1O@HADGPJAD@?$AAx?$AA?5?$AA?$DO?$AA?$DN?$AA?5?$AA0?$AA?$AA@" = comdat any

@"??_C@_1BK@EIOCNNHA@?$AAe?$AAx?$AAa?$AAm?$AAp?$AAl?$AAe?$AA4?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@" = linkonce_odr dso_local unnamed_addr constant [13 x i16] [i16 101, i16 120, i16 97, i16 109, i16 112, i16 108, i16 101, i16 52, i16 46, i16 99, i16 112, i16 112, i16 0], comdat, align 2
@"??_C@_1O@HADGPJAD@?$AAx?$AA?5?$AA?$DO?$AA?$DN?$AA?5?$AA0?$AA?$AA@" = linkonce_odr dso_local unnamed_addr constant [7 x i16] [i16 120, i16 32, i16 62, i16 61, i16 32, i16 48, i16 0], comdat, align 2

; Function Attrs: mustprogress noinline uwtable
define dso_local noundef i32 @"?bar@@YAHHH@Z"(i32 noundef %0, i32 noundef %1) #0 {
  %3 = sub nsw i32 %0, %1
  %4 = icmp sge i32 %0, 0
  br i1 %4, label %6, label %5

5:                                                ; preds = %2
  call void @_wassert(ptr noundef @"??_C@_1O@HADGPJAD@?$AAx?$AA?5?$AA?$DO?$AA?$DN?$AA?5?$AA0?$AA?$AA@", ptr noundef @"??_C@_1BK@EIOCNNHA@?$AAe?$AAx?$AAa?$AAm?$AAp?$AAl?$AAe?$AA4?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@", i32 noundef 5)
  br label %6

6:                                                ; preds = %5, %2
  ret i32 %3
}

declare dso_local void @_wassert(ptr noundef, ptr noundef, i32 noundef) #1

; Function Attrs: mustprogress noinline norecurse uwtable
define dso_local noundef i32 @main() #2 {
  %1 = call noundef i32 @"?bar@@YAHHH@Z"(i32 noundef 10, i32 noundef 1)
  ret i32 0
}

attributes #0 = { mustprogress noinline uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { mustprogress noinline norecurse uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 2}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{i32 1, !"MaxTLSAlign", i32 65536}
!4 = !{!"clang version 18.1.8 (https://github.com/llvm/llvm-project.git 4ec508cc867ae77acbb67775609d09e67e0fbb12)"}
