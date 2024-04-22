; ModuleID = 'LLVMIRs/fun-call.ll'
source_filename = "fun-call.cpp"
target datalayout = "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-windows-msvc19.38.33134"

$"??_C@_1BK@DALHFPIJ@?$AAf?$AAu?$AAn?$AA?9?$AAc?$AAa?$AAl?$AAl?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@" = comdat any

$"??_C@_1O@OLFJOGEJ@?$AAa?$AA?5?$AA?$DN?$AA?$DN?$AA?5?$AA1?$AA?$AA@" = comdat any

$"??_C@_1O@LCFDJMEO@?$AAb?$AA?5?$AA?$DN?$AA?$DN?$AA?5?$AA7?$AA?$AA@" = comdat any

@"??_C@_1BK@DALHFPIJ@?$AAf?$AAu?$AAn?$AA?9?$AAc?$AAa?$AAl?$AAl?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@" = linkonce_odr dso_local unnamed_addr constant [13 x i16] [i16 102, i16 117, i16 110, i16 45, i16 99, i16 97, i16 108, i16 108, i16 46, i16 99, i16 112, i16 112, i16 0], comdat, align 2
@"??_C@_1O@OLFJOGEJ@?$AAa?$AA?5?$AA?$DN?$AA?$DN?$AA?5?$AA1?$AA?$AA@" = linkonce_odr dso_local unnamed_addr constant [7 x i16] [i16 97, i16 32, i16 61, i16 61, i16 32, i16 49, i16 0], comdat, align 2
@"??_C@_1O@LCFDJMEO@?$AAb?$AA?5?$AA?$DN?$AA?$DN?$AA?5?$AA7?$AA?$AA@" = linkonce_odr dso_local unnamed_addr constant [7 x i16] [i16 98, i16 32, i16 61, i16 61, i16 32, i16 55, i16 0], comdat, align 2

; Function Attrs: mustprogress noinline norecurse uwtable
define dso_local noundef i32 @main() #0 {
  %1 = call noundef i32 @"?inc@@YAHH@Z"(i32 noundef 0)
  %2 = add nsw i32 %1, 2
  %3 = add nsw i32 %2, 3
  %4 = icmp eq i32 %1, 1
  br i1 %4, label %6, label %5

5:                                                ; preds = %0
  call void @_wassert(ptr noundef @"??_C@_1O@OLFJOGEJ@?$AAa?$AA?5?$AA?$DN?$AA?$DN?$AA?5?$AA1?$AA?$AA@", ptr noundef @"??_C@_1BK@DALHFPIJ@?$AAf?$AAu?$AAn?$AA?9?$AAc?$AAa?$AAl?$AAl?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@", i32 noundef 11)
  br label %6

6:                                                ; preds = %5, %0
  %7 = phi i1 [ true, %0 ], [ false, %5 ]
  %8 = icmp eq i32 %3, 7
  br i1 %8, label %10, label %9

9:                                                ; preds = %6
  call void @_wassert(ptr noundef @"??_C@_1O@LCFDJMEO@?$AAb?$AA?5?$AA?$DN?$AA?$DN?$AA?5?$AA7?$AA?$AA@", ptr noundef @"??_C@_1BK@DALHFPIJ@?$AAf?$AAu?$AAn?$AA?9?$AAc?$AAa?$AAl?$AAl?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@", i32 noundef 13)
  br label %10

10:                                               ; preds = %9, %6
  %11 = phi i1 [ true, %6 ], [ false, %9 ]
  ret i32 0
}

declare dso_local noundef i32 @"?inc@@YAHH@Z"(i32 noundef) #1

declare dso_local void @_wassert(ptr noundef, ptr noundef, i32 noundef) #1

attributes #0 = { mustprogress noinline norecurse uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 2}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{i32 1, !"MaxTLSAlign", i32 65536}
!4 = !{!"clang version 17.0.1"}
