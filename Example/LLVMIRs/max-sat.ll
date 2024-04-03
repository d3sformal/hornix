; ModuleID = 'max-sat.ll'
source_filename = "../max-sat.cpp"
target datalayout = "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-windows-msvc19.38.33134"

$"??_C@_1BO@HHHAEIJH@?$AA?4?$AA?4?$AA?1?$AAm?$AAa?$AAx?$AA?9?$AAs?$AAa?$AAt?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@" = comdat any

$"??_C@_1CC@KBGACFEO@?$AAc?$AA?5?$AA?$DO?$AA?$DN?$AA?5?$AAa?$AA?5?$AA?$CG?$AA?$CG?$AA?5?$AAc?$AA?5?$AA?$DO?$AA?$DN?$AA?5?$AAb?$AA?$AA@" = comdat any

@"??_C@_1BO@HHHAEIJH@?$AA?4?$AA?4?$AA?1?$AAm?$AAa?$AAx?$AA?9?$AAs?$AAa?$AAt?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@" = linkonce_odr dso_local unnamed_addr constant [15 x i16] [i16 46, i16 46, i16 47, i16 109, i16 97, i16 120, i16 45, i16 115, i16 97, i16 116, i16 46, i16 99, i16 112, i16 112, i16 0], comdat, align 2
@"??_C@_1CC@KBGACFEO@?$AAc?$AA?5?$AA?$DO?$AA?$DN?$AA?5?$AAa?$AA?5?$AA?$CG?$AA?$CG?$AA?5?$AAc?$AA?5?$AA?$DO?$AA?$DN?$AA?5?$AAb?$AA?$AA@" = linkonce_odr dso_local unnamed_addr constant [17 x i16] [i16 99, i16 32, i16 62, i16 61, i16 32, i16 97, i16 32, i16 38, i16 38, i16 32, i16 99, i16 32, i16 62, i16 61, i16 32, i16 98, i16 0], comdat, align 2

; Function Attrs: mustprogress noinline uwtable
define dso_local void @"?max@@YAXHH@Z"(i32 noundef %0, i32 noundef %1) #0 {
  %3 = icmp sgt i32 %0, %1
  br i1 %3, label %4, label %5

4:                                                ; preds = %2
  br label %6

5:                                                ; preds = %2
  br label %6

6:                                                ; preds = %5, %4
  %.0 = phi i32 [ %0, %4 ], [ %1, %5 ]
  %7 = icmp sge i32 %.0, %0
  br i1 %7, label %8, label %10

8:                                                ; preds = %6
  %9 = icmp sge i32 %.0, %1
  br i1 %9, label %11, label %10

10:                                               ; preds = %8, %6
  call void @_wassert(ptr noundef @"??_C@_1CC@KBGACFEO@?$AAc?$AA?5?$AA?$DO?$AA?$DN?$AA?5?$AAa?$AA?5?$AA?$CG?$AA?$CG?$AA?5?$AAc?$AA?5?$AA?$DO?$AA?$DN?$AA?5?$AAb?$AA?$AA@", ptr noundef @"??_C@_1BO@HHHAEIJH@?$AA?4?$AA?4?$AA?1?$AAm?$AAa?$AAx?$AA?9?$AAs?$AAa?$AAt?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@", i32 noundef 11)
  br label %11

11:                                               ; preds = %10, %8
  %12 = phi i1 [ true, %8 ], [ false, %10 ]
  ret void
}

declare dso_local void @_wassert(ptr noundef, ptr noundef, i32 noundef) #1

attributes #0 = { mustprogress noinline uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 2}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{i32 1, !"MaxTLSAlign", i32 65536}
!4 = !{!"clang version 17.0.1"}
