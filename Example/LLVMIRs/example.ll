; ModuleID = 'LLVMIRs/example.ll'
source_filename = "example.cpp"
target datalayout = "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-windows-msvc19.38.33134"

$"??_C@_1BI@MGCDFEKO@?$AAe?$AAx?$AAa?$AAm?$AAp?$AAl?$AAe?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@" = comdat any

$"??_C@_1M@GIONGGCF@?$AAx?$AA?5?$AA?$DO?$AA?5?$AAy?$AA?$AA@" = comdat any

@"??_C@_1BI@MGCDFEKO@?$AAe?$AAx?$AAa?$AAm?$AAp?$AAl?$AAe?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@" = linkonce_odr dso_local unnamed_addr constant [12 x i16] [i16 101, i16 120, i16 97, i16 109, i16 112, i16 108, i16 101, i16 46, i16 99, i16 112, i16 112, i16 0], comdat, align 2
@"??_C@_1M@GIONGGCF@?$AAx?$AA?5?$AA?$DO?$AA?5?$AAy?$AA?$AA@" = linkonce_odr dso_local unnamed_addr constant [6 x i16] [i16 120, i16 32, i16 62, i16 32, i16 121, i16 0], comdat, align 2

; Function Attrs: mustprogress noinline uwtable
define dso_local void @"?fun@@YAXXZ"() #0 {
  br label %1

1:                                                ; preds = %3, %0
  %.01 = phi i32 [ 0, %0 ], [ %5, %3 ]
  %.0 = phi i32 [ 1, %0 ], [ %4, %3 ]
  %2 = icmp slt i32 %.01, 10
  br i1 %2, label %3, label %6

3:                                                ; preds = %1
  %4 = add nsw i32 %.0, %.01
  %5 = add nsw i32 %.01, 1
  br label %1, !llvm.loop !5

6:                                                ; preds = %1
  %7 = icmp sgt i32 %.0, %.01
  br i1 %7, label %9, label %8

8:                                                ; preds = %6
  call void @_wassert(ptr noundef @"??_C@_1M@GIONGGCF@?$AAx?$AA?5?$AA?$DO?$AA?5?$AAy?$AA?$AA@", ptr noundef @"??_C@_1BI@MGCDFEKO@?$AAe?$AAx?$AAa?$AAm?$AAp?$AAl?$AAe?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@", i32 noundef 33)
  br label %9

9:                                                ; preds = %8, %6
  %10 = phi i1 [ true, %6 ], [ false, %8 ]
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
!5 = distinct !{!5, !6}
!6 = !{!"llvm.loop.mustprogress"}
