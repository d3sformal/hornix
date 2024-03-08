; ModuleID = 'example.cpp'
source_filename = "example.cpp"
target datalayout = "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-windows-msvc19.38.33134"

$"??_C@_1BI@MGCDFEKO@?$AAe?$AAx?$AAa?$AAm?$AAp?$AAl?$AAe?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@" = comdat any

$"??_C@_1M@GIONGGCF@?$AAx?$AA?5?$AA?$DO?$AA?5?$AAy?$AA?$AA@" = comdat any

@"??_C@_1BI@MGCDFEKO@?$AAe?$AAx?$AAa?$AAm?$AAp?$AAl?$AAe?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@" = linkonce_odr dso_local unnamed_addr constant [12 x i16] [i16 101, i16 120, i16 97, i16 109, i16 112, i16 108, i16 101, i16 46, i16 99, i16 112, i16 112, i16 0], comdat, align 2
@"??_C@_1M@GIONGGCF@?$AAx?$AA?5?$AA?$DO?$AA?5?$AAy?$AA?$AA@" = linkonce_odr dso_local unnamed_addr constant [6 x i16] [i16 120, i16 32, i16 62, i16 32, i16 121, i16 0], comdat, align 2

; Function Attrs: mustprogress noinline uwtable
define dso_local void @"?fun@@YAXXZ"() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 1, ptr %1, align 4
  store i32 0, ptr %2, align 4
  br label %3

3:                                                ; preds = %6, %0
  %4 = load i32, ptr %2, align 4
  %5 = icmp slt i32 %4, 10
  br i1 %5, label %6, label %12

6:                                                ; preds = %3
  %7 = load i32, ptr %1, align 4
  %8 = load i32, ptr %2, align 4
  %9 = add nsw i32 %7, %8
  store i32 %9, ptr %1, align 4
  %10 = load i32, ptr %2, align 4
  %11 = add nsw i32 %10, 1
  store i32 %11, ptr %2, align 4
  br label %3, !llvm.loop !5

12:                                               ; preds = %3
  %13 = load i32, ptr %1, align 4
  %14 = load i32, ptr %2, align 4
  %15 = icmp sgt i32 %13, %14
  br i1 %15, label %17, label %16

16:                                               ; preds = %12
  call void @_wassert(ptr noundef @"??_C@_1M@GIONGGCF@?$AAx?$AA?5?$AA?$DO?$AA?5?$AAy?$AA?$AA@", ptr noundef @"??_C@_1BI@MGCDFEKO@?$AAe?$AAx?$AAa?$AAm?$AAp?$AAl?$AAe?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@", i32 noundef 34)
  br label %17

17:                                               ; preds = %16, %12
  %18 = phi i1 [ true, %12 ], [ false, %16 ]
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
