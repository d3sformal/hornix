; ModuleID = 'example.cpp'
source_filename = "example.cpp"
target datalayout = "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-windows-msvc19.38.33134"

$"??_C@_1BI@MGCDFEKO@?$AAe?$AAx?$AAa?$AAm?$AAp?$AAl?$AAe?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@" = comdat any

$"??_C@_1CC@KBGACFEO@?$AAc?$AA?5?$AA?$DO?$AA?$DN?$AA?5?$AAa?$AA?5?$AA?$CG?$AA?$CG?$AA?5?$AAc?$AA?5?$AA?$DO?$AA?$DN?$AA?5?$AAb?$AA?$AA@" = comdat any

@"??_C@_1BI@MGCDFEKO@?$AAe?$AAx?$AAa?$AAm?$AAp?$AAl?$AAe?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@" = linkonce_odr dso_local unnamed_addr constant [12 x i16] [i16 101, i16 120, i16 97, i16 109, i16 112, i16 108, i16 101, i16 46, i16 99, i16 112, i16 112, i16 0], comdat, align 2
@"??_C@_1CC@KBGACFEO@?$AAc?$AA?5?$AA?$DO?$AA?$DN?$AA?5?$AAa?$AA?5?$AA?$CG?$AA?$CG?$AA?5?$AAc?$AA?5?$AA?$DO?$AA?$DN?$AA?5?$AAb?$AA?$AA@" = linkonce_odr dso_local unnamed_addr constant [17 x i16] [i16 99, i16 32, i16 62, i16 61, i16 32, i16 97, i16 32, i16 38, i16 38, i16 32, i16 99, i16 32, i16 62, i16 61, i16 32, i16 98, i16 0], comdat, align 2

; Function Attrs: mustprogress noinline uwtable
define dso_local noundef i32 @"?max@@YAHHH@Z"(i32 noundef %0, i32 noundef %1) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  store i32 %1, ptr %3, align 4
  store i32 %0, ptr %4, align 4
  %6 = load i32, ptr %4, align 4
  %7 = load i32, ptr %3, align 4
  %8 = icmp sgt i32 %6, %7
  br i1 %8, label %9, label %11

9:                                                ; preds = %2
  %10 = load i32, ptr %4, align 4
  store i32 %10, ptr %5, align 4
  br label %13

11:                                               ; preds = %2
  %12 = load i32, ptr %3, align 4
  store i32 %12, ptr %5, align 4
  br label %13

13:                                               ; preds = %11, %9
  %14 = load i32, ptr %5, align 4
  %15 = load i32, ptr %4, align 4
  %16 = icmp sge i32 %14, %15
  br i1 %16, label %17, label %21

17:                                               ; preds = %13
  %18 = load i32, ptr %5, align 4
  %19 = load i32, ptr %3, align 4
  %20 = icmp sge i32 %18, %19
  br i1 %20, label %22, label %21

21:                                               ; preds = %17, %13
  call void @_wassert(ptr noundef @"??_C@_1CC@KBGACFEO@?$AAc?$AA?5?$AA?$DO?$AA?$DN?$AA?5?$AAa?$AA?5?$AA?$CG?$AA?$CG?$AA?5?$AAc?$AA?5?$AA?$DO?$AA?$DN?$AA?5?$AAb?$AA?$AA@", ptr noundef @"??_C@_1BI@MGCDFEKO@?$AAe?$AAx?$AAa?$AAm?$AAp?$AAl?$AAe?$AA?4?$AAc?$AAp?$AAp?$AA?$AA@", i32 noundef 11)
  br label %22

22:                                               ; preds = %21, %17
  %23 = phi i1 [ true, %17 ], [ false, %21 ]
  %24 = load i32, ptr %5, align 4
  ret i32 %24
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
