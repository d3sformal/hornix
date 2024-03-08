; ModuleID = 'example.cpp'
source_filename = "example.cpp"
target datalayout = "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-windows-msvc19.38.33134"

; Function Attrs: mustprogress noinline nounwind uwtable
define dso_local noundef i32 @"?max@@YAHHH@Z"(i32 noundef %0, i32 noundef %1) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  store i32 %1, ptr %4, align 4
  store i32 %0, ptr %5, align 4
  %6 = load i32, ptr %5, align 4
  %7 = load i32, ptr %4, align 4
  %8 = icmp sgt i32 %6, %7
  br i1 %8, label %9, label %11

9:                                                ; preds = %2
  %10 = load i32, ptr %5, align 4
  store i32 %10, ptr %3, align 4
  br label %13

11:                                               ; preds = %2
  %12 = load i32, ptr %4, align 4
  store i32 %12, ptr %3, align 4
  br label %13

13:                                               ; preds = %11, %9
  %14 = load i32, ptr %3, align 4
  ret i32 %14
}

; Function Attrs: mustprogress noinline nounwind uwtable
define dso_local noundef i32 @"?add@@YAHH@Z"(i32 noundef %0) #0 {
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
  %6 = load i32, ptr %2, align 4
  store i32 %6, ptr %3, align 4
  store i32 1, ptr %5, align 4
  br label %7

7:                                                ; preds = %15, %1
  %8 = load i32, ptr %5, align 4
  %9 = icmp slt i32 %8, 10
  br i1 %9, label %10, label %18

10:                                               ; preds = %7
  %11 = load i32, ptr %3, align 4
  %12 = load i32, ptr %5, align 4
  %13 = add nsw i32 %11, %12
  store i32 %13, ptr %4, align 4
  %14 = load i32, ptr %4, align 4
  store i32 %14, ptr %3, align 4
  br label %15

15:                                               ; preds = %10
  %16 = load i32, ptr %5, align 4
  %17 = add nsw i32 %16, 1
  store i32 %17, ptr %5, align 4
  br label %7, !llvm.loop !12

18:                                               ; preds = %7
  %19 = load i32, ptr %3, align 4
  ret i32 %19
}

; Function Attrs: mustprogress noinline norecurse nounwind uwtable
define dso_local noundef i32 @main(i32 noundef %0, ptr noundef %1) #1 {
  %3 = alloca i32, align 4
  %4 = alloca ptr, align 8
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  store i32 0, ptr %3, align 4
  store ptr %1, ptr %4, align 8
  store i32 %0, ptr %5, align 4
  store i32 1, ptr %6, align 4
  store i32 2, ptr %7, align 4
  ret i32 0
}

attributes #0 = { mustprogress noinline nounwind uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { mustprogress noinline norecurse nounwind uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.linker.options = !{!0, !1, !2, !3, !4, !5, !6}
!llvm.module.flags = !{!7, !8, !9, !10}
!llvm.ident = !{!11}

!0 = !{!"/FAILIFMISMATCH:\22_MSC_VER=1900\22"}
!1 = !{!"/FAILIFMISMATCH:\22_ITERATOR_DEBUG_LEVEL=0\22"}
!2 = !{!"/FAILIFMISMATCH:\22RuntimeLibrary=MT_StaticRelease\22"}
!3 = !{!"/DEFAULTLIB:libcpmt.lib"}
!4 = !{!"/FAILIFMISMATCH:\22_CRT_STDIO_ISO_WIDE_SPECIFIERS=0\22"}
!5 = !{!"/FAILIFMISMATCH:\22annotate_string=0\22"}
!6 = !{!"/FAILIFMISMATCH:\22annotate_vector=0\22"}
!7 = !{i32 1, !"wchar_size", i32 2}
!8 = !{i32 8, !"PIC Level", i32 2}
!9 = !{i32 7, !"uwtable", i32 2}
!10 = !{i32 1, !"MaxTLSAlign", i32 65536}
!11 = !{!"clang version 17.0.1"}
!12 = distinct !{!12, !13}
!13 = !{!"llvm.loop.mustprogress"}
