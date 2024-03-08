; ModuleID = 'ex-max-no-opt.ll'
source_filename = "example.cpp"
target datalayout = "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-windows-msvc19.38.33134"

; Function Attrs: mustprogress noinline nounwind uwtable
define dso_local noundef i32 @"?max@@YAHHH@Z"(i32 noundef %0, i32 noundef %1) #0 {
  %3 = icmp sgt i32 %0, %1
  br i1 %3, label %4, label %5

4:                                                ; preds = %2
  br label %6

5:                                                ; preds = %2
  br label %6

6:                                                ; preds = %5, %4
  %.0 = phi i32 [ %0, %4 ], [ %1, %5 ]
  ret i32 %.0
}

; Function Attrs: mustprogress noinline nounwind uwtable
define dso_local noundef i32 @"?add@@YAHH@Z"(i32 noundef %0) #0 {
  br label %2

2:                                                ; preds = %6, %1
  %.01 = phi i32 [ %0, %1 ], [ %5, %6 ]
  %.0 = phi i32 [ 1, %1 ], [ %7, %6 ]
  %3 = icmp slt i32 %.0, 10
  br i1 %3, label %4, label %8

4:                                                ; preds = %2
  %5 = add nsw i32 %.01, %.0
  br label %6

6:                                                ; preds = %4
  %7 = add nsw i32 %.0, 1
  br label %2, !llvm.loop !5

8:                                                ; preds = %2
  ret i32 %.01
}

; Function Attrs: mustprogress noinline norecurse nounwind uwtable
define dso_local noundef i32 @main(i32 noundef %0, ptr noundef %1) #1 {
  %3 = call noundef i32 @"?max@@YAHHH@Z"(i32 noundef 1, i32 noundef 2)
  ret i32 0
}

attributes #0 = { mustprogress noinline nounwind uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { mustprogress noinline norecurse nounwind uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 2}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{i32 1, !"MaxTLSAlign", i32 65536}
!4 = !{!"clang version 17.0.1"}
!5 = distinct !{!5, !6}
!6 = !{!"llvm.loop.mustprogress"}
