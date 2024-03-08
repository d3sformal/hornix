; ModuleID = 'ex-mem2reg.ll'
source_filename = "example.cpp"
target datalayout = "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-windows-msvc19.38.33134"

; Function Attrs: mustprogress noinline nounwind uwtable
define dso_local noundef i32 @"?max@@YAHHH@Z"(i32 noundef %0, i32 noundef %1) #0 {
  %.0.reg2mem = alloca i32, align 4
  %"reg2mem alloca point" = bitcast i32 0 to i32
  %3 = icmp sgt i32 %0, %1
  br i1 %3, label %4, label %5

4:                                                ; preds = %2
  store i32 %0, ptr %.0.reg2mem, align 4
  br label %6

5:                                                ; preds = %2
  store i32 %1, ptr %.0.reg2mem, align 4
  br label %6

6:                                                ; preds = %5, %4
  %.0.reload = load i32, ptr %.0.reg2mem, align 4
  ret i32 %.0.reload
}

; Function Attrs: mustprogress noinline nounwind uwtable
define dso_local noundef i32 @"?add@@YAHH@Z"(i32 noundef %0) #0 {
  %.reg2mem = alloca i32, align 4
  %.reg2mem1 = alloca i32, align 4
  %.0.reg2mem = alloca i32, align 4
  %.01.reg2mem = alloca i32, align 4
  %.0.reg2mem6 = alloca i32, align 4
  %.01.reg2mem8 = alloca i32, align 4
  %"reg2mem alloca point" = bitcast i32 0 to i32
  store i32 1, ptr %.0.reg2mem6, align 4
  store i32 %0, ptr %.01.reg2mem8, align 4
  br label %2

2:                                                ; preds = %6, %1
  %.01.reload9 = load i32, ptr %.01.reg2mem8, align 4
  %.0.reload7 = load i32, ptr %.0.reg2mem6, align 4
  store i32 %.01.reload9, ptr %.01.reg2mem, align 4
  store i32 %.0.reload7, ptr %.0.reg2mem, align 4
  %.0.reload4 = load i32, ptr %.0.reg2mem, align 4
  %3 = icmp slt i32 %.0.reload4, 10
  br i1 %3, label %4, label %8

4:                                                ; preds = %2
  %.0.reload3 = load i32, ptr %.0.reg2mem, align 4
  %.01.reload5 = load i32, ptr %.01.reg2mem, align 4
  %5 = add nsw i32 %.01.reload5, %.0.reload3
  store i32 %5, ptr %.reg2mem1, align 4
  br label %6

6:                                                ; preds = %4
  %.0.reload = load i32, ptr %.0.reg2mem, align 4
  %7 = add nsw i32 %.0.reload, 1
  store i32 %7, ptr %.reg2mem, align 4
  %.reload = load i32, ptr %.reg2mem, align 4
  %.reload2 = load i32, ptr %.reg2mem1, align 4
  store i32 %.reload, ptr %.0.reg2mem6, align 4
  store i32 %.reload2, ptr %.01.reg2mem8, align 4
  br label %2, !llvm.loop !5

8:                                                ; preds = %2
  %.01.reload = load i32, ptr %.01.reg2mem, align 4
  ret i32 %.01.reload
}

; Function Attrs: mustprogress noinline norecurse nounwind uwtable
define dso_local noundef i32 @main(i32 noundef %0, ptr noundef %1) #1 {
  %"reg2mem alloca point" = bitcast i32 0 to i32
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
