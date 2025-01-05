; ModuleID = 'LLVMIRs/example2.ll'
source_filename = "example2.cpp"
target datalayout = "e-m:w-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-windows-msvc19.38.33134"

$"??_C@_0M@KEBPDOMG@reach_error?$AA@" = comdat any

$"??_C@_0BG@PKFEHKPB@for_infinite_loop_2?4c?$AA@" = comdat any

$"??_C@_01GBGANLPD@0?$AA@" = comdat any

@"??_C@_0M@KEBPDOMG@reach_error?$AA@" = linkonce_odr dso_local unnamed_addr constant [12 x i8] c"reach_error\00", comdat, align 1
@"??_C@_0BG@PKFEHKPB@for_infinite_loop_2?4c?$AA@" = linkonce_odr dso_local unnamed_addr constant [22 x i8] c"for_infinite_loop_2.c\00", comdat, align 1
@"??_C@_01GBGANLPD@0?$AA@" = linkonce_odr dso_local unnamed_addr constant [2 x i8] c"0\00", comdat, align 1

; Function Attrs: mustprogress noinline nounwind uwtable
define dso_local void @"?reach_error@@YAXXZ"() #0 {
  call void @"?__assert_fail@@YAXPEBD0I0@Z"(ptr noundef @"??_C@_01GBGANLPD@0?$AA@", ptr noundef @"??_C@_0BG@PKFEHKPB@for_infinite_loop_2?4c?$AA@", i32 noundef 3, ptr noundef @"??_C@_0M@KEBPDOMG@reach_error?$AA@") #5
  unreachable
}

; Function Attrs: nocallback noreturn nounwind
declare dso_local void @"?__assert_fail@@YAXPEBD0I0@Z"(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: mustprogress noinline uwtable
define dso_local void @"?assume_abort_if_not@@YAXH@Z"(i32 noundef %0) #2 {
  %2 = icmp ne i32 %0, 0
  br i1 %2, label %4, label %3

3:                                                ; preds = %1
  call void @"?abort@@YAXXZ"()
  br label %4

4:                                                ; preds = %3, %1
  ret void
}

declare dso_local void @"?abort@@YAXXZ"() #3

; Function Attrs: mustprogress noinline uwtable
define dso_local void @"?__VERIFIER_assert@@YAXH@Z"(i32 noundef %0) #2 {
  %2 = icmp ne i32 %0, 0
  br i1 %2, label %5, label %3

3:                                                ; preds = %1
  br label %4

4:                                                ; preds = %3
  call void @"?reach_error@@YAXXZ"()
  call void @"?abort@@YAXXZ"()
  br label %5

5:                                                ; preds = %4, %1
  ret void
}

; Function Attrs: mustprogress noinline norecurse uwtable
define dso_local noundef i32 @main() #4 {
  %1 = call noundef i32 @"?__VERIFIER_nondet_int@@YAHXZ"()
  %2 = icmp sgt i32 %1, 0
  br i1 %2, label %4, label %3

3:                                                ; preds = %0
  br label %10

4:                                                ; preds = %0
  br label %5

5:                                                ; preds = %7, %4
  %.01 = phi i32 [ 0, %4 ], [ %8, %7 ]
  br i1 true, label %6, label %9

6:                                                ; preds = %5
  call void @"?__VERIFIER_assert@@YAXH@Z"(i32 noundef 1)
  br label %7

7:                                                ; preds = %6
  %8 = add i32 %.01, 1
  br label %5, !llvm.loop !5

9:                                                ; preds = %5
  call void @"?__VERIFIER_assert@@YAXH@Z"(i32 noundef 0)
  br label %10

10:                                               ; preds = %9, %3
  ret i32 0
}

declare dso_local noundef i32 @"?__VERIFIER_nondet_int@@YAHXZ"() #3

attributes #0 = { mustprogress noinline nounwind uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback noreturn nounwind "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { mustprogress noinline uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { mustprogress noinline norecurse uwtable "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #5 = { nocallback noreturn nounwind }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 1, !"wchar_size", i32 2}
!1 = !{i32 8, !"PIC Level", i32 2}
!2 = !{i32 7, !"uwtable", i32 2}
!3 = !{i32 1, !"MaxTLSAlign", i32 65536}
!4 = !{!"clang version 18.1.8 (https://github.com/llvm/llvm-project.git 4ec508cc867ae77acbb67775609d09e67e0fbb12)"}
!5 = distinct !{!5, !6}
!6 = !{!"llvm.loop.mustprogress"}
