; RUN: opt < %s -reassociate -constprop -instcombine -dce -S | FileCheck %s

; With sub reassociation, constant folding can eliminate all of the constants.
define i32 @test1(i32 %A, i32 %B) {
; CHECK-LABEL: @test1(
; CHECK-NEXT:    [[Z:%.*]] = sub i32 %A, %B
; CHECK-NEXT:    ret i32 [[Z]]
;
  %W = add i32 5, %B
  %X = add i32 -7, %A
  %Y = sub i32 %X, %W
  %Z = add i32 %Y, 12
  ret i32 %Z
}

; With sub reassociation, constant folding can eliminate the two 12 constants.
define i32 @test2(i32 %A, i32 %B, i32 %C, i32 %D) {
; CHECK-LABEL: @test2(
; CHECK-NEXT:    [[SUM:%.*]] = add i32 %B, %A
; CHECK-NEXT:    [[SUM1:%.*]] = add i32 [[SUM]], %C
; CHECK-NEXT:    [[Q:%.*]] = sub i32 %D, [[SUM1]]
; CHECK-NEXT:    ret i32 [[Q]]
;
  %M = add i32 %A, 12
  %N = add i32 %M, %B
  %O = add i32 %N, %C
  %P = sub i32 %D, %O
  %Q = add i32 %P, 12
  ret i32 %Q
}

