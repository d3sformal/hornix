(set-logic HORN)
(declare-fun |?reach_error@@YAXXZ0_entry| () Bool )
(declare-fun |?reach_error@@YAXXZ| ( Bool Bool) Bool )

(assert 
 (=>  
  true
  ?reach_error@@YAXXZ0_entry
 )
)
(assert 
 (=>  
  ?reach_error@@YAXXZ0_entry
  (?reach_error@@YAXXZ false true )
 )
)
(assert 
 (?reach_error@@YAXXZ true true )
)

(declare-fun |?assume_abort_if_not@@YAXH@Z0_entry| ( Int) Bool )
(declare-fun |?assume_abort_if_not@@YAXH@Z1_entry| ( Int Bool) Bool )
(declare-fun |?assume_abort_if_not@@YAXH@Z1_exit| ( Int Bool) Bool )
(declare-fun |?assume_abort_if_not@@YAXH@Z3_entry| ( Int Bool) Bool )
(declare-fun |?assume_abort_if_not@@YAXH@Z2_entry| ( Int Bool) Bool )
(declare-fun |?assume_abort_if_not@@YAXH@Z2_exit| ( Int Bool) Bool )
(declare-fun |?assume_abort_if_not@@YAXH@Z3_exit| ( Int Bool) Bool )
(declare-fun |?assume_abort_if_not@@YAXH@Z| ( Int Bool Bool) Bool )

(assert 
 (forall ( ( %x0 Int ) )
  (=>  
   true
   (?assume_abort_if_not@@YAXH@Z0_entry %x0 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Bool ) )
  (=>  
   (?assume_abort_if_not@@YAXH@Z0_entry %x0 )
   (?assume_abort_if_not@@YAXH@Z1_entry %x0 %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Bool )( %x1p Bool ) )
  (=>  
   (and (?assume_abort_if_not@@YAXH@Z1_entry %x0 %x1 ) (= %x1p (not (= %x0 0 ))) )
   (?assume_abort_if_not@@YAXH@Z1_exit %x0 %x1p )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Bool ) )
  (=>  
   (and (?assume_abort_if_not@@YAXH@Z1_exit %x0 %x1 ) (= %x1 true ) )
   (?assume_abort_if_not@@YAXH@Z3_entry %x0 %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Bool ) )
  (=>  
   (and (?assume_abort_if_not@@YAXH@Z1_exit %x0 %x1 ) (= %x1 false ) )
   (?assume_abort_if_not@@YAXH@Z2_entry %x0 %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Bool ) )
  (=>  
   (and (?assume_abort_if_not@@YAXH@Z2_entry %x0 %x1 ) true )
   (?assume_abort_if_not@@YAXH@Z2_exit %x0 %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Bool ) )
  (=>  
   (?assume_abort_if_not@@YAXH@Z2_exit %x0 %x1 )
   (?assume_abort_if_not@@YAXH@Z3_entry %x0 %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Bool ) )
  (=>  
   (?assume_abort_if_not@@YAXH@Z3_entry %x0 %x1 )
   (?assume_abort_if_not@@YAXH@Z3_exit %x0 %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Bool ) )
  (=>  
   (?assume_abort_if_not@@YAXH@Z3_exit %x0 %x1 )
   (?assume_abort_if_not@@YAXH@Z %x0 false false )
  )
 )
)
(assert 
 (forall ( ( %x0 Int ) )
  (?assume_abort_if_not@@YAXH@Z %x0 true true )
 )
)

(declare-fun |?__VERIFIER_assert@@YAXH@Z0_entry| ( Int) Bool )
(declare-fun |?__VERIFIER_assert@@YAXH@Z1_entry| ( Int Bool) Bool )
(declare-fun |?__VERIFIER_assert@@YAXH@Z1_exit| ( Int Bool) Bool )
(declare-fun |?__VERIFIER_assert@@YAXH@Z4_entry| ( Int Bool) Bool )
(declare-fun |?__VERIFIER_assert@@YAXH@Z2_entry| ( Int Bool) Bool )
(declare-fun |?__VERIFIER_assert@@YAXH@Z2_exit| ( Int Bool) Bool )
(declare-fun |?__VERIFIER_assert@@YAXH@Z3_entry| ( Int Bool) Bool )
(declare-fun |?__VERIFIER_assert@@YAXH@Z3_exit| ( Int Bool Bool) Bool )
(declare-fun |?__VERIFIER_assert@@YAXH@Z| ( Int Bool Bool) Bool )
(declare-fun |?__VERIFIER_assert@@YAXH@Z4_exit| ( Int Bool) Bool )

(assert 
 (forall ( ( %x6 Int ) )
  (=>  
   true
   (?__VERIFIER_assert@@YAXH@Z0_entry %x6 )
  )
 )
)
(assert 
 (forall ( ( %x6 Int )( %x7 Bool ) )
  (=>  
   (?__VERIFIER_assert@@YAXH@Z0_entry %x6 )
   (?__VERIFIER_assert@@YAXH@Z1_entry %x6 %x7 )
  )
 )
)
(assert 
 (forall ( ( %x6 Int )( %x7 Bool )( %x7p Bool ) )
  (=>  
   (and (?__VERIFIER_assert@@YAXH@Z1_entry %x6 %x7 ) (= %x7p (not (= %x6 0 ))) )
   (?__VERIFIER_assert@@YAXH@Z1_exit %x6 %x7p )
  )
 )
)
(assert 
 (forall ( ( %x6 Int )( %x7 Bool ) )
  (=>  
   (and (?__VERIFIER_assert@@YAXH@Z1_exit %x6 %x7 ) (= %x7 true ) )
   (?__VERIFIER_assert@@YAXH@Z4_entry %x6 %x7 )
  )
 )
)
(assert 
 (forall ( ( %x6 Int )( %x7 Bool ) )
  (=>  
   (and (?__VERIFIER_assert@@YAXH@Z1_exit %x6 %x7 ) (= %x7 false ) )
   (?__VERIFIER_assert@@YAXH@Z2_entry %x6 %x7 )
  )
 )
)
(assert 
 (forall ( ( %x6 Int )( %x7 Bool ) )
  (=>  
   (?__VERIFIER_assert@@YAXH@Z2_entry %x6 %x7 )
   (?__VERIFIER_assert@@YAXH@Z2_exit %x6 %x7 )
  )
 )
)
(assert 
 (forall ( ( %x6 Int )( %x7 Bool ) )
  (=>  
   (?__VERIFIER_assert@@YAXH@Z2_exit %x6 %x7 )
   (?__VERIFIER_assert@@YAXH@Z3_entry %x6 %x7 )
  )
 )
)
(assert 
 (forall ( ( %x6 Int )( %x7 Bool )( e1 Bool ) )
  (=>  
   (and (?__VERIFIER_assert@@YAXH@Z3_entry %x6 %x7 ) (?reach_error@@YAXXZ false e1 ) true )
   (?__VERIFIER_assert@@YAXH@Z3_exit %x6 %x7 e1 )
  )
 )
)
(assert 
 (forall ( ( %x6 Int )( %x7 Bool ) )
  (=>  
   (?__VERIFIER_assert@@YAXH@Z3_exit %x6 %x7 false )
   (?__VERIFIER_assert@@YAXH@Z4_entry %x6 %x7 )
  )
 )
)
(assert 
 (forall ( ( %x6 Int )( %x7 Bool ) )
  (=>  
   (?__VERIFIER_assert@@YAXH@Z3_exit %x6 %x7 true )
   (?__VERIFIER_assert@@YAXH@Z %x6 false true )
  )
 )
)
(assert 
 (forall ( ( %x6 Int )( %x7 Bool ) )
  (=>  
   (?__VERIFIER_assert@@YAXH@Z4_entry %x6 %x7 )
   (?__VERIFIER_assert@@YAXH@Z4_exit %x6 %x7 )
  )
 )
)
(assert 
 (forall ( ( %x6 Int )( %x7 Bool ) )
  (=>  
   (?__VERIFIER_assert@@YAXH@Z4_exit %x6 %x7 )
   (?__VERIFIER_assert@@YAXH@Z %x6 false false )
  )
 )
)
(assert 
 (forall ( ( %x6 Int ) )
  (?__VERIFIER_assert@@YAXH@Z %x6 true true )
 )
)

(declare-fun |main0_entry| () Bool )
(declare-fun |main1_entry| ( Int Bool) Bool )
(declare-fun |main1_exit| ( Int Bool) Bool )
(declare-fun |main3_entry| ( Int Bool) Bool )
(declare-fun |main2_entry| ( Int Bool) Bool )
(declare-fun |main2_exit| ( Int Bool) Bool )
(declare-fun |main8_entry| ( Int Int Bool Int) Bool )
(declare-fun |main3_exit| ( Int Bool) Bool )
(declare-fun |main4_entry| ( Int Int Bool Int) Bool )
(declare-fun |main4_exit| ( Int Int Bool Int) Bool )
(declare-fun |main5_entry| ( Int Bool Int Int) Bool )
(declare-fun |main5_exit| ( Int Bool Int Int Bool) Bool )
(declare-fun |main6_entry| ( Int Int Bool Int) Bool )
(declare-fun |main_error| () Bool )
(declare-fun |main6_exit| ( Int Int Bool Int) Bool )
(declare-fun |main7_exit| ( Int Bool Int Int Bool) Bool )
(declare-fun |main7_entry| ( Int Bool Int Int) Bool )
(declare-fun |main8_exit| ( Int Int Bool Int) Bool )
(declare-fun |main| ( Int) Bool )

(assert 
 (=>  
  true
  main0_entry
 )
)
(assert 
 (forall ( ( %x13 Int )( %x14 Bool ) )
  (=>  
   main0_entry
   (main1_entry %x13 %x14 )
  )
 )
)
(assert 
 (forall ( ( %x13 Int )( %x14 Bool )( %x14p Bool ) )
  (=>  
   (and (main1_entry %x13 %x14 ) true (= %x14p (> %x13 0 )) )
   (main1_exit %x13 %x14p )
  )
 )
)
(assert 
 (forall ( ( %x13 Int )( %x14 Bool ) )
  (=>  
   (and (main1_exit %x13 %x14 ) (= %x14 true ) )
   (main3_entry %x13 %x14 )
  )
 )
)
(assert 
 (forall ( ( %x13 Int )( %x14 Bool ) )
  (=>  
   (and (main1_exit %x13 %x14 ) (= %x14 false ) )
   (main2_entry %x13 %x14 )
  )
 )
)
(assert 
 (forall ( ( %x13 Int )( %x14 Bool ) )
  (=>  
   (main2_entry %x13 %x14 )
   (main2_exit %x13 %x14 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x13 Int )( %x14 Bool )( %x20 Int ) )
  (=>  
   (main2_exit %x13 %x14 )
   (main8_entry %x13 %x20 %x14 %.01 )
  )
 )
)
(assert 
 (forall ( ( %x13 Int )( %x14 Bool ) )
  (=>  
   (main3_entry %x13 %x14 )
   (main3_exit %x13 %x14 )
  )
 )
)
(assert 
 (forall ( ( %.01p Int )( %x13 Int )( %x14 Bool )( %x20 Int ) )
  (=>  
   (and (main3_exit %x13 %x14 ) (= %.01p 0 ) )
   (main4_entry %x13 %x20 %x14 %.01p )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x13 Int )( %x14 Bool )( %x20 Int ) )
  (=>  
   (main4_entry %x13 %x20 %x14 %.01 )
   (main4_exit %x13 %x20 %x14 %.01 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x13 Int )( %x14 Bool )( %x20 Int ) )
  (=>  
   (and (main4_exit %x13 %x20 %x14 %.01 ) (= true true ) )
   (main5_entry %x13 %x14 %x20 %.01 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x13 Int )( %x14 Bool )( %x20 Int )( e1 Bool ) )
  (=>  
   (and (main5_entry %x13 %x14 %x20 %.01 ) (?__VERIFIER_assert@@YAXH@Z 1 false e1 ) )
   (main5_exit %x13 %x14 %x20 %.01 e1 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x13 Int )( %x14 Bool )( %x20 Int ) )
  (=>  
   (main5_exit %x13 %x14 %x20 %.01 false )
   (main6_entry %x13 %x20 %x14 %.01 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x13 Int )( %x14 Bool )( %x20 Int ) )
  (=>  
   (main5_exit %x13 %x14 %x20 %.01 true )
   main_error
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x13 Int )( %x14 Bool )( %x20 Int )( %x20p Int ) )
  (=>  
   (and (main6_entry %x13 %x20 %x14 %.01 ) (= %x20p (+ %.01 1 )) )
   (main6_exit %x13 %x20p %x14 %.01 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %.01p Int )( %x13 Int )( %x14 Bool )( %x20 Int ) )
  (=>  
   (and (main6_exit %x13 %x20 %x14 %.01 ) (= %.01p %x20 ) )
   (main4_entry %x13 %x20 %x14 %.01p )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x13 Int )( %x14 Bool )( %x20 Int )( e1 Bool ) )
  (=>  
   (and (main7_entry %x13 %x14 %x20 %.01 ) (?__VERIFIER_assert@@YAXH@Z 0 false e1 ) )
   (main7_exit %x13 %x14 %x20 %.01 e1 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x13 Int )( %x14 Bool )( %x20 Int ) )
  (=>  
   (main7_exit %x13 %x14 %x20 %.01 false )
   (main8_entry %x13 %x20 %x14 %.01 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x13 Int )( %x14 Bool )( %x20 Int ) )
  (=>  
   (main7_exit %x13 %x14 %x20 %.01 true )
   main_error
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x13 Int )( %x14 Bool )( %x20 Int ) )
  (=>  
   (main8_entry %x13 %x20 %x14 %.01 )
   (main8_exit %x13 %x20 %x14 %.01 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x13 Int )( %x14 Bool )( %x20 Int ) )
  (=>  
   (main8_exit %x13 %x20 %x14 %.01 )
   (main 0 )
  )
 )
)
(assert 
 (=>  
  main_error
  false
 )
)

(check-sat)
