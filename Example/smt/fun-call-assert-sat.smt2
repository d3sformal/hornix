(set-logic HORN)
(declare-fun |?foo@@YAHHH@Z0_entry| ( Int Int) Bool )
(declare-fun |?foo@@YAHHH@Z1_entry| ( Int Int Int) Bool )
(declare-fun |?foo@@YAHHH@Z1_exit| ( Int Int Int) Bool )
(declare-fun |?foo@@YAHHH@Z| ( Int Int Int Bool Bool) Bool )

(assert 
 (forall ( ( %x0 Int )( %x1 Int ) )
  (=>  
   true
   (?foo@@YAHHH@Z0_entry %x1 %x0 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Int ) )
  (=>  
   (?foo@@YAHHH@Z0_entry %x1 %x0 )
   (?foo@@YAHHH@Z1_entry %x2 %x1 %x0 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Int )( %x2p Int ) )
  (=>  
   (and (?foo@@YAHHH@Z1_entry %x2 %x1 %x0 ) (= %x2p (+ %x0 %x1 )) )
   (?foo@@YAHHH@Z1_exit %x2p %x1 %x0 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Int ) )
  (=>  
   (?foo@@YAHHH@Z1_exit %x2 %x1 %x0 )
   (?foo@@YAHHH@Z %x0 %x1 %x2 false false )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Int ) )
  (?foo@@YAHHH@Z %x0 %x1 %x2 true true )
 )
)

(declare-fun |?bar@@YAHHH@Z0_entry| ( Int Int) Bool )
(declare-fun |?bar@@YAHHH@Z1_entry| ( Bool Int Int Int) Bool )
(declare-fun |?bar@@YAHHH@Z1_exit| ( Bool Int Int Int) Bool )
(declare-fun |?bar@@YAHHH@Z2_entry| ( Int Int Int Bool Bool) Bool )
(declare-fun |?bar@@YAHHH@Z| ( Int Int Int Bool Bool) Bool )
(declare-fun |?bar@@YAHHH@Z2_exit| ( Int Int Int Bool Bool) Bool )
(declare-fun |?bar@@YAHHH@Z3_entry| ( Bool Int Int Int Bool Bool) Bool )
(declare-fun |?bar@@YAHHH@Z3_exit| ( Bool Int Int Int Bool Bool) Bool )
(declare-fun |?bar@@YAHHH@Z5_entry| ( Bool Int Int Int Bool Bool) Bool )
(declare-fun |?bar@@YAHHH@Z5_exit| ( Bool Int Int Int Bool Bool) Bool )

(assert 
 (forall ( ( %x3 Int )( %x4 Int ) )
  (=>  
   true
   (?bar@@YAHHH@Z0_entry %x4 %x3 )
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool ) )
  (=>  
   (?bar@@YAHHH@Z0_entry %x4 %x3 )
   (?bar@@YAHHH@Z1_entry %x6 %x5 %x4 %x3 )
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x4 Int )( %x5 Int )( %x5p Int )( %x6 Bool )( %x6p Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z1_entry %x6 %x5 %x4 %x3 ) (= %x5p (- %x3 %x4 )) (= %x6p (>= %x3 0 )) )
   (?bar@@YAHHH@Z1_exit %x6p %x5p %x4 %x3 )
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x9 Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z1_exit %x6 %x5 %x4 %x3 ) (= %x6 true ) )
   (?bar@@YAHHH@Z2_entry %x3 %x4 %x5 %x6 %x9 )
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z1_exit %x6 %x5 %x4 %x3 ) (= %x6 false ) )
   (?bar@@YAHHH@Z %x3 %x4 %x5 false true )
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x9 Bool )( %x9p Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z2_entry %x3 %x4 %x5 %x6 %x9 ) (= %x9p (>= %x4 0 )) )
   (?bar@@YAHHH@Z2_exit %x3 %x4 %x5 %x6 %x9p )
  )
 )
)
(assert 
 (forall ( ( %x12 Bool )( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x9 Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z2_exit %x3 %x4 %x5 %x6 %x9 ) (= %x9 true ) )
   (?bar@@YAHHH@Z3_entry %x6 %x5 %x4 %x3 %x9 %x12 )
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x9 Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z2_exit %x3 %x4 %x5 %x6 %x9 ) (= %x9 false ) )
   (?bar@@YAHHH@Z %x3 %x4 %x5 false true )
  )
 )
)
(assert 
 (forall ( ( %x12 Bool )( %x12p Bool )( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x9 Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z3_entry %x6 %x5 %x4 %x3 %x9 %x12 ) (= %x12p (> %x3 %x5 )) )
   (?bar@@YAHHH@Z3_exit %x6 %x5 %x4 %x3 %x9 %x12p )
  )
 )
)
(assert 
 (forall ( ( %x12 Bool )( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x9 Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z3_exit %x6 %x5 %x4 %x3 %x9 %x12 ) (= %x12 true ) )
   (?bar@@YAHHH@Z5_entry %x6 %x5 %x4 %x3 %x9 %x12 )
  )
 )
)
(assert 
 (forall ( ( %x12 Bool )( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x9 Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z3_exit %x6 %x5 %x4 %x3 %x9 %x12 ) (= %x12 false ) )
   (?bar@@YAHHH@Z %x3 %x4 %x5 false true )
  )
 )
)
(assert 
 (forall ( ( %x12 Bool )( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x9 Bool ) )
  (=>  
   (?bar@@YAHHH@Z5_entry %x6 %x5 %x4 %x3 %x9 %x12 )
   (?bar@@YAHHH@Z5_exit %x6 %x5 %x4 %x3 %x9 %x12 )
  )
 )
)
(assert 
 (forall ( ( %x12 Bool )( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x9 Bool ) )
  (=>  
   (?bar@@YAHHH@Z5_exit %x6 %x5 %x4 %x3 %x9 %x12 )
   (?bar@@YAHHH@Z %x3 %x4 %x5 false false )
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x4 Int )( %x5 Int ) )
  (?bar@@YAHHH@Z %x3 %x4 %x5 true true )
 )
)

(declare-fun |main0_entry| () Bool )
(declare-fun |main1_entry| ( Int Int Int Bool) Bool )
(declare-fun |main1_exit| ( Int Int Int Bool Bool) Bool )
(declare-fun |main2_entry| ( Int Int Int Bool Bool) Bool )
(declare-fun |main_error| () Bool )
(declare-fun |main2_exit| ( Int Int Int Bool Bool) Bool )
(declare-fun |main4_entry| ( Int Int Int Bool Bool) Bool )
(declare-fun |main4_exit| ( Int Int Int Bool Bool) Bool )
(declare-fun |main| ( Int) Bool )

(assert 
 (=>  
  true
  main0_entry
 )
)
(assert 
 (forall ( ( %x18 Int )( %x21 Int )( %x23 Int )( %x24 Bool ) )
  (=>  
   main0_entry
   (main1_entry %x18 %x21 %x23 %x24 )
  )
 )
)
(assert 
 (forall ( ( %x18 Int )( %x18p Int )( %x21 Int )( %x21p Int )( %x23 Int )( %x23p Int )( %x24 Bool )( %x24p Bool )( e1 Bool )( e2 Bool )( e3 Bool ) )
  (=>  
   (and (main1_entry %x18 %x21 %x23 %x24 ) (?foo@@YAHHH@Z 10 1 %x18p false e1 ) (?bar@@YAHHH@Z %x18p 1 %x21p e1 e2 ) (?bar@@YAHHH@Z %x18p %x21p %x23p e2 e3 ) (= %x24p (= %x23p 1 )) )
   (main1_exit %x18p %x21p %x23p %x24p e3 )
  )
 )
)
(assert 
 (forall ( ( %x18 Int )( %x21 Int )( %x23 Int )( %x24 Bool )( %x28 Bool ) )
  (=>  
   (and (main1_exit %x18 %x21 %x23 %x24 false ) (= %x24 true ) )
   (main2_entry %x18 %x21 %x23 %x24 %x28 )
  )
 )
)
(assert 
 (forall ( ( %x18 Int )( %x21 Int )( %x23 Int )( %x24 Bool )( e3 Bool ) )
  (=>  
   (and (main1_exit %x18 %x21 %x23 %x24 e3 ) (= %x24 false ) )
   main_error
  )
 )
)
(assert 
 (forall ( ( %x18 Int )( %x21 Int )( %x23 Int )( %x24 Bool ) )
  (=>  
   (main1_exit %x18 %x21 %x23 %x24 true )
   main_error
  )
 )
)
(assert 
 (forall ( ( %x18 Int )( %x21 Int )( %x23 Int )( %x24 Bool )( %x28 Bool )( %x28p Bool ) )
  (=>  
   (and (main2_entry %x18 %x21 %x23 %x24 %x28 ) (= %x28p (= %x21 10 )) )
   (main2_exit %x18 %x21 %x23 %x24 %x28p )
  )
 )
)
(assert 
 (forall ( ( %x18 Int )( %x21 Int )( %x23 Int )( %x24 Bool )( %x28 Bool ) )
  (=>  
   (and (main2_exit %x18 %x21 %x23 %x24 %x28 ) (= %x28 true ) )
   (main4_entry %x18 %x21 %x23 %x24 %x28 )
  )
 )
)
(assert 
 (forall ( ( %x18 Int )( %x21 Int )( %x23 Int )( %x24 Bool )( %x28 Bool ) )
  (=>  
   (and (main2_exit %x18 %x21 %x23 %x24 %x28 ) (= %x28 false ) )
   main_error
  )
 )
)
(assert 
 (forall ( ( %x18 Int )( %x21 Int )( %x23 Int )( %x24 Bool )( %x28 Bool ) )
  (=>  
   (main4_entry %x18 %x21 %x23 %x24 %x28 )
   (main4_exit %x18 %x21 %x23 %x24 %x28 )
  )
 )
)
(assert 
 (forall ( ( %x18 Int )( %x21 Int )( %x23 Int )( %x24 Bool )( %x28 Bool ) )
  (=>  
   (main4_exit %x18 %x21 %x23 %x24 %x28 )
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
