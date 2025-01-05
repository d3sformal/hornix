(set-logic HORN)
(declare-fun |?bar@@YAHHH@Z0_entry| ( Int Int) Bool )
(declare-fun |?bar@@YAHHH@Z1_entry| ( Int Int Int Bool) Bool )
(declare-fun |?bar@@YAHHH@Z1_exit| ( Int Int Int Bool) Bool )
(declare-fun |?bar@@YAHHH@Z3_entry| ( Int Int Int Bool) Bool )
(declare-fun |?bar@@YAHHH@Z| ( Int Int Int Bool Bool) Bool )
(declare-fun |?bar@@YAHHH@Z3_exit| ( Int Int Int Bool) Bool )

(assert 
 (forall ( ( %x0 Int )( %x1 Int ) )
  (=>  
   true
   (?bar@@YAHHH@Z0_entry %x1 %x0 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Int )( %x3 Bool ) )
  (=>  
   (?bar@@YAHHH@Z0_entry %x1 %x0 )
   (?bar@@YAHHH@Z1_entry %x1 %x0 %x2 %x3 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Int )( %x2p Int )( %x3 Bool )( %x3p Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z1_entry %x1 %x0 %x2 %x3 ) (= %x2p (- %x0 %x1 )) (= %x3p (>= %x0 0 )) )
   (?bar@@YAHHH@Z1_exit %x1 %x0 %x2p %x3p )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Int )( %x3 Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z1_exit %x1 %x0 %x2 %x3 ) (= %x3 true ) )
   (?bar@@YAHHH@Z3_entry %x1 %x0 %x2 %x3 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Int )( %x3 Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z1_exit %x1 %x0 %x2 %x3 ) (= %x3 false ) )
   (?bar@@YAHHH@Z %x0 %x1 %x2 false true )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Int )( %x3 Bool ) )
  (=>  
   (?bar@@YAHHH@Z3_entry %x1 %x0 %x2 %x3 )
   (?bar@@YAHHH@Z3_exit %x1 %x0 %x2 %x3 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Int )( %x3 Bool ) )
  (=>  
   (?bar@@YAHHH@Z3_exit %x1 %x0 %x2 %x3 )
   (?bar@@YAHHH@Z %x0 %x1 %x2 false false )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Int ) )
  (?bar@@YAHHH@Z %x0 %x1 %x2 true true )
 )
)

(declare-fun |main0_entry| () Bool )
(declare-fun |main1_entry| ( Int) Bool )
(declare-fun |main1_exit| ( Int Bool) Bool )
(declare-fun |main2_entry| ( Int Bool) Bool )
(declare-fun |main_error| () Bool )
(declare-fun |main2_exit| ( Int Bool) Bool )
(declare-fun |main4_entry| ( Int Bool) Bool )
(declare-fun |main4_exit| ( Int Bool) Bool )
(declare-fun |main| ( Int) Bool )

(assert 
 (=>  
  true
  main0_entry
 )
)
(assert 
 (forall ( ( %x8 Int ) )
  (=>  
   main0_entry
   (main1_entry %x8 )
  )
 )
)
(assert 
 (forall ( ( %x8 Int )( %x8p Int )( e1 Bool ) )
  (=>  
   (and (main1_entry %x8 ) (?bar@@YAHHH@Z 10 1 %x8p false e1 ) )
   (main1_exit %x8p e1 )
  )
 )
)
(assert 
 (forall ( ( %x15 Bool )( %x8 Int ) )
  (=>  
   (and (main1_exit %x8 false ) (= true true ) )
   (main2_entry %x8 %x15 )
  )
 )
)
(assert 
 (forall ( ( %x8 Int ) )
  (=>  
   (main1_exit %x8 true )
   main_error
  )
 )
)
(assert 
 (forall ( ( %x15 Bool )( %x15p Bool )( %x8 Int ) )
  (=>  
   (and (main2_entry %x8 %x15 ) (= %x15p (= %x8 9 )) )
   (main2_exit %x8 %x15p )
  )
 )
)
(assert 
 (forall ( ( %x15 Bool )( %x8 Int ) )
  (=>  
   (and (main2_exit %x8 %x15 ) (= %x15 true ) )
   (main4_entry %x8 %x15 )
  )
 )
)
(assert 
 (forall ( ( %x15 Bool )( %x8 Int ) )
  (=>  
   (and (main2_exit %x8 %x15 ) (= %x15 false ) )
   main_error
  )
 )
)
(assert 
 (forall ( ( %x15 Bool )( %x8 Int ) )
  (=>  
   (main4_entry %x8 %x15 )
   (main4_exit %x8 %x15 )
  )
 )
)
(assert 
 (forall ( ( %x15 Bool )( %x8 Int ) )
  (=>  
   (main4_exit %x8 %x15 )
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
