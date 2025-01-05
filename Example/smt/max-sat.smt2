(set-logic HORN)
(declare-fun |?max@@YAHHH@Z0_entry| ( Int Int) Bool )
(declare-fun |?max@@YAHHH@Z1_entry| ( Bool Int Int) Bool )
(declare-fun |?max@@YAHHH@Z1_exit| ( Bool Int Int) Bool )
(declare-fun |?max@@YAHHH@Z2_entry| ( Int Int Bool) Bool )
(declare-fun |?max@@YAHHH@Z3_entry| ( Int Int Bool) Bool )
(declare-fun |?max@@YAHHH@Z2_exit| ( Int Int Bool) Bool )
(declare-fun |?max@@YAHHH@Z4_entry| ( Bool Int Int Int) Bool )
(declare-fun |?max@@YAHHH@Z3_exit| ( Int Int Bool) Bool )
(declare-fun |?max@@YAHHH@Z4_exit| ( Bool Int Int Int) Bool )
(declare-fun |?max@@YAHHH@Z5_entry| ( Int Int Bool Int) Bool )
(declare-fun |?max@@YAHHH@Z5_exit| ( Int Int Bool Int) Bool )
(declare-fun |?max@@YAHHH@Z7_entry| ( Int Int Bool Int) Bool )
(declare-fun |?max@@YAHHH@Z7_exit| ( Int Int Bool Int) Bool )
(declare-fun |?max@@YAHHH@Z| ( Int Int Int Bool Bool) Bool )

(assert 
 (forall ( ( %x0 Int )( %x1 Int ) )
  (=>  
   true
   (?max@@YAHHH@Z0_entry %x1 %x0 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Bool ) )
  (=>  
   (?max@@YAHHH@Z0_entry %x1 %x0 )
   (?max@@YAHHH@Z1_entry %x2 %x1 %x0 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Bool )( %x2p Bool ) )
  (=>  
   (and (?max@@YAHHH@Z1_entry %x2 %x1 %x0 ) (= %x2p (> %x0 %x1 )) )
   (?max@@YAHHH@Z1_exit %x2p %x1 %x0 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Bool ) )
  (=>  
   (and (?max@@YAHHH@Z1_exit %x2 %x1 %x0 ) (= %x2 true ) )
   (?max@@YAHHH@Z2_entry %x0 %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Bool ) )
  (=>  
   (and (?max@@YAHHH@Z1_exit %x2 %x1 %x0 ) (= %x2 false ) )
   (?max@@YAHHH@Z3_entry %x0 %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Bool ) )
  (=>  
   (?max@@YAHHH@Z2_entry %x0 %x1 %x2 )
   (?max@@YAHHH@Z2_exit %x0 %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %.0p Int )( %x0 Int )( %x1 Int )( %x2 Bool ) )
  (=>  
   (and (?max@@YAHHH@Z2_exit %x0 %x1 %x2 ) (= %.0p %x0 ) )
   (?max@@YAHHH@Z4_entry %x2 %x1 %x0 %.0p )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Bool ) )
  (=>  
   (?max@@YAHHH@Z3_entry %x0 %x1 %x2 )
   (?max@@YAHHH@Z3_exit %x0 %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %.0p Int )( %x0 Int )( %x1 Int )( %x2 Bool ) )
  (=>  
   (and (?max@@YAHHH@Z3_exit %x0 %x1 %x2 ) (= %.0p %x1 ) )
   (?max@@YAHHH@Z4_entry %x2 %x1 %x0 %.0p )
  )
 )
)
(assert 
 (forall ( ( %.0 Int )( %x0 Int )( %x1 Int )( %x2 Bool ) )
  (=>  
   (?max@@YAHHH@Z4_entry %x2 %x1 %x0 %.0 )
   (?max@@YAHHH@Z4_exit %x2 %x1 %x0 %.0 )
  )
 )
)
(assert 
 (forall ( ( %.0 Int )( %x0 Int )( %x1 Int )( %x2 Bool ) )
  (=>  
   (and (?max@@YAHHH@Z4_exit %x2 %x1 %x0 %.0 ) (= true true ) )
   (?max@@YAHHH@Z5_entry %x0 %x1 %x2 %.0 )
  )
 )
)
(assert 
 (forall ( ( %.0 Int )( %x0 Int )( %x1 Int )( %x2 Bool ) )
  (=>  
   (?max@@YAHHH@Z5_entry %x0 %x1 %x2 %.0 )
   (?max@@YAHHH@Z5_exit %x0 %x1 %x2 %.0 )
  )
 )
)
(assert 
 (forall ( ( %.0 Int )( %x0 Int )( %x1 Int )( %x2 Bool ) )
  (=>  
   (and (?max@@YAHHH@Z5_exit %x0 %x1 %x2 %.0 ) (= true true ) )
   (?max@@YAHHH@Z7_entry %x0 %x1 %x2 %.0 )
  )
 )
)
(assert 
 (forall ( ( %.0 Int )( %x0 Int )( %x1 Int )( %x2 Bool ) )
  (=>  
   (?max@@YAHHH@Z7_entry %x0 %x1 %x2 %.0 )
   (?max@@YAHHH@Z7_exit %x0 %x1 %x2 %.0 )
  )
 )
)
(assert 
 (forall ( ( %.0 Int )( %x0 Int )( %x1 Int )( %x2 Bool ) )
  (=>  
   (?max@@YAHHH@Z7_exit %x0 %x1 %x2 %.0 )
   (?max@@YAHHH@Z %x0 %x1 %.0 false false )
  )
 )
)
(assert 
 (forall ( ( %.0 Int )( %x0 Int )( %x1 Int ) )
  (?max@@YAHHH@Z %x0 %x1 %.0 true true )
 )
)

(declare-fun |main0_entry| () Bool )
(declare-fun |main1_entry| ( Int) Bool )
(declare-fun |main1_exit| ( Int Bool) Bool )
(declare-fun |main_error| () Bool )
(declare-fun |main| ( Int) Bool )

(assert 
 (=>  
  true
  main0_entry
 )
)
(assert 
 (forall ( ( %x10 Int ) )
  (=>  
   main0_entry
   (main1_entry %x10 )
  )
 )
)
(assert 
 (forall ( ( %x10 Int )( %x10p Int )( e1 Bool ) )
  (=>  
   (and (main1_entry %x10 ) (?max@@YAHHH@Z 1 2 %x10p false e1 ) )
   (main1_exit %x10p e1 )
  )
 )
)
(assert 
 (forall ( ( %x10 Int ) )
  (=>  
   (main1_exit %x10 true )
   main_error
  )
 )
)
(assert 
 (forall ( ( %x10 Int ) )
  (=>  
   (main1_exit %x10 false )
   (main 1 )
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
