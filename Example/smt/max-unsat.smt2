(set-logic HORN)
(declare-fun |?max@@YAXHH@Z0_entry| ( Int Int) Bool )
(declare-fun |?max@@YAXHH@Z1_entry| ( Int Int Bool) Bool )
(declare-fun |?max@@YAXHH@Z1_exit| ( Int Int Bool) Bool )
(declare-fun |?max@@YAXHH@Z2_entry| ( Int Int Bool) Bool )
(declare-fun |?max@@YAXHH@Z3_entry| ( Int Int Bool) Bool )
(declare-fun |?max@@YAXHH@Z2_exit| ( Int Int Bool) Bool )
(declare-fun |?max@@YAXHH@Z4_entry| ( Int Int Bool Bool Int) Bool )
(declare-fun |?max@@YAXHH@Z3_exit| ( Int Int Bool) Bool )
(declare-fun |?max@@YAXHH@Z4_exit| ( Int Int Bool Bool Int) Bool )
(declare-fun |?max@@YAXHH@Z5_entry| ( Int Int Bool Bool Bool Int) Bool )
(declare-fun |?max@@YAXHH@Z| ( Int Int Bool Bool) Bool )
(declare-fun |?max@@YAXHH@Z5_exit| ( Int Int Bool Bool Bool Int) Bool )
(declare-fun |?max@@YAXHH@Z7_entry| ( Int Int Bool Bool Bool Int) Bool )
(declare-fun |?max@@YAXHH@Z7_exit| ( Int Int Bool Bool Bool Int) Bool )

(assert 
 (forall ( ( %x0 Int )( %x1 Int ) )
  (=>  
   true
   (?max@@YAXHH@Z0_entry %x1 %x0 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Bool ) )
  (=>  
   (?max@@YAXHH@Z0_entry %x1 %x0 )
   (?max@@YAXHH@Z1_entry %x1 %x0 %x2 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Bool )( %x2p Bool ) )
  (=>  
   (and (?max@@YAXHH@Z1_entry %x1 %x0 %x2 ) (= %x2p (> %x0 %x1 )) )
   (?max@@YAXHH@Z1_exit %x1 %x0 %x2p )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Bool ) )
  (=>  
   (and (?max@@YAXHH@Z1_exit %x1 %x0 %x2 ) (= %x2 true ) )
   (?max@@YAXHH@Z2_entry %x0 %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Bool ) )
  (=>  
   (and (?max@@YAXHH@Z1_exit %x1 %x0 %x2 ) (= %x2 false ) )
   (?max@@YAXHH@Z3_entry %x0 %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Bool ) )
  (=>  
   (?max@@YAXHH@Z2_entry %x0 %x1 %x2 )
   (?max@@YAXHH@Z2_exit %x0 %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %.0p Int )( %x0 Int )( %x1 Int )( %x2 Bool )( %x3 Bool ) )
  (=>  
   (and (?max@@YAXHH@Z2_exit %x0 %x1 %x2 ) (= %.0p %x0 ) )
   (?max@@YAXHH@Z4_entry %x1 %x0 %x3 %x2 %.0p )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Bool ) )
  (=>  
   (?max@@YAXHH@Z3_entry %x0 %x1 %x2 )
   (?max@@YAXHH@Z3_exit %x0 %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %.0p Int )( %x0 Int )( %x1 Int )( %x2 Bool )( %x3 Bool ) )
  (=>  
   (and (?max@@YAXHH@Z3_exit %x0 %x1 %x2 ) (= %.0p %x1 ) )
   (?max@@YAXHH@Z4_entry %x1 %x0 %x3 %x2 %.0p )
  )
 )
)
(assert 
 (forall ( ( %.0 Int )( %x0 Int )( %x1 Int )( %x2 Bool )( %x3 Bool )( %x3p Bool ) )
  (=>  
   (and (?max@@YAXHH@Z4_entry %x1 %x0 %x3 %x2 %.0 ) (= %x3p (<= %.0 %x0 )) )
   (?max@@YAXHH@Z4_exit %x1 %x0 %x3p %x2 %.0 )
  )
 )
)
(assert 
 (forall ( ( %.0 Int )( %x0 Int )( %x1 Int )( %x2 Bool )( %x3 Bool )( %x4 Bool ) )
  (=>  
   (and (?max@@YAXHH@Z4_exit %x1 %x0 %x3 %x2 %.0 ) (= %x3 true ) )
   (?max@@YAXHH@Z5_entry %x0 %x1 %x4 %x2 %x3 %.0 )
  )
 )
)
(assert 
 (forall ( ( %.0 Int )( %x0 Int )( %x1 Int )( %x2 Bool )( %x3 Bool ) )
  (=>  
   (and (?max@@YAXHH@Z4_exit %x1 %x0 %x3 %x2 %.0 ) (= %x3 false ) )
   (?max@@YAXHH@Z %x0 %x1 false true )
  )
 )
)
(assert 
 (forall ( ( %.0 Int )( %x0 Int )( %x1 Int )( %x2 Bool )( %x3 Bool )( %x4 Bool )( %x4p Bool ) )
  (=>  
   (and (?max@@YAXHH@Z5_entry %x0 %x1 %x4 %x2 %x3 %.0 ) (= %x4p (<= %.0 %x1 )) )
   (?max@@YAXHH@Z5_exit %x0 %x1 %x4p %x2 %x3 %.0 )
  )
 )
)
(assert 
 (forall ( ( %.0 Int )( %x0 Int )( %x1 Int )( %x2 Bool )( %x3 Bool )( %x4 Bool ) )
  (=>  
   (and (?max@@YAXHH@Z5_exit %x0 %x1 %x4 %x2 %x3 %.0 ) (= %x4 true ) )
   (?max@@YAXHH@Z7_entry %x0 %x1 %x4 %x2 %x3 %.0 )
  )
 )
)
(assert 
 (forall ( ( %.0 Int )( %x0 Int )( %x1 Int )( %x2 Bool )( %x3 Bool )( %x4 Bool ) )
  (=>  
   (and (?max@@YAXHH@Z5_exit %x0 %x1 %x4 %x2 %x3 %.0 ) (= %x4 false ) )
   (?max@@YAXHH@Z %x0 %x1 false true )
  )
 )
)
(assert 
 (forall ( ( %.0 Int )( %x0 Int )( %x1 Int )( %x2 Bool )( %x3 Bool )( %x4 Bool ) )
  (=>  
   (?max@@YAXHH@Z7_entry %x0 %x1 %x4 %x2 %x3 %.0 )
   (?max@@YAXHH@Z7_exit %x0 %x1 %x4 %x2 %x3 %.0 )
  )
 )
)
(assert 
 (forall ( ( %.0 Int )( %x0 Int )( %x1 Int )( %x2 Bool )( %x3 Bool )( %x4 Bool ) )
  (=>  
   (?max@@YAXHH@Z7_exit %x0 %x1 %x4 %x2 %x3 %.0 )
   (?max@@YAXHH@Z %x0 %x1 false false )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int ) )
  (?max@@YAXHH@Z %x0 %x1 true true )
 )
)

(declare-fun |main0_entry| () Bool )
(declare-fun |main1_entry| () Bool )
(declare-fun |main1_exit| ( Bool) Bool )
(declare-fun |main_error| () Bool )
(declare-fun |main| ( Int) Bool )

(assert 
 (=>  
  true
  main0_entry
 )
)
(assert 
 (=>  
  main0_entry
  main1_entry
 )
)
(assert 
 (forall ( ( e1 Bool ) )
  (=>  
   (and main1_entry (?max@@YAXHH@Z 1 2 false e1 ) )
   (main1_exit e1 )
  )
 )
)
(assert 
 (=>  
  (main1_exit true )
  main_error
 )
)
(assert 
 (=>  
  (main1_exit false )
  (main 1 )
 )
)
(assert 
 (=>  
  main_error
  false
 )
)

(check-sat)
