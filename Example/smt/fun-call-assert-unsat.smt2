(set-logic HORN)
(declare-fun |?foo@@YAHHH@Z0_entry| ( Int Int) Bool )
(declare-fun |?foo@@YAHHH@Z1_entry| ( Int Int Int) Bool )
(declare-fun |?foo@@YAHHH@Z1_exit| ( Int Int Int) Bool )
(declare-fun |?foo@@YAHHH@Z| ( Int Int Int Bool Bool) Bool )

(assert 
 (forall ( ( %x1 Int )( %x2 Int ) )
  (=>  
   true
   (?foo@@YAHHH@Z0_entry %x2 %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Int ) )
  (=>  
   (?foo@@YAHHH@Z0_entry %x2 %x1 )
   (?foo@@YAHHH@Z1_entry %x0 %x2 %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x0p Int )( %x1 Int )( %x2 Int ) )
  (=>  
   (and (?foo@@YAHHH@Z1_entry %x0 %x2 %x1 )(= %x0p (+ %x1 %x2 )))
   (?foo@@YAHHH@Z1_exit %x0p %x2 %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Int ) )
  (=>  
   (?foo@@YAHHH@Z1_exit %x0 %x2 %x1 )
   (?foo@@YAHHH@Z %x1 %x2 %x0 false false )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int )( %x2 Int ) )
  (?foo@@YAHHH@Z %x1 %x2 %x0 true true )
 )
)

(declare-fun |?bar@@YAHHH@Z0_entry| ( Int Int) Bool )
(declare-fun |?bar@@YAHHH@Z1_entry| ( Int Int Int Bool) Bool )
(declare-fun |?bar@@YAHHH@Z1_exit| ( Int Int Int Bool) Bool )
(declare-fun |?bar@@YAHHH@Z2_entry| ( Int Int Int Bool Bool) Bool )
(declare-fun |?bar@@YAHHH@Z| ( Int Int Int Bool Bool) Bool )
(declare-fun |?bar@@YAHHH@Z2_exit| ( Int Int Int Bool Bool) Bool )
(declare-fun |?bar@@YAHHH@Z3_entry| ( Int Int Int Bool Bool Bool) Bool )
(declare-fun |?bar@@YAHHH@Z3_exit| ( Int Int Int Bool Bool Bool) Bool )
(declare-fun |?bar@@YAHHH@Z5_entry| ( Int Bool Int Int Bool Bool Bool) Bool )
(declare-fun |?bar@@YAHHH@Z5_exit| ( Int Bool Int Int Bool Bool Bool) Bool )

(assert 
 (forall ( ( %x4 Int )( %x5 Int ) )
  (=>  
   true
   (?bar@@YAHHH@Z0_entry %x4 %x5 )
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool ) )
  (=>  
   (?bar@@YAHHH@Z0_entry %x4 %x5 )
   (?bar@@YAHHH@Z1_entry %x3 %x4 %x5 %x6 )
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x3p Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x6p Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z1_entry %x3 %x4 %x5 %x6 )(= %x3p (- %x4 %x5 ))(= %x6p ( >=  %x4 0 )))
   (?bar@@YAHHH@Z1_exit %x3p %x4 %x5 %x6p )
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x9 Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z1_exit %x3 %x4 %x5 %x6 )(= %x6 true ))
   (?bar@@YAHHH@Z2_entry %x3 %x4 %x5 %x9 %x6 )
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z1_exit %x3 %x4 %x5 %x6 )(= %x6 false ))
   (?bar@@YAHHH@Z %x4 %x5 %x3 false true )
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x9 Bool )( %x9p Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z2_entry %x3 %x4 %x5 %x9 %x6 )(= %x9p ( >=  %x5 0 )))
   (?bar@@YAHHH@Z2_exit %x3 %x4 %x5 %x9p %x6 )
  )
 )
)
(assert 
 (forall ( ( %x12 Bool )( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x9 Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z2_exit %x3 %x4 %x5 %x9 %x6 )(= %x9 true ))
   (?bar@@YAHHH@Z3_entry %x3 %x4 %x5 %x12 %x6 %x9 )
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x9 Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z2_exit %x3 %x4 %x5 %x9 %x6 )(= %x9 false ))
   (?bar@@YAHHH@Z %x4 %x5 %x3 false true )
  )
 )
)
(assert 
 (forall ( ( %x12 Bool )( %x12p Bool )( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x9 Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z3_entry %x3 %x4 %x5 %x12 %x6 %x9 )(= %x12p ( <  %x4 %x3 )))
   (?bar@@YAHHH@Z3_exit %x3 %x4 %x5 %x12p %x6 %x9 )
  )
 )
)
(assert 
 (forall ( ( %x12 Bool )( %x18p Bool )( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x9 Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z3_exit %x3 %x4 %x5 %x12 %x6 %x9 )(= %x18p true )(?bar@@YAHHH@Z3_exit %x3 %x4 %x5 %x12 %x6 %x9 )(= %x12 true ))
   (?bar@@YAHHH@Z5_entry %x3 %x18p %x4 %x5 %x12 %x6 %x9 )
  )
 )
)
(assert 
 (forall ( ( %x12 Bool )( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x9 Bool ) )
  (=>  
   (and (?bar@@YAHHH@Z3_exit %x3 %x4 %x5 %x12 %x6 %x9 )(= %x12 false ))
   (?bar@@YAHHH@Z %x4 %x5 %x3 false true )
  )
 )
)
(assert 
 (forall ( ( %x12 Bool )( %x18 Bool )( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x9 Bool ) )
  (=>  
   (?bar@@YAHHH@Z5_entry %x3 %x18 %x4 %x5 %x12 %x6 %x9 )
   (?bar@@YAHHH@Z5_exit %x3 %x18 %x4 %x5 %x12 %x6 %x9 )
  )
 )
)
(assert 
 (forall ( ( %x12 Bool )( %x18 Bool )( %x3 Int )( %x4 Int )( %x5 Int )( %x6 Bool )( %x9 Bool ) )
  (=>  
   (?bar@@YAHHH@Z5_exit %x3 %x18 %x4 %x5 %x12 %x6 %x9 )
   (?bar@@YAHHH@Z %x4 %x5 %x3 false false )
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x4 Int )( %x5 Int ) )
  (?bar@@YAHHH@Z %x4 %x5 %x3 true true )
 )
)

(declare-fun |main0_entry| () Bool )
(declare-fun |main1_entry| ( Int Int Bool Int) Bool )
(declare-fun |main1_exit| ( Int Int Bool Int Bool) Bool )
(declare-fun |main2_entry| ( Bool Int Int Int Bool) Bool )
(declare-fun |main_error| () Bool )
(declare-fun |main2_exit| ( Bool Int Int Int Bool) Bool )
(declare-fun |main4_entry| ( Bool Bool Int Int Int Bool) Bool )
(declare-fun |main4_exit| ( Bool Bool Int Int Int Bool) Bool )
(declare-fun |main| ( Int Bool Bool) Bool )

(assert 
 (=>  
  true
  main0_entry
 )
)
(assert 
 (forall ( ( %x21 Int )( %x24 Int )( %x26 Int )( %x27 Bool ) )
  (=>  
   main0_entry
   (main1_entry %x21 %x24 %x27 %x26 )
  )
 )
)
(assert 
 (forall ( ( %x21 Int )( %x21p Int )( %x24 Int )( %x24p Int )( %x26 Int )( %x26p Int )( %x27 Bool )( %x27p Bool )( e1 Bool )( e2 Bool )( e3 Bool ) )
  (=>  
   (and (main1_entry %x21 %x24 %x27 %x26 )(?foo@@YAHHH@Z 10 1 %x21p false e1 )(?bar@@YAHHH@Z %x21p 1 %x24p e1 e2 )(?bar@@YAHHH@Z %x21p %x24p %x26p e2 e3 )(= %x27p ( =  %x26p 1 )))
   (main1_exit %x21p %x24p %x27p %x26p e3 )
  )
 )
)
(assert 
 (forall ( ( %x21 Int )( %x24 Int )( %x26 Int )( %x27 Bool )( %x31 Bool ) )
  (=>  
   (and (main1_exit %x21 %x24 %x27 %x26 false )(= %x27 true ))
   (main2_entry %x31 %x21 %x24 %x26 %x27 )
  )
 )
)
(assert 
 (forall ( ( %x21 Int )( %x24 Int )( %x26 Int )( %x27 Bool )( e3 Bool ) )
  (=>  
   (and (main1_exit %x21 %x24 %x27 %x26 e3 )(= %x27 false ))
   main_error
  )
 )
)
(assert 
 (forall ( ( %x21 Int )( %x24 Int )( %x26 Int )( %x27 Bool ) )
  (=>  
   (main1_exit %x21 %x24 %x27 %x26 true )
   main_error
  )
 )
)
(assert 
 (forall ( ( %x21 Int )( %x24 Int )( %x26 Int )( %x27 Bool )( %x31 Bool )( %x31p Bool ) )
  (=>  
   (and (main2_entry %x31 %x21 %x24 %x26 %x27 )(= %x31p ( =  %x24 10 )))
   (main2_exit %x31p %x21 %x24 %x26 %x27 )
  )
 )
)
(assert 
 (forall ( ( %x21 Int )( %x24 Int )( %x26 Int )( %x27 Bool )( %x31 Bool )( %x41p Bool ) )
  (=>  
   (and (main2_exit %x31 %x21 %x24 %x26 %x27 )(= %x41p true )(main2_exit %x31 %x21 %x24 %x26 %x27 )(= %x31 true ))
   (main4_entry %x41p %x31 %x21 %x24 %x26 %x27 )
  )
 )
)
(assert 
 (forall ( ( %x21 Int )( %x24 Int )( %x26 Int )( %x27 Bool )( %x31 Bool ) )
  (=>  
   (and (main2_exit %x31 %x21 %x24 %x26 %x27 )(= %x31 false ))
   main_error
  )
 )
)
(assert 
 (forall ( ( %x21 Int )( %x24 Int )( %x26 Int )( %x27 Bool )( %x31 Bool )( %x41 Bool ) )
  (=>  
   (main4_entry %x41 %x31 %x21 %x24 %x26 %x27 )
   (main4_exit %x41 %x31 %x21 %x24 %x26 %x27 )
  )
 )
)
(assert 
 (forall ( ( %x21 Int )( %x24 Int )( %x26 Int )( %x27 Bool )( %x31 Bool )( %x41 Bool ) )
  (=>  
   (main4_exit %x41 %x31 %x21 %x24 %x26 %x27 )
   (main 0 false false )
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
