(set-logic HORN)
(set-info :status sat)
(declare-fun |main0_entry| () Bool )
(declare-fun |main1_entry| ( Int Int Int Bool) Bool )
(declare-fun |main1_exit| ( Int Int Int Bool) Bool )
(declare-fun |main3_entry| ( Int Int Bool Bool Int Bool) Bool )
(declare-fun |main_error| () Bool )
(declare-fun |main3_exit| ( Int Int Bool Bool Int Bool) Bool )
(declare-fun |main5_entry| ( Int Int Bool Bool Int Bool Bool) Bool )
(declare-fun |main5_exit| ( Int Int Bool Bool Int Bool Bool) Bool )
(declare-fun |main| ( Int) Bool )

(assert 
 (=>  
  true
  main0_entry
 )
)
(assert 
 (forall ( ( %x0 Int )( %x2 Int )( %x4 Int )( %x6 Bool ) )
  (=>  
   main0_entry
   (main1_entry %x0 %x2 %x4 %x6 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x0p Int )( %x2 Int )( %x2p Int )( %x4 Int )( %x4p Int )( %x6 Bool )( %x6p Bool ) )
  (=>  
   (and (main1_entry %x0 %x2 %x4 %x6 )(?inc@@YAHH@Z %x0p 0 )(= %x2p (+ %x0p 2 ))(= %x4p (+ %x2p 3 ))(= %x6p ( =  %x0p 1 )))
   (main1_exit %x0p %x2p %x4p %x6p )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x2 Int )( %x20p Bool )( %x23 Bool )( %x4 Int )( %x6 Bool ) )
  (=>  
   (and (main1_exit %x0 %x2 %x4 %x6 )(= %x20p true )(= %x6 true ))
   (main3_entry %x0 %x2 %x20p %x23 %x4 %x6 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x2 Int )( %x4 Int )( %x6 Bool ) )
  (=>  
   (and (main1_exit %x0 %x2 %x4 %x6 )(= %x6 false ))
   main_error
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x2 Int )( %x20 Bool )( %x23 Bool )( %x23p Bool )( %x4 Int )( %x6 Bool ) )
  (=>  
   (and (main3_entry %x0 %x2 %x20 %x23 %x4 %x6 )(= %x23p ( =  %x4 7 )))
   (main3_exit %x0 %x2 %x20 %x23p %x4 %x6 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x2 Int )( %x20 Bool )( %x23 Bool )( %x4 Int )( %x46p Bool )( %x6 Bool ) )
  (=>  
   (and (main3_exit %x0 %x2 %x20 %x23 %x4 %x6 )(= %x46p true )(= %x23 true ))
   (main5_entry %x0 %x2 %x20 %x23 %x4 %x46p %x6 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x2 Int )( %x20 Bool )( %x23 Bool )( %x4 Int )( %x6 Bool ) )
  (=>  
   (and (main3_exit %x0 %x2 %x20 %x23 %x4 %x6 )(= %x23 false ))
   main_error
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x2 Int )( %x20 Bool )( %x23 Bool )( %x4 Int )( %x46 Bool )( %x6 Bool ) )
  (=>  
   (main5_entry %x0 %x2 %x20 %x23 %x4 %x46 %x6 )
   (main5_exit %x0 %x2 %x20 %x23 %x4 %x46 %x6 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x2 Int )( %x20 Bool )( %x23 Bool )( %x4 Int )( %x46 Bool )( %x6 Bool ) )
  (=>  
   (main5_exit %x0 %x2 %x20 %x23 %x4 %x46 %x6 )
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
