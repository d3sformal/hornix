(set-logic HORN)
(set-info :status sat)
(declare-fun |?inc@@YAHH@Z0_entry| ( Int) Bool )
(declare-fun |?inc@@YAHH@Z1_entry| ( Int Int) Bool )
(declare-fun |?inc@@YAHH@Z1_exit| ( Int Int) Bool )
(declare-fun |?inc@@YAHH@Z| ( Int Int) Bool )

(assert 
 (forall ( ( %x1 Int ) )
  (=>  
   true
   (?inc@@YAHH@Z0_entry %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int ) )
  (=>  
   (?inc@@YAHH@Z0_entry %x1 )
   (?inc@@YAHH@Z1_entry %x0 %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x0p Int )( %x1 Int ) )
  (=>  
   (and (?inc@@YAHH@Z1_entry %x0 %x1 )(= %x0p (+ %x1 1 )))
   (?inc@@YAHH@Z1_exit %x0p %x1 )
  )
 )
)
(assert 
 (forall ( ( %x1 Int )( %x0 Int ) )
  (=>  
   (?inc@@YAHH@Z1_exit %x0 %x1 )
   (?inc@@YAHH@Z %x1 %x0 )
  )
 )
)

(declare-fun |main0_entry| () Bool )
(declare-fun |main1_entry| ( Int Bool) Bool )
(declare-fun |main1_exit| ( Int Bool) Bool )
(declare-fun |main3_entry| ( Int Bool Bool) Bool )
(declare-fun |main_error| () Bool )
(declare-fun |main3_exit| ( Int Bool Bool) Bool )
(declare-fun |main| ( Int) Bool )

(assert 
 (=>  
  true
  main0_entry
 )
)
(assert 
 (forall ( ( %x3 Int )( %x5 Bool ) )
  (=>  
   main0_entry
   (main1_entry %x3 %x5 )
  )
 )
)
(assert 
 (forall ( ( %x3p Int )( %x5p Bool )( %x3 Int )( %x5 Bool ) )
  (=>  
   (and (main1_entry %x3 %x5 )(?inc@@YAHH@Z 0 %x3p )(= %x5p ( =  %x3p 1 )))
   (main1_exit %x3p %x5p )
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x13p Bool )( %x5 Bool ) )
  (=>  
   (and (main1_exit %x3 %x5 )(= %x13p true )(= %x5 true ))
   (main3_entry %x3 %x13p %x5 )
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x5 Bool ) )
  (=>  
   (and (main1_exit %x3 %x5 )(= %x5 false ))
   main_error
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x13 Bool )( %x5 Bool ) )
  (=>  
   (main3_entry %x3 %x13 %x5 )
   (main3_exit %x3 %x13 %x5 )
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x13 Bool )( %x5 Bool ) )
  (=>  
   (main3_exit %x3 %x13 %x5 )
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
