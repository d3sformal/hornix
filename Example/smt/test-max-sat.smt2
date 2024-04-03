(set-logic HORN)
(set-info :status sat)

(declare-fun |BB0_entry| ( Int Int) Bool )
(declare-fun |BB1_entry| ( Bool Int Int) Bool )
(declare-fun |BB1_exit| ( Bool Int Int) Bool )
(declare-fun |BB2_entry| ( Int Int Bool) Bool )
(declare-fun |BB3_entry| ( Int Int Bool) Bool )
(declare-fun |BB2_exit| ( Int Int Bool) Bool )
(declare-fun |BB4_entry| ( Bool Int Int Int Bool) Bool )
(declare-fun |BB3_exit| ( Int Int Bool) Bool )
(declare-fun |BB4_exit| ( Bool Int Int Int Bool) Bool )
(declare-fun |BB5_entry| ( Int Int Int Bool Bool Bool) Bool )
(declare-fun |BB_error| () Bool )
(declare-fun |BB5_exit| ( Int Int Int Bool Bool Bool) Bool )
(declare-fun |BB7_entry| ( Bool Bool Int Int Int Bool Bool) Bool )
(declare-fun |BB7_exit| ( Bool Bool Int Int Int Bool Bool) Bool )

(assert 
 (forall ( ( %x2 Int )( %x1 Int ) )
  (=>  
   true
   (BB0_entry %x2 %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %x2 Int ) )
  (=>  
   (BB0_entry %x2 %x1 )
   (BB1_entry %x0 %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x0p Bool )( %x1 Int )( %x2 Int ) )
  (=>  
   (and (BB1_entry %x0 %x1 %x2 )(= %x0p ( >  %x1 %x2 )))
   (BB1_exit %x0p %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %x2 Int )( %x1 Int )( %x0 Bool ) )
  (=>  
   (and (BB1_exit %x0 %x1 %x2 )(= %x0 true ))
   (BB2_entry %x2 %x1 %x0 )
  )
 )
)
(assert 
 (forall ( ( %x2 Int )( %x1 Int )( %x0 Bool ) )
  (=>  
   (and (BB1_exit %x0 %x1 %x2 )(= %x0 false ))
   (BB3_entry %x2 %x1 %x0 )
  )
 )
)
(assert 
 (forall ( ( %x2 Int )( %x1 Int )( %x0 Bool ) )
  (=>  
   (BB2_entry %x2 %x1 %x0 )
   (BB2_exit %x2 %x1 %x0 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %.0p Int )( %x2 Int )( %x3 Bool ) )
  (=>  
   (and (BB2_exit %x2 %x1 %x0 )(= %.0p %x1 ))
   (BB4_entry %x0 %x1 %.0p %x2 %x3 )
  )
 )
)
(assert 
 (forall ( ( %x2 Int )( %x1 Int )( %x0 Bool ) )
  (=>  
   (BB3_entry %x2 %x1 %x0 )
   (BB3_exit %x2 %x1 %x0 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %.0p Int )( %x2 Int )( %x3 Bool ) )
  (=>  
   (and (BB3_exit %x2 %x1 %x0 )(= %.0p %x2 ))
   (BB4_entry %x0 %x1 %.0p %x2 %x3 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x3p Bool )( %x1 Int )( %x2 Int )( %.0 Int )( %x3 Bool ) )
  (=>  
   (and (BB4_entry %x0 %x1 %.0 %x2 %x3 )(= %x3p ( >=  %.0 %x1 )))
   (BB4_exit %x0 %x1 %.0 %x2 %x3p )
  )
 )
)
(assert 
 (forall ( ( %.0 Int )( %x2 Int )( %x1 Int )( %x0 Bool )( %x4 Bool )( %x3 Bool ) )
  (=>  
   (and (BB4_exit %x0 %x1 %x2 %.0 %x3 )(= %x3 true ))
   (BB5_entry %x2 %.0 %x1 %x0 %x4 %x3 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %.0 Int )( %x2 Int )( %x3 Bool ) )
  (=>  
   (and (BB4_exit %x0 %x1 %x2 %.0 %x3 )(= %x3 false ))
   BB_error
  )
 )
)
(assert 
 (forall ( ( %x2 Int )( %.0 Int )( %x1 Int )( %x0 Bool )( %x4 Bool )( %x4p Bool )( %x3 Bool ) )
  (=>  
   (and (BB5_entry %.0 %x2 %x1 %x0 %x4 %x3 )(= %x4p ( >=  %.0 %x2 )))
   (BB5_exit %.0 %x2 %x1 %x0 %x4p %x3 )
  )
 )
)
(assert 
 (forall ( ( %x4 Bool )( %x0 Bool )( %x1 Int )( %x2 Int )( %.0 Int )( %x3 Bool )( %x5p Bool ) )
  (=>  
   (and (BB5_exit %.0 %x2 %x1 %x0 %x4 %x3 )(= %x5p true )(= %x4 true ))
   (BB7_entry %x4 %x0 %x1 %.0 %x2 %x3 %x5p )
  )
 )
)
(assert 
 (forall ( ( %x2 Int )( %.0 Int )( %x1 Int )( %x0 Bool )( %x4 Bool )( %x3 Bool ) )
  (=>  
   (and (BB5_exit %.0 %x2 %x1 %x0 %x4 %x3 )(= %x4 false ))
   BB_error
  )
 )
)
(assert 
 (forall ( ( %x4 Bool )( %x0 Bool )( %x1 Int )( %.0 Int )( %x2 Int )( %x3 Bool )( %x5 Bool ) )
  (=>  
   (BB7_entry %x4 %x0 %x1 %.0 %x2 %x3 %x5 )
   (BB7_exit %x4 %x0 %x1 %x2 %.0 %x3 %x5 )
  )
 )
)
(assert 
 (=>  
  BB_error
  false
 )
)

(check-sat)
