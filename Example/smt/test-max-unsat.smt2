(set-logic HORN)
(set-info :status sat)

(declare-fun |BB0_entry| ( Int Int) Bool )
(declare-fun |BB1_entry| ( Bool Int Int) Bool )
(declare-fun |BB1_exit| ( Bool Int Int) Bool )
(declare-fun |BB2_entry| ( Bool Int Int) Bool )
(declare-fun |BB3_entry| ( Bool Int Int) Bool )
(declare-fun |BB2_exit| ( Bool Int Int) Bool )
(declare-fun |BB4_entry| ( Bool Int Int Int Bool) Bool )
(declare-fun |BB3_exit| ( Bool Int Int) Bool )
(declare-fun |BB4_exit| ( Bool Int Int Int Bool) Bool )
(declare-fun |BB5_entry| ( Bool Int Int Int Bool Bool) Bool )
(declare-fun |BB_error| () Bool )
(declare-fun |BB5_exit| ( Bool Int Int Int Bool Bool) Bool )
(declare-fun |BB7_entry| ( Bool Int Int Int Bool Bool Bool) Bool )
(declare-fun |BB7_exit| ( Bool Int Int Int Bool Bool Bool) Bool )

(assert 
 (forall ( ( %x1 Int )( %x2 Int ) )
  (=>  
   true
   (BB0_entry %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %x2 Int ) )
  (=>  
   (BB0_entry %x1 %x2 )
   (BB1_entry %x0 %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %x2 Int ) )
  (=>  
   (and (BB1_entry %x0 %x1 %x2 )(= %x0 ( >  %x1 %x2 )))
   (BB1_exit %x0 %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %x2 Int ) )
  (=>  
   (and (BB1_exit %x0 %x1 %x2 )(= %x0 true ))
   (BB2_entry %x0 %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %x2 Int ) )
  (=>  
   (and (BB1_exit %x0 %x1 %x2 )(= %x0 false ))
   (BB3_entry %x0 %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %x2 Int ) )
  (=>  
   (BB2_entry %x0 %x1 %x2 )
   (BB2_exit %x0 %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %.0 Int )( %x2 Int )( %x3 Bool ) )
  (=>  
   (and (BB2_exit %x0 %x1 %x2 )(= %.0 %x1 ))
   (BB4_entry %x0 %x1 %x2 %.0 %x3 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %x2 Int ) )
  (=>  
   (BB3_entry %x0 %x1 %x2 )
   (BB3_exit %x0 %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %.0 Int )( %x2 Int )( %x3 Bool ) )
  (=>  
   (and (BB3_exit %x0 %x1 %x2 )(= %.0 %x2 ))
   (BB4_entry %x0 %x1 %x2 %.0 %x3 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %.0 Int )( %x2 Int )( %x3 Bool ) )
  (=>  
   (and (BB4_entry %x0 %x1 %x2 %.0 %x3 )(= %x3 ( <=  %.0 %x1 )))
   (BB4_exit %x0 %x1 %x2 %.0 %x3 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %.0 Int )( %x2 Int )( %x3 Bool )( %x4 Bool ) )
  (=>  
   (and (BB4_exit %x0 %x1 %x2 %.0 %x3 )(= %x3 true ))
   (BB5_entry %x0 %x1 %x2 %.0 %x3 %x4 )
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
 (forall ( ( %x0 Bool )( %x1 Int )( %.0 Int )( %x2 Int )( %x3 Bool )( %x4 Bool ) )
  (=>  
   (and (BB5_entry %x0 %x1 %x2 %.0 %x3 %x4 )(= %x4 ( <=  %.0 %x2 )))
   (BB5_exit %x0 %x1 %x2 %.0 %x3 %x4 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %.0 Int )( %x2 Int )( %x3 Bool )( %x4 Bool )( %x5 Bool ) )
  (=>  
   (and (BB5_exit %x0 %x1 %x2 %.0 %x3 %x4 )(= %x4 true )(= %x5 true ))
   (BB7_entry %x0 %x1 %x2 %.0 %x3 %x4 %x5 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %.0 Int )( %x2 Int )( %x3 Bool )( %x4 Bool ) )
  (=>  
   (and (BB5_exit %x0 %x1 %x2 %.0 %x3 %x4 )(= %x4 false ))
   BB_error
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %.0 Int )( %x2 Int )( %x3 Bool )( %x4 Bool )( %x5 Bool ) )
  (=>  
   (BB7_entry %x0 %x1 %x2 %.0 %x3 %x4 %x5 )
   (BB7_exit %x0 %x1 %x2 %.0 %x3 %x4 %x5 )
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
