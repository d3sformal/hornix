(set-logic HORN)
(set-info :status sat)
(declare-fun |?max@@YAXHH@Z0_entry| ( Int Int) Bool )
(declare-fun |?max@@YAXHH@Z1_entry| ( Bool Int Int) Bool )
(declare-fun |?max@@YAXHH@Z1_exit| ( Bool Int Int) Bool )
(declare-fun |?max@@YAXHH@Z2_entry| ( Bool Int Int) Bool )
(declare-fun |?max@@YAXHH@Z3_entry| ( Bool Int Int) Bool )
(declare-fun |?max@@YAXHH@Z2_exit| ( Bool Int Int) Bool )
(declare-fun |?max@@YAXHH@Z4_entry| ( Bool Int Int Int Bool) Bool )
(declare-fun |?max@@YAXHH@Z3_exit| ( Bool Int Int) Bool )
(declare-fun |?max@@YAXHH@Z4_exit| ( Bool Int Int Int Bool) Bool )
(declare-fun |?max@@YAXHH@Z5_entry| ( Bool Int Int Int Bool Bool) Bool )
(declare-fun |?max@@YAXHH@Z_error| () Bool )
(declare-fun |?max@@YAXHH@Z5_exit| ( Bool Int Int Int Bool Bool) Bool )
(declare-fun |?max@@YAXHH@Z7_entry| ( Bool Int Int Int Bool Bool Bool) Bool )
(declare-fun |?max@@YAXHH@Z7_exit| ( Bool Int Int Int Bool Bool Bool) Bool )
(declare-fun |?max@@YAXHH@Z| ( Int Int) Bool )

(assert 
 (forall ( ( %x2 Int )( %x1 Int ) )
  (=>  
   true
   (?max@@YAXHH@Z0_entry %x2 %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %x2 Int ) )
  (=>  
   (?max@@YAXHH@Z0_entry %x2 %x1 )
   (?max@@YAXHH@Z1_entry %x0 %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x0p Bool )( %x1 Int )( %x2 Int ) )
  (=>  
   (and (?max@@YAXHH@Z1_entry %x0 %x1 %x2 )(= %x0p ( >  %x1 %x2 )))
   (?max@@YAXHH@Z1_exit %x0p %x1 %x2 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x2 Int )( %x1 Int ) )
  (=>  
   (and (?max@@YAXHH@Z1_exit %x0 %x1 %x2 )(= %x0 true ))
   (?max@@YAXHH@Z2_entry %x0 %x2 %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x2 Int )( %x1 Int ) )
  (=>  
   (and (?max@@YAXHH@Z1_exit %x0 %x1 %x2 )(= %x0 false ))
   (?max@@YAXHH@Z3_entry %x0 %x2 %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x2 Int )( %x1 Int ) )
  (=>  
   (?max@@YAXHH@Z2_entry %x0 %x2 %x1 )
   (?max@@YAXHH@Z2_exit %x0 %x2 %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %x2 Int )( %.0p Int )( %x3 Bool ) )
  (=>  
   (and (?max@@YAXHH@Z2_exit %x0 %x2 %x1 )(= %.0p %x1 ))
   (?max@@YAXHH@Z4_entry %x0 %x1 %x2 %.0p %x3 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x2 Int )( %x1 Int ) )
  (=>  
   (?max@@YAXHH@Z3_entry %x0 %x2 %x1 )
   (?max@@YAXHH@Z3_exit %x0 %x2 %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %x2 Int )( %.0p Int )( %x3 Bool ) )
  (=>  
   (and (?max@@YAXHH@Z3_exit %x0 %x2 %x1 )(= %.0p %x2 ))
   (?max@@YAXHH@Z4_entry %x0 %x1 %x2 %.0p %x3 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x3p Bool )( %x1 Int )( %.0 Int )( %x2 Int )( %x3 Bool ) )
  (=>  
   (and (?max@@YAXHH@Z4_entry %x0 %x1 %.0 %x2 %x3 )(= %x3p ( <=  %.0 %x1 )))
   (?max@@YAXHH@Z4_exit %x0 %x1 %x2 %.0 %x3p )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x2 Int )( %.0 Int )( %x1 Int )( %x3 Bool )( %x4 Bool ) )
  (=>  
   (and (?max@@YAXHH@Z4_exit %x0 %x1 %x2 %.0 %x3 )(= %x3 true ))
   (?max@@YAXHH@Z5_entry %x0 %.0 %x2 %x1 %x3 %x4 )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %x2 Int )( %.0 Int )( %x3 Bool ) )
  (=>  
   (and (?max@@YAXHH@Z4_exit %x0 %x1 %x2 %.0 %x3 )(= %x3 false ))
   ?max@@YAXHH@Z_error
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %.0 Int )( %x2 Int )( %x1 Int )( %x3 Bool )( %x4 Bool )( %x4p Bool ) )
  (=>  
   (and (?max@@YAXHH@Z5_entry %x0 %.0 %x2 %x1 %x3 %x4 )(= %x4p ( <=  %.0 %x2 )))
   (?max@@YAXHH@Z5_exit %x0 %x2 %.0 %x1 %x3 %x4p )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %.0 Int )( %x2 Int )( %x3 Bool )( %x4 Bool )( %x5p Bool ) )
  (=>  
   (and (?max@@YAXHH@Z5_exit %x0 %x2 %.0 %x1 %x3 %x4 )(= %x5p true )(= %x4 true ))
   (?max@@YAXHH@Z7_entry %x0 %x1 %x2 %.0 %x3 %x4 %x5p )
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %.0 Int )( %x2 Int )( %x1 Int )( %x3 Bool )( %x4 Bool ) )
  (=>  
   (and (?max@@YAXHH@Z5_exit %x0 %.0 %x2 %x1 %x3 %x4 )(= %x4 false ))
   ?max@@YAXHH@Z_error
  )
 )
)
(assert 
 (forall ( ( %x0 Bool )( %x1 Int )( %x2 Int )( %.0 Int )( %x3 Bool )( %x4 Bool )( %x5 Bool ) )
  (=>  
   (?max@@YAXHH@Z7_entry %x0 %x1 %x2 %.0 %x3 %x4 %x5 )
   (?max@@YAXHH@Z7_exit %x0 %x1 %.0 %x2 %x3 %x4 %x5 )
  )
 )
)
(assert 
 (forall ( ( %x1 Int )( %.0 Int )( %x2 Int )( %x0 Bool )( %x3 Bool )( %x4 Bool )( %x5 Bool ) )
  (=>  
   (?max@@YAXHH@Z7_exit %x0 %x1 %.0 %x2 %x3 %x4 %x5 )
   (?max@@YAXHH@Z %x1 %x2 )
  )
 )
)
(assert 
 (=>  
  ?max@@YAXHH@Z_error
  false
 )
)

(check-sat)
