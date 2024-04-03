(set-logic HORN)
(set-info :status sat)

(declare-fun |BB0_entry| () Bool )
(declare-fun |BB1_entry| () Bool )
(declare-fun |BB1_exit| () Bool )
(declare-fun |BB2_entry| ( Int Int Bool Int Int) Bool )
(declare-fun |BB2_exit| ( Int Int Bool Int Int) Bool )
(declare-fun |BB3_entry| ( Int Bool Int Int Int) Bool )
(declare-fun |BB4_entry| ( Int Int Bool Int Int Bool) Bool )
(declare-fun |BB3_exit| ( Int Bool Int Int Int) Bool )
(declare-fun |BB4_exit| ( Int Int Bool Int Int Bool) Bool )
(declare-fun |BB6_entry| ( Int Int Bool Int Int Bool Bool) Bool )
(declare-fun |BB_error| () Bool )
(declare-fun |BB6_exit| ( Int Int Bool Int Int Bool Bool) Bool )

(assert 
 (=>  
  true
  BB0_entry
 )
)
(assert 
 (=>  
  BB0_entry
  BB1_entry
 )
)
(assert 
 (=>  
  BB1_entry
  BB1_exit
 )
)
(assert 
 (forall ( ( %.01p Int )( %x1 Int )( %x4 Bool )( %.0p Int )( %x3 Int ) )
  (=>  
   (and BB1_exit(= %.01p 0 )(= %.0p 1 ))
   (BB2_entry %.01p %x1 %x4 %.0p %x3 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x1 Int )( %x4 Bool )( %x4p Bool )( %.0 Int )( %x3 Int ) )
  (=>  
   (and (BB2_entry %.01 %x1 %x4 %.0 %x3 )(= %x4p ( <  %.01 10 )))
   (BB2_exit %.01 %x1 %x4p %.0 %x3 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x4 Bool )( %x1 Int )( %.0 Int )( %x3 Int ) )
  (=>  
   (and (BB2_exit %.01 %x1 %x4 %.0 %x3 )(= %x4 true ))
   (BB3_entry %.01 %x4 %x1 %.0 %x3 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x1 Int )( %x4 Bool )( %.0 Int )( %x3 Int )( %x13 Bool ) )
  (=>  
   (and (BB2_exit %.01 %x1 %x4 %.0 %x3 )(= %x4 false ))
   (BB4_entry %.01 %x1 %x4 %.0 %x3 %x13 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x4 Bool )( %x3 Int )( %x1p Int )( %.0 Int )( %x1 Int )( %x3p Int ) )
  (=>  
   (and (BB3_entry %.01 %x4 %x1 %.0 %x3 )(= %x3p (+ %.0 %.01 ))(= %x1p (+ %.01 1 )))
   (BB3_exit %.01 %x4 %x1p %.0 %x3p )
  )
 )
)
(assert 
 (forall ( ( %.01p Int )( %x1 Int )( %x4 Bool )( %.0p Int )( %x3 Int )( %.01 Int )( %.0 Int ) )
  (=>  
   (and (BB3_exit %.01 %x4 %x1 %.0 %x3 )(= %.01p %x1 )(= %.0p %x3 ))
   (BB2_entry %.01p %x1 %x4 %.0p %x3 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x1 Int )( %x4 Bool )( %.0 Int )( %x3 Int )( %x13 Bool )( %x13p Bool ) )
  (=>  
   (and (BB4_entry %.01 %x1 %x4 %.0 %x3 %x13 )(= %x13p ( <  %.0 %.01 )))
   (BB4_exit %.01 %x1 %x4 %.0 %x3 %x13p )
  )
 )
)
(assert 
 (forall ( ( %x23p Bool )( %.01 Int )( %x1 Int )( %x4 Bool )( %.0 Int )( %x3 Int )( %x13 Bool ) )
  (=>  
   (and (BB4_exit %.01 %x1 %x4 %.0 %x3 %x13 )(= %x23p true )(= %x13 true ))
   (BB6_entry %.01 %x1 %x4 %.0 %x3 %x13 %x23p )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x1 Int )( %x4 Bool )( %.0 Int )( %x3 Int )( %x13 Bool ) )
  (=>  
   (and (BB4_exit %.01 %x1 %x4 %.0 %x3 %x13 )(= %x13 false ))
   BB_error
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x1 Int )( %x4 Bool )( %.0 Int )( %x3 Int )( %x13 Bool )( %x23 Bool ) )
  (=>  
   (BB6_entry %.01 %x1 %x4 %.0 %x3 %x13 %x23 )
   (BB6_exit %.01 %x1 %x4 %.0 %x3 %x13 %x23 )
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
