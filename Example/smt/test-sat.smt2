(set-logic HORN)
(set-info :status sat)

(declare-fun |BB0_entry| () Bool )
(declare-fun |BB1_entry| () Bool )
(declare-fun |BB1_exit| () Bool )
(declare-fun |BB2_entry| ( Int Int Int Int Bool) Bool )
(declare-fun |BB2_exit| ( Int Int Int Int Bool) Bool )
(declare-fun |BB3_entry| ( Int Int Int Int Bool) Bool )
(declare-fun |BB4_entry| ( Int Int Int Int Bool Bool) Bool )
(declare-fun |BB3_exit| ( Int Int Int Int Bool) Bool )
(declare-fun |BB4_exit| ( Int Int Int Int Bool Bool) Bool )
(declare-fun |BB6_entry| ( Int Int Int Int Bool Bool Bool) Bool )
(declare-fun |BB_error| () Bool )
(declare-fun |BB6_exit| ( Int Int Int Int Bool Bool Bool) Bool )

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
 (forall ( ( %.01 Int )( %x1 Int )( %.0 Int )( %x3 Int )( %x4 Bool ) )
  (=>  
   (and BB1_exit(= %.01 0 )(= %.0 1 ))
   (BB2_entry %.01 %x1 %.0 %x3 %x4 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x1 Int )( %.0 Int )( %x3 Int )( %x4 Bool ) )
  (=>  
   (and (BB2_entry %.01 %x1 %.0 %x3 %x4 )(= %x4 ( <  %.01 10 )))
   (BB2_exit %.01 %x1 %.0 %x3 %x4 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x1 Int )( %.0 Int )( %x3 Int )( %x4 Bool ) )
  (=>  
   (and (BB2_exit %.01 %x1 %.0 %x3 %x4 )(= %x4 true ))
   (BB3_entry %.01 %x1 %.0 %x3 %x4 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x1 Int )( %.0 Int )( %x3 Int )( %x4 Bool )( %x13 Bool ) )
  (=>  
   (and (BB2_exit %.01 %x1 %.0 %x3 %x4 )(= %x4 false ))
   (BB4_entry %.01 %x1 %.0 %x3 %x4 %x13 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x1 Int )( %.0 Int )( %x3 Int )( %x4 Bool ) )
  (=>  
   (and (BB3_entry %.01 %x1 %.0 %x3 %x4 )(= %x3 (+ %.0 %.01 ))(= %x1 (+ %.01 1 )))
   (BB3_exit %.01 %x1 %.0 %x3 %x4 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x1 Int )( %.0 Int )( %x3 Int )( %x4 Bool ) )
  (=>  
   (and (BB3_exit %.01 %x1 %.0 %x3 %x4 )(= %.01 %x1 )(= %.0 %x3 ))
   (BB2_entry %.01 %x1 %.0 %x3 %x4 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x1 Int )( %.0 Int )( %x3 Int )( %x4 Bool )( %x13 Bool ) )
  (=>  
   (and (BB4_entry %.01 %x1 %.0 %x3 %x4 %x13 )(= %x13 (not ( >  %.0 %.01 ))))
   (BB4_exit %.01 %x1 %.0 %x3 %x4 %x13 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x1 Int )( %.0 Int )( %x3 Int )( %x4 Bool )( %x13 Bool )( %x23 Bool ) )
  (=>  
   (and (BB4_exit %.01 %x1 %.0 %x3 %x4 %x13 )(= %x13 true )(= %x23 true ))
   (BB6_entry %.01 %x1 %.0 %x3 %x4 %x13 %x23 )
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x1 Int )( %.0 Int )( %x3 Int )( %x4 Bool )( %x13 Bool ) )
  (=>  
   (and (BB4_exit %.01 %x1 %.0 %x3 %x4 %x13 )(= %x13 false ))
   BB_error
  )
 )
)
(assert 
 (forall ( ( %.01 Int )( %x1 Int )( %.0 Int )( %x3 Int )( %x4 Bool )( %x13 Bool )( %x23 Bool ) )
  (=>  
   (BB6_entry %.01 %x1 %.0 %x3 %x4 %x13 %x23 )
   (BB6_exit %.01 %x1 %.0 %x3 %x4 %x13 %x23 )
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
(get-model)