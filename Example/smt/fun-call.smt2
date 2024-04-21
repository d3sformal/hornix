(set-logic HORN)
(set-info :status sat)

(declare-fun |BB0_entry| ( Int) Bool )
(declare-fun |BB1_entry| ( Int Int) Bool )
(declare-fun |BB1_exit| ( Int Int) Bool )

(assert 
 (forall ( ( %x1 Int ) )
  (=>  
   true
   (BB0_entry %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x1 Int ) )
  (=>  
   (BB0_entry %x1 )
   (BB1_entry %x0 %x1 )
  )
 )
)
(assert 
 (forall ( ( %x0 Int )( %x0p Int )( %x1 Int ) )
  (=>  
   (and (BB1_entry %x0 %x1 )(= %x0p (+ %x1 1 )))
   (BB1_exit %x0p %x1 )
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
(set-logic HORN)
(set-info :status sat)

(declare-fun |BB0_entry| () Bool )
(declare-fun |BB1_entry| ( Int Int Int) Bool )
(declare-fun |BB1_exit| ( Int Int Int) Bool )

(assert 
 (=>  
  true
  BB0_entry
 )
)
(assert 
 (forall ( ( %x3 Int )( %x5 Int )( %x7 Int ) )
  (=>  
   BB0_entry
   (BB1_entry %x3 %x5 %x7 )
  )
 )
)
(assert 
 (forall ( ( %x3 Int )( %x7 Int )( %x5p Int )( %x5 Int )( %x7p Int ) )
  (=>  
   (and (BB1_entry %x3 %x5 %x7 )(= %x5p (+ %x3 2 ))(= %x7p (+ %x5 3 )))
   (BB1_exit %x3 %x5p %x7p )
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
