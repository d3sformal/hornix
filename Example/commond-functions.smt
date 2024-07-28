(declare-fun |zextBoolToInt0| ( Bool) Bool )
(declare-fun |zextBoolToInt1| ( Bool Bool) Bool )
(declare-fun |zextBoolToInt| ( Bool Int) Bool )
(declare-fun |truncIntToBool0| ( Int) Bool )
(declare-fun |truncIntToBool| ( Int Bool) Bool )

(assert 
 (forall ( ( z1 Bool ) )
  (=>  
   true
   (zextBoolToInt0 z1 )
  )
 )
)
(assert 
 (forall ( ( z1 Bool )( z3 Bool ) )
  (=>  
   (and (zextBoolToInt0 z1 ) (= z3 (= z1 true )) )
   (zextBoolToInt1 z1 z3 )
  )
 )
)
(assert 
 (forall ( ( z1 Bool )( z3 Bool ) )
  (=>  
   (and (zextBoolToInt1 z1 z3 ) (= z3 true ) )
   (zextBoolToInt z1 1 )
  )
 )
)
(assert 
 (forall ( ( z1 Bool )( z3 Bool ) )
  (=>  
   (and (zextBoolToInt1 z1 z3 ) (= z3 false ) )
   (zextBoolToInt z1 0 )
  )
 )
)
(assert 
 (forall ( ( z1 Int ) )
  (=>  
   true
   (truncIntToBool0 z1 )
  )
 )
)
(assert 
 (forall ( ( z1 Int )( z3 Bool ) )
  (=>  
   (and (truncIntToBool0 z1 ) (= z3 (> z1 0 )) )
   (truncIntToBool z1 z3 )
  )
 )
)