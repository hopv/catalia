;; cons(a, nil) |-> forall x,y,z:int. (1, (ite (= y 0) x (ite (>= x z) x z)))
;; a |-> (w, x)     l |-> (y,z)

(
 ( "LstInt"
   ( "cons"
	 ( (x y z)
	   1
	   (ite (= y 0) x (ite (>= x z) x z))
	   )
	 )
   ( "nil"
	 ( ()
	   0
	   0
	   )
	 )
   )
 )
