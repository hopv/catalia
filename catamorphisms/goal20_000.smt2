;; cons(a,l) a|->(w) and l |->(x, y, z)

;; v curr elem
;; w is it cons?
;; x are previous elements sorted?
;; y list lenght
(
 ( "listOfInt"
   ( "conslistOfInt"
	 ( (a v w x y)
	   a
	   1
	   (ite (or (= w 0) (and (= w 1) (<= a v) (= x 1))) 1 0)
	   (+ 1 y)
	   )
	 )
   ( "nillistOfInt"
	 ( ()
	   0
	   0
	   1
	   0
	   )
	 )
   )
 )
