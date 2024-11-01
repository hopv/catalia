(set-logic HORN)
(declare-datatypes ((treeOfInt 0)) (
   (
      (nodetreeOfInt (lefttreeOfInt treeOfInt) (righttreeOfInt treeOfInt)) 
      (leaftreeOfInt))
   )
)

(declare-fun evenleft (treeOfInt) Bool)

(assert (forall ((x treeOfInt)) (=>
  (= x leaftreeOfInt)
  (evenleft x))))

(assert (forall ((x treeOfInt) (x2 treeOfInt) (y treeOfInt) (z treeOfInt) ) (=>
  (and 
    (= x (nodetreeOfInt (nodetreeOfInt x2 y) z))
    (evenleft x2)
  )
  (evenleft x))
))

(assert (forall ((x treeOfInt) (y treeOfInt) ) (=>
  (and 
    (evenleft x)
    (evenleft (nodetreeOfInt x y))
  )
  false)
))

(check-sat)
