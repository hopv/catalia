(set-logic HORN)

(declare-datatypes ((Nat 0)) (((Z) (S (p Nat)))))

(declare-fun |inc| ( Nat Nat ) Bool)
(declare-fun |dec| ( Nat Nat ) Bool)

(assert (forall ( (x Nat) (y Nat) )
  (=> (and (= x Z) (= y Z)) 
  (inc x y)
  )
))

(assert (forall ( (x Nat) (y Nat) (x2 Nat) (y2 Nat) )
  (=> (and (= x (S x2)) (= y (S y2)) (inc x2 y2))  
  (inc x y)
  )
))

(assert (forall ( (x Nat) (y Nat) )
  (=> (and (= x (S Z)) (= y Z)) 
  (dec x y)
  )
))

(assert (forall ( (x Nat) (y Nat) (x2 Nat) (y2 Nat) )
  (=> (and (= x (S x2)) (= y (S y2)) (dec x2 y2))  
  (dec x y)
  )
))

(assert (forall ( (x Nat) (y Nat) )
  (=> (and (inc x y) (dec x y)) 
   false
  )
))
(check-sat)
