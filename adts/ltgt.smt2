(set-logic HORN)

(declare-datatypes ((Nat 0)) (((Z) (S (p Nat)))))


(declare-fun |gt| ( Nat Nat ) Bool)
(declare-fun |lt| ( Nat Nat ) Bool)

(assert (forall ( (x Nat) (y Nat) (y2 Nat) )
  (=> 
    (and (= x Z) (= y (S y2)))
    (lt x y)
  )
))

(assert (forall ( (x Nat) (y Nat) (x2 Nat) (y2 Nat) )
  (=> 
    (and (= y (S y2)) (= x (S x2)) (lt x2 y2))
    (lt x y)
  )
))

(assert (forall ( (x Nat) (y Nat) (x2 Nat) )
  (=> 
    (and (= y Z) (= x (S x2)))
    (gt x y)
  )
))

(assert (forall ( (x Nat) (y Nat) (x2 Nat) (y2 Nat) )
  (=> 
    (and (= y (S y2)) (= x (S x2)) (gt x2 y2))
    (gt x y)
  )
))

(assert (forall ( (x Nat) (y Nat) )
  (=> (and (lt x y) (gt x y)) false)
))

(check-sat)
