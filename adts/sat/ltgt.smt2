(set-logic HORN)

(declare-datatypes ((NatLtgt 0)) (((ZLtgt) (SLtgt (pLtgt NatLtgt)))))


(declare-fun |gt| ( NatLtgt NatLtgt ) Bool)
(declare-fun |lt| ( NatLtgt NatLtgt ) Bool)

(assert (forall ( (x NatLtgt) (y NatLtgt) (y2 NatLtgt) )
  (=>
    (and (= x ZLtgt) (= y (SLtgt y2)))
    (lt x y)
  )
))

(assert (forall ( (x NatLtgt) (y NatLtgt) (x2 NatLtgt) (y2 NatLtgt) )
  (=>
    (and (= y (SLtgt y2)) (= x (SLtgt x2)) (lt x2 y2))
    (lt x y)
  )
))

(assert (forall ( (x NatLtgt) (y NatLtgt) (x2 NatLtgt) )
  (=>
    (and (= y ZLtgt) (= x (SLtgt x2)))
    (gt x y)
  )
))

(assert (forall ( (x NatLtgt) (y NatLtgt) (x2 NatLtgt) (y2 NatLtgt) )
  (=>
    (and (= y (SLtgt y2)) (= x (SLtgt x2)) (gt x2 y2))
    (gt x y)
  )
))

(assert (forall ( (x NatLtgt) (y NatLtgt) )
  (=> (and (lt x y) (gt x y)) false)
))

(check-sat)
