(set-logic HORN)

(declare-datatypes ((NatId 0)) (((ZId) (SId (pId NatId)))))

(declare-fun |inc| ( NatId NatId ) Bool)
(declare-fun |dec| ( NatId NatId ) Bool)

(assert (forall ( (x NatId) (y NatId) )
  (=> (and (= x ZId) (= y ZId))
  (inc x y)
  )
))

(assert (forall ( (x NatId) (y NatId) (x2 NatId) (y2 NatId) )
  (=> (and (= x (SId x2)) (= y (SId y2)) (inc x2 y2))
  (inc x y)
  )
))

(assert (forall ( (x NatId) (y NatId) )
  (=> (and (= x (SId ZId)) (= y ZId))
  (dec x y)
  )
))

(assert (forall ( (x NatId) (y NatId) (x2 NatId) (y2 NatId) )
  (=> (and (= x (SId x2)) (= y (SId y2)) (dec x2 y2))
  (dec x y)
  )
))

(assert (forall ( (x NatId) (y NatId) )
  (=> (and (inc x y) (dec x y))
   false
  )
))
(check-sat)
