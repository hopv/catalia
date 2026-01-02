(set-logic HORN)

(declare-datatypes ((LstTae 1)) (
    (par (T) (
      nilTae (consTae (headTae T) (tailTae (LstTae T))))
    )
))

(declare-fun check ((LstTae Int) (LstTae Int)) Bool)
(declare-fun app ((LstTae Int) (LstTae Int) (LstTae Int)) Bool)

(assert (forall ((l (LstTae Int)) (r (LstTae Int))(l2 (LstTae Int)) (r2 (LstTae Int)) (x Int) (y Int))
    (=> (and (= l (consTae x l2)) (= r (consTae y r2)) (check l2 r2))
      (check l r))))
(assert (forall ((dummy Int)) (check nilTae nilTae)))

(assert (forall ((l (LstTae Int))) (=> true (app nilTae l l))))
(assert (forall ((x Int) (l (LstTae Int)) (r (LstTae Int)) (l2 (LstTae Int)) )
  (=>
    (app l r l2)
    (app (consTae x l) r (consTae x l2))
  )
))

(assert (forall ((x Int) (y Int) (l (LstTae Int)) (r (LstTae Int)) (l2 (LstTae Int)) )
  (=>
    (and (= l (consTae x r)) (check l l2) (app l l l2))
    false
  )
))


(check-sat)
(get-model)
