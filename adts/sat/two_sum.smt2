(set-logic HORN)

(declare-datatypes ((LstTs 1)) (
    (par (T) (
      nilTs (consTs (headTs T) (tailTs (LstTs T))))
    )
))

(declare-fun sum ((LstTs Int) Int) Bool)
(declare-fun twice ((LstTs Int) (LstTs Int)) Bool)

(assert (forall ((dummy Int)) (=> true (sum nilTs 0))))
(assert (forall ((dummy Int)) (=> true (twice nilTs nilTs))))

(assert (forall ((x Int) (y Int) (l (LstTs Int)))
  (=>
    (sum l x)
    (sum (consTs y l) (+ x y))
  )
))

(assert (forall ((x Int) (y Int) (l (LstTs Int)) (r (LstTs Int)))
  (=>
    (twice l r)
    (twice (consTs x l) (consTs (* 2 x) r))
  )
))

(assert (forall ((x Int) (y Int) (l (LstTs Int)) (r (LstTs Int)))
  (=>
    (and (twice l r) (sum l x) (sum r y))
    (= (* 2 x) y)
  )
))


(check-sat)
