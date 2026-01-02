(set-logic HORN)

(declare-datatypes ((LstEos 1)) (
    (par (T) (
      nilEos (consEos (headEos T) (tailEos (LstEos T))))
    )
) )


(declare-fun sum_even_odd ((LstEos Int) Int Int) Bool)
(declare-fun sum_odd_even ((LstEos Int) Int Int) Bool)
(declare-fun gen ((LstEos Int) Int) Bool)

(assert (forall ((dummy Int)) (=> true (sum_even_odd nilEos 0 0))))

(assert (forall ((x Int) (m Int) (n Int) (l (LstEos Int)))
  (=>
  (sum_odd_even l m n)
  (sum_even_odd (consEos x l) (+ x m ) n)
  )
))

(assert (forall ((x Int) (m Int) (n Int) (l (LstEos Int)))
  (=>
  (sum_even_odd l m n)
  (sum_odd_even (consEos x l) m (+ x n))
  )
))


(assert (forall ((dummy Int)) (=> true (gen nilEos 0))))

(assert (forall ((n Int) (x Int) (l (LstEos Int)))
  (=>
    (gen l (- n 1))
    (gen (consEos x (consEos (- x 1) l)) n)
  )
))

(assert (forall ((x Int) (m Int) (n Int) (l (LstEos Int)))
  (=>
  (and
    (sum_even_odd l m n)
    (gen l x)
    (>= x 0)
  )
  (= (- m n) x)
  )
))
(check-sat)
