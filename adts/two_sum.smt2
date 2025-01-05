(set-logic HORN)

(declare-datatypes ((Lst 1)) (
    (par (T) (
      nil (cons (head T) (tail (Lst T))))
    )
))

(declare-fun sum ((Lst Int) Int) Bool)
(declare-fun twice ((Lst Int) (Lst Int)) Bool)

(assert (forall ((dummy Int)) (=> true (sum nil 0))))
(assert (forall ((dummy Int)) (=> true (twice nil nil))))

(assert (forall ((x Int) (y Int) (l (Lst Int)))
  (=> 
    (sum l x)
    (sum (cons y l) (+ x y))
  )
))

(assert (forall ((x Int) (y Int) (l (Lst Int)) (r (Lst Int)))
  (=> 
    (twice l r) 
    (twice (cons x l) (cons (* 2 x) r))
  )
))

(assert (forall ((x Int) (y Int) (l (Lst Int)) (r (Lst Int)))
  (=> 
    (and (twice l r) (sum l x) (sum r y))
    (= (* 2 x) y)
  )
))


(check-sat)

