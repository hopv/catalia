(set-logic HORN)

(declare-datatypes ((Lst 1)) (
    (par (T) (
      nil (cons (head T) (tail (Lst T))))
    )
))

(declare-fun check ((Lst Int) (Lst Int)) Bool)
(declare-fun app ((Lst Int) (Lst Int) (Lst Int)) Bool)

(assert (forall ((l (Lst Int)) (r (Lst Int))(l2 (Lst Int)) (r2 (Lst Int)) (x Int) (y Int))
    (=> (and (= l (cons x l2)) (= r (cons y r2)) (check l2 r2))
      (check l r))))
(assert (forall ((dummy Int)) (check nil nil)))

(assert (forall ((l (Lst Int))) (=> true (app nil l l))))
(assert (forall ((x Int) (l (Lst Int)) (r (Lst Int)) (l2 (Lst Int)) )
  (=> 
    (app l r l2)
    (app (cons x l) r (cons x l2))
  )
))

(assert (forall ((x Int) (y Int) (l (Lst Int)) (r (Lst Int)) (l2 (Lst Int)) )
  (=> 
    (and (= l (cons x r)) (check l l2) (app l l l2))
    false
  )
))


(check-sat)
(get-model)

